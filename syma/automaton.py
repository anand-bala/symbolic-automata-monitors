import logging
import sys
from dataclasses import dataclass
from typing import Iterable, Optional, Tuple, Union

import networkx as nx

from syma.alphabet import Interval
from syma.constraint.constraint import Constraint
from syma.constraint.node.node import (BoolConst, BoolVar, IntVar, Node, Or,
                                       RealVar)

VarNode = Union[BoolVar, IntVar, RealVar]


@dataclass
class Location(object):
    id: int
    initial: bool = False
    accepting: bool = False
    rejecting: bool = False


@dataclass
class Transition(object):
    src: int
    dst: int
    guard: Constraint


class SymbolicAutomaton(object):
    """A Symbolic Automaton

    Symbolic automaton SA is a tuple (A, Q, q_0, F, T), where:
    * A - is the alphabet (an effective Boolean algebra)
    * Q - is a finite set of locations
    * q_0 - is the initial location
    * F - is the set of final locations
    * T - is a finite set of transitions of the form (q, psi, q'), where psi is a Boolean constraint defined in A
    """

    def __init__(self):
        from syma.alphabet import Alphabet

        self._alphabet = Alphabet()  # alphabet (effective Boolean algebra)
        self._graph = nx.DiGraph()  # automaton structure
        self._initial_location: Optional[int] = None
        self.logger = logging.getLogger(__name__)

        self._is_complete = False

    def add_var(self, name: VarNode, domain: Optional[Union[Interval, Tuple]] = None):
        if domain is not None and isinstance(domain, tuple):
            domain = Interval(*domain)
        self._alphabet.add_var(name, domain)

    def declare_bool(self, name: str) -> BoolVar:
        var = BoolVar(name)
        self.add_var(var)
        return var

    def declare_int(self, name: str, domain: Optional[Tuple] = None) -> IntVar:
        var = IntVar(name)
        self.add_var(var, domain)
        return var

    def declare_real(self, name: str, domain: Optional[Tuple] = None) -> RealVar:
        var = RealVar(name)
        self.add_var(var, domain)
        return var

    def add_location(self, location: int, initial=False, accepting=False):
        if location in self._graph.nodes:
            raise ValueError(f"Location {location} already exists in automaton")
        if initial:
            if self._initial_location is not None:
                raise ValueError(
                    f"Initial Location already exists: {self.initial}. Cannot redefine."
                )
            self._initial_location = location
        self._graph.add_node(location, initial=initial, accepting=accepting)

    def add_transition(
        self,
        src: int,
        dst: int,
        guard: Union[Constraint, Node, bool],
        *,
        minimize: bool = True,
    ):
        if (src, dst) in self._graph.edges:
            raise ValueError(
                f"Transition from {src} to {dst} already exists. Did you want to update the guard?"
            )
        if isinstance(guard, Node):
            guard = Constraint(self._alphabet, guard)
        elif isinstance(guard, bool):
            guard = Constraint(self._alphabet, BoolConst(guard))

        if guard.is_trivially_false():
            return
        if minimize:
            guard = guard.minimize()
        self._graph.add_edge(src, dst, guard=guard)

        self._is_complete = False

    def location(self, node: int) -> Location:
        data = self._graph.nodes[node]
        return Location(id=node, initial=data["initial"], accepting=data["accepting"])

    def __getitem__(self, node: int) -> Location:
        return self.location(node)

    def transition(self, src: int, dst: int) -> Transition:
        data = self._graph.edges[src, dst]
        return Transition(src=src, dst=dst, guard=data["guard"])

    def has_transition(self, src: int, dst: int) -> bool:
        return (src, dst) in self._graph.edges

    def get_guard(self, src: int, dst: int) -> Constraint:
        return self.transition(src, dst).guard

    @property
    def num_locations(self) -> int:
        return len(self._graph)

    def __len__(self) -> int:
        return len(self._graph)

    @property
    def locations(self) -> Iterable[int]:
        return self._graph.nodes

    @property
    def transitions(self) -> Iterable[Tuple[int, int]]:
        return self._graph.edges

    @property
    def initial(self) -> int:
        if self._initial_location is None:
            raise ValueError("No initial location assigned in the automaton")
        return self._initial_location

    def in_edges(self, q: int) -> Iterable[Tuple[int, int]]:
        for q_ in self._graph.predecessors(q):
            yield q_, q

    def out_edges(self, q: int) -> Iterable[Tuple[int, int]]:
        for q_ in self._graph.successors(q):
            yield q, q_

    def _is_state_complete(self, q: int) -> bool:
        """Check if the given state is complete"""
        out_guards = [self.get_guard(q, q_).formula for q_ in self._graph.successors(q)]
        if len(out_guards) == 0:
            self.logger.error(f"State {q} has 2 out going edges.")
            sys.exit(1)
        elif len(out_guards) == 1:
            disjunction = Constraint(self._alphabet, out_guards[0])
        else:
            disjunction = Constraint(formula=Or(*out_guards), alphabet=self._alphabet)
        return disjunction.is_trivially_true()

    def _check_complete(self) -> bool:
        """Checks if the automaton is complete without early exit.

        Here, we essentially check if the disjunction of all outgoing transition guards
        from each state evaluates to `True`.
        """
        is_complete = True
        for q in self.locations:
            if not self._is_state_complete(q):
                self.logger.warning(
                    f"Automaton is incomplete at location: {self.location(q)}"
                )
                is_complete = False

        return is_complete

    def is_complete(self) -> bool:
        """Checks if the automaton is complete.

        Here, we essentially check if the disjunction of all outgoing transition guards
        from each state evaluates to `True`.
        """
        if self._is_complete:
            return self._is_complete
        for q in self.locations:
            if not self._is_state_complete(q):
                self._is_complete = False
                return self._is_complete

        self._is_complete = True
        return self._is_complete

    def is_accepting(self, loc: int) -> bool:
        info = self.location(loc)
        return info.accepting

    def accepting(self) -> Iterable[int]:
        node: int
        acc: bool
        for node, acc in self._graph.nodes(data="accepting"):  # type: ignore
            if acc:
                yield node

    def has_unique_accepting_sink(self) -> bool:
        """Check if the automaton has a unique accepting sink"""
        return len(set(self.accepting())) == 1

    def accepting_sink(self) -> int:
        accepting_states = set(self.accepting())
        if len(accepting_states) == 0:
            raise ValueError("Given automaton does not have any accepting state")
        if len(accepting_states) > 1:
            raise ValueError("Given automaton does not have a unique accepting sink")
        return accepting_states.pop()

    def is_rejecting_sink(self, loc: int) -> bool:
        """Check if location has unique outgoing transition, which is a self loop, and location is not accepting"""
        if self.is_accepting(loc):
            return False
        successors = set(self._graph.successors(loc))
        if len(successors) == 0:
            raise ValueError("Can't find rejecting sink for incomplete automaton")
        if len(successors) > 1:
            return False
        succ = successors.pop()
        if succ != loc:
            return False

        guard = self.get_guard(loc, succ)
        if guard.is_trivially_true():
            return True
        else:
            raise ValueError(f"Looks like automaton is incomplete at location {loc}")

    def rejecting(self) -> Iterable[int]:
        for node in self.locations:
            if self.is_rejecting_sink(node):
                yield node

    def has_unique_rejecting_sink(self) -> bool:
        """Check if the automaton has a unique rejecting sink"""
        return len(set(self.rejecting())) == 1

    def rejecting_sink(self) -> Optional[int]:
        rejecting_states = set(self.rejecting())
        if len(rejecting_states) == 0:
            return None
        if len(rejecting_states) > 1:
            return None
        return rejecting_states.pop()
