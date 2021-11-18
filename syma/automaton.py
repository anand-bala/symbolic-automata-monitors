import logging
from dataclasses import dataclass
from typing import Iterable, Optional, Tuple, Union

import networkx as nx
import z3

from syma.alphabet import Alphabet
from syma.constraint.constraint import Constraint
from syma.constraint.node import BoolVar, IntVar, RealVar
from syma.constraint.node.node import BoolConst, Node
from syma.constraint.transform import to_dnf

VarNode = Union[BoolVar, IntVar, RealVar]


@dataclass
class Location(object):
    id: int
    initial: bool = False
    accepting: bool = False


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
        self._alphabet = Alphabet()  # alphabet (effective Boolean algebra)
        self._graph = nx.DiGraph()  # automaton structure
        self._initial_location = None
        self.logger = logging.getLogger(__name__)

    def add_var(self, name, domain):
        self._alphabet.add_var(name, domain)

    def declare_bool(self, name: str, domain: Optional[Tuple] = None) -> BoolVar:
        var = BoolVar(name)
        self.add_var(var, domain)
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

    def add_transition(self, src: int, dst: int, guard: Union[Constraint, Node, bool]):
        if (src, dst) in self._graph.edges:
            raise ValueError(
                f"Transition from {src} to {dst} already exists. Did you want to update the guard?"
            )
        if isinstance(guard, Node):
            guard = Constraint(self._alphabet, guard)
        elif isinstance(guard, bool):
            guard = Constraint(self._alphabet, BoolConst(guard))
        self._graph.add_edge(src, dst, guard=guard)

    def location(self, node: int) -> Location:
        data = self._graph.nodes[node]
        return Location(id=node, initial=data["initial"], accepting=data["accepting"])

    def __getitem__(self, node: int) -> Location:
        return self.location(node)

    def transition(self, src: int, dst: int) -> Transition:
        data = self._graph.edges[src, dst]
        return Transition(src=src, dst=dst, guard=data["guard"])

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
    def initial(self) -> int:
        if self._initial_location is None:
            raise ValueError("No initial location assigned in the automaton")
        return self._initial_location

    @property
    def accepting(self) -> Iterable[int]:
        node: int
        acc: bool
        for node, acc in self._graph.nodes(data="accepting"):  # type: ignore
            if acc:
                yield node

    def in_edges(self, q: int) -> Iterable[Tuple[int, int]]:
        for q_ in self._graph.predecessors(q):
            yield q_, q

    def out_edges(self, q: int) -> Iterable[Tuple[int, int]]:
        for q_ in self._graph.successors(q):
            yield q, q_

    def is_complete(self) -> bool:
        """Checks if the automaton is complete.

        Here, we essentially check if the disjunction of all outgoing transition guards
        from each state evaluates to `True`.
        """
        for q in self.locations:
            out_guards = [
                self.get_guard(q, q_).expr for q_ in self._graph.successors(q)
            ]
            disjunction = z3.Or(*out_guards)
            solver = z3.Solver()
            solver.add(z3.ForAll(list(self._alphabet.get_z3_vars()), disjunction))
            if solver.check() != z3.sat:
                self.logger.warning(
                    f"Automaton is incomplete at location: {self.location(q)}"
                )
                return False

        return True
