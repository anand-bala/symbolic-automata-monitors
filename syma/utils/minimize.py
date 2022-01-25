"""Provides methods to minimize the size of a symbolic automaton"""

from collections import deque
from typing import AbstractSet, Deque, Dict, FrozenSet, Optional, Set

from syma.automaton import SymbolicAutomaton
from syma.constraint.constraint import Constraint
from syma.constraint.node.node import BoolConst, Node


class _MinimizeSFA:
    def __init__(self, sa: SymbolicAutomaton):
        self.sa = sa
        self.states = frozenset(sa.locations)
        self.final = frozenset(sa.accepting())
        self.non_final = self.states - self.final

        self.partitions: Set[FrozenSet[int]] = {self.final, self.non_final}
        self.candidates: Set[FrozenSet[int]] = set()
        if len(self.non_final) <= len(self.final):
            self.candidates.add(self.non_final)
        else:
            self.candidates.add(self.final)

        self.guard_cache: Dict[str, Constraint] = dict()

    def run(self) -> SymbolicAutomaton:
        while len(self.candidates) > 0:
            r_set = self.candidates.pop()
            g_set = {p: self._transitions_into_set(p, r_set) for p in self.states}
            s_set = frozenset(g_set.keys())

            for part in self.partitions:
                part1 = part & s_set
                part2 = part - s_set
                if len(part1) != 0 and len(part2) != 0:
                    self._split(part, part1, part2)

            iterate = True
            while iterate:
                iterate = False
                relevant = {part for part in self.partitions if len(part & s_set) > 0}
                for part in relevant:
                    part1 = self._local_minterms(g_set, part)
                    if len(part1) < len(part):
                        iterate = iterate or (len(part) > 2)
                        part2 = part - part1
                        self._split(part, part1, part2)

        return self._reconstitute_automaton()

    def _reconstitute_automaton(self) -> SymbolicAutomaton:
        """
        We have partitioned the states based on equivalent classes.
        Now we need to create a new automaton such that:

        1. Each partition set represents a node in the new automaton.
        2. For any two partition sets, P and R, for all edges that goes from a state in P
           to a state in R, a new edge is created with the guard being the disjunction of
           each individual edge guards.
        """
        # Create a mapping of new nodes to partition sets, along with if they are
        # accepting or not
        # Sort the partitions. Just for debugging purposes
        node_map = {
            i: part for i, part in enumerate(sorted(self.partitions, key=tuple))
        }
        acc_map: Dict[int, bool] = dict()
        initial_map: Dict[int, bool] = dict()
        for i, part in node_map.items():
            acc = all(self.sa.is_accepting(q) for q in part)
            initial = all(q == self.sa.initial for q in part)
            if initial:
                assert len(part) == 1
            acc_map[i] = acc
            initial_map[i] = initial

        aut = SymbolicAutomaton()
        aut._alphabet = self.sa._alphabet

        # Add the new nodes
        for i in node_map.keys():
            accepting = acc_map[i]
            initial = initial_map[i]
            aut.add_location(i, accepting=accepting, initial=initial)

        # Add the new transitions
        for i, P in node_map.items():
            for j, R in node_map.items():
                guard = self._transitions_between_sets(P, R)
                if not guard.is_trivially_false():
                    aut.add_transition(i, j, guard=guard, minimize=False)

        return aut

    def _transitions_between_sets(
        self,
        P: AbstractSet[int],
        R: AbstractSet[int],
    ) -> Constraint:
        guard = BoolConst(False)
        for p in P:
            for r in R:
                if self.sa.has_transition(p, r):
                    guard |= self.sa.get_guard(p, r).formula

        guard_str = str(guard)
        if guard_str not in self.guard_cache:
            self.guard_cache[guard_str] = Constraint(
                self.sa._alphabet, guard
            ).minimize()

        return self.guard_cache[guard_str]

    def _transitions_into_set(self, p: int, R: AbstractSet[int]) -> Constraint:
        guards: Deque[Node] = deque()

        for q in self.sa._graph.successors(p):
            if q in R:
                guards.append(self.sa.get_guard(p, q).formula)

        disjunction = BoolConst(False)
        for guard in guards:
            disjunction |= guard

        disjunction_str = str(disjunction)
        if disjunction_str not in self.guard_cache:
            self.guard_cache[disjunction_str] = Constraint(
                self.sa._alphabet, disjunction
            ).minimize()

        return self.guard_cache[disjunction_str]

    def _split(
        self,
        p_set: FrozenSet[int],
        part1: FrozenSet[int],
        part2: FrozenSet[int],
    ):
        self.partitions.remove(p_set)
        self.partitions.add(part1)
        self.partitions.add(part2)

        if p_set in self.candidates:
            self.candidates.remove(p_set)
            self.candidates.add(part1)
            self.candidates.add(part2)
        else:
            if len(part1) <= len(part2):
                self.candidates.add(part1)
            else:
                self.candidates.add(part2)

    def _local_minterms(
        self,
        g_set: Dict[int, Constraint],
        part: FrozenSet[int],
    ) -> FrozenSet[int]:
        part1: Set[int] = set()
        psi: Optional[Constraint] = None

        splitter_found = False
        for q in part:
            if psi is None:
                psi = g_set[q]
                part1.add(q)
                continue

            phi = g_set[q]
            case2 = Constraint(self.sa._alphabet, psi.formula & (~phi.formula))
            case3 = Constraint(self.sa._alphabet, (~psi.formula) & phi.formula)
            # Cache the cases
            case1_f = psi.formula & phi.formula
            case1_str = str(case1_f)
            if case1_str not in self.guard_cache:
                self.guard_cache[case1_str] = Constraint(
                    self.sa._alphabet, psi.formula & phi.formula
                )
            case1 = self.guard_cache[case1_str]

            case2_f = psi.formula & (~phi.formula)
            case2_str = str(case2_f)
            if case2_str not in self.guard_cache:
                self.guard_cache[case2_str] = Constraint(
                    self.sa._alphabet, psi.formula & phi.formula
                )
            case2 = self.guard_cache[case2_str]

            case3_f = (~psi.formula) & phi.formula
            case3_str = str(case3_f)
            if case3_str not in self.guard_cache:
                self.guard_cache[case3_str] = Constraint(
                    self.sa._alphabet, psi.formula & phi.formula
                )
            case3 = self.guard_cache[case3_str]

            if splitter_found and case1.is_sat():
                part1.add(q)
                psi = case1
            elif case2.is_sat():
                psi = case2  # Refine local minterm
                splitter_found = True
            elif case3.is_sat():  # psi implies phi
                part1.clear()
                part1.add(q)
                psi = case3  # swap the local minterm
                splitter_found = True
            else:  # psi is equivalent to phi
                part1.add(q)

        return frozenset(part1)


def minimize_sfa(sa: SymbolicAutomaton) -> SymbolicAutomaton:
    """Symbolic finite automaton minimization algorithm.

    This follows the algorithm used in [1].

    [1] : L. D’Antoni and M. Veanes, "Minimization of symbolic automata,"
        in Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages,
        New York, NY, USA, Jan. 2014, pp. 541–553.
        doi: 10.1145/2535838.2535849.

    """
    return _MinimizeSFA(sa).run()
