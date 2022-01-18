"""Provides methods to minimize the size of a symbolic automaton"""

from collections import deque
from functools import reduce
from typing import AbstractSet, Deque, Dict, FrozenSet, Optional, Set

import z3

from syma.automaton import SymbolicAutomaton
from syma.constraint.constraint import Constraint
from syma.constraint.node.node import BoolConst, Node


def _transitions_between_sets(
    sa: SymbolicAutomaton,
    P: AbstractSet[int],
    R: AbstractSet[int],
) -> Constraint:
    guard = BoolConst(False)
    for p in P:
        for r in R:
            if sa.has_transition(p, r):
                guard |= sa.get_guard(p, r).formula

    return Constraint(sa._alphabet, guard).minimize()


def _transitions_into_set(
    sa: SymbolicAutomaton, p: int, R: AbstractSet[int]
) -> Constraint:
    guards: Deque[Node] = deque()

    for q in sa._graph.successors(p):
        if q in R:
            guards.append(sa.get_guard(p, q).formula)

    disjunction = BoolConst(False)
    for guard in guards:
        disjunction |= guard

    return Constraint(sa._alphabet, disjunction)


def _split(
    p_set: FrozenSet[int],
    part1: FrozenSet[int],
    part2: FrozenSet[int],
    partitions: Set[FrozenSet[int]],
    candidates: Set[FrozenSet[int]],
):
    partitions.remove(p_set)
    partitions.add(part1)
    partitions.add(part2)

    if p_set in candidates:
        candidates.remove(p_set)
        candidates.add(part1)
        candidates.add(part2)
    else:
        if len(part1) <= len(part2):
            candidates.add(part1)
        else:
            candidates.add(part2)


def _local_minterms(
    sa: SymbolicAutomaton,
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
        case1 = Constraint(sa._alphabet, psi.formula & phi.formula)
        case2 = Constraint(sa._alphabet, psi.formula & (~phi.formula))
        case3 = Constraint(sa._alphabet, (~psi.formula) & phi.formula)

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


def _reconstitute_automaton(
    old_sa: SymbolicAutomaton, partitions: Set[FrozenSet[int]]
) -> SymbolicAutomaton:
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
    node_map = {i: part for i, part in enumerate(sorted(partitions, key=tuple))}
    acc_map: Dict[int, bool] = dict()
    initial_map: Dict[int, bool] = dict()
    for i, part in node_map.items():
        acc = all(old_sa.is_accepting(q) for q in part)
        initial = all(q == old_sa.initial for q in part)
        if initial:
            assert len(part) == 1
        acc_map[i] = acc
        initial_map[i] = initial

    aut = SymbolicAutomaton()
    aut._alphabet = old_sa._alphabet

    # Add the new nodes
    for i in node_map.keys():
        accepting = acc_map[i]
        initial = initial_map[i]
        aut.add_location(i, accepting=accepting, initial=initial)

    # Add the new transitions
    for i, P in node_map.items():
        for j, R in node_map.items():
            guard = _transitions_between_sets(old_sa, P, R)
            if not guard.is_trivially_false():
                aut.add_transition(i, j, guard=guard)

    return aut


def minimize_sfa(sa: SymbolicAutomaton) -> SymbolicAutomaton:
    """Symbolic finite automaton minimization algorithm.

    This follows the algorithm used in [1].

    [1] : L. D’Antoni and M. Veanes, "Minimization of symbolic automata,"
        in Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages,
        New York, NY, USA, Jan. 2014, pp. 541–553.
        doi: 10.1145/2535838.2535849.

    """
    states = frozenset(sa.locations)
    final = frozenset(sa.accepting())
    non_final = states - final

    partitions: Set[FrozenSet[int]] = {final, non_final}

    # partitions = {q: acc if sa.is_accepting(q) else non_acc for q in states}

    candidates = set()  # type: Set[FrozenSet[int]]
    if len(non_final) <= len(final):
        candidates.add(non_final)
    else:
        candidates.add(final)

    while len(candidates) > 0:
        r_set = candidates.pop()
        g_set = {p: _transitions_into_set(sa, p, r_set) for p in states}
        s_set = frozenset(g_set.keys())

        for part in partitions:
            part1 = part & s_set
            part2 = part - s_set
            if len(part1) != 0 and len(part2) != 0:
                _split(part, part1, part2, partitions, candidates)

        iterate = True
        while iterate:
            iterate = False
            relevant = {part for part in partitions if len(part & s_set) > 0}
            for part in relevant:
                part1 = _local_minterms(sa, g_set, part)
                if len(part1) < len(part):
                    iterate = iterate or (len(part) > 2)
                    part2 = part - part1
                    _split(part, part1, part2, partitions, candidates)

    return _reconstitute_automaton(sa, partitions)
