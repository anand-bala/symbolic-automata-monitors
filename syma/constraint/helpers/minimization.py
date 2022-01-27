from itertools import product
from typing import TYPE_CHECKING

import z3

from syma.constraint.helpers.smt import to_smt
from syma.constraint.node import BoolConst, Node, NodeType, Or

if TYPE_CHECKING:
    from syma.alphabet import Alphabet

def _reduce_or(alphabet: "Alphabet", formula: Node) -> Node:
    if formula.node_type != NodeType.Or:
        return formula

    alph_list = list(alphabet.get_z3_vars())

    predicates = formula.children
    # Get the list of predicate indices in the conjunction
    predicate_set = set(range(len(formula.children)))
    # Cache the z3 exprs for each child
    z3_predicates = [to_smt(e) for e in predicates]

    for i, j in product(predicate_set, repeat=2):
        # Make sure both, i and j are in the predicate_set
        if (i not in predicate_set) or (j not in predicate_set):
            continue
        if i == j:
            continue
        p = z3_predicates[i]
        q = z3_predicates[j]
        # Check if p -> q is Sat for all input alphabet
        solver = z3.Solver()
        solver.add(z3.ForAll(alph_list, z3.Implies(p, q)))
        if solver.check() == z3.sat:
            # The product consumes the iterable, so it is safe to modify predicate_set
            predicate_set.remove(i)

    predicates = [predicates[i] for i in predicate_set]
    assert (
        len(predicates) >= 1
    ), "At least one predicate must be there after minimization"

    expr: Node = BoolConst(False)
    for p in predicates:
        expr |= p
    return expr

def _reduce(alphabet: "Alphabet", formula: Node) -> Node:
    if formula.node_type != NodeType.And:
        return formula

    alph_list = list(alphabet.get_z3_vars())

    predicates = formula.children
    # Get the list of predicate indices in the conjunction
    predicate_set = set(range(len(formula.children)))
    # Cache the z3 exprs for each child
    z3_predicates = [to_smt(e) for e in predicates]

    for i, j in product(predicate_set, repeat=2):
        # Make sure both, i and j are in the predicate_set
        if (i not in predicate_set) or (j not in predicate_set):
            continue
        if i == j:
            continue
        p = z3_predicates[i]
        q = z3_predicates[j]
        # Check if p -> q is Sat for all input alphabet
        solver = z3.Solver()
        solver.add(z3.ForAll(alph_list, z3.Implies(p, q)))
        if solver.check() == z3.sat:
            # The product consumes the iterable, so it is safe to modify predicate_set
            predicate_set.remove(j)

    predicates = [predicates[i] for i in predicate_set]
    assert (
        len(predicates) >= 1
    ), "At least one predicate must be there after minimization"

    expr: Node = BoolConst(True)
    for p in predicates:
        expr &= p
    return expr


def minimize_formula(alphabet: "Alphabet", formula: Node) -> Node:
    """Minimize the number of And in a DNF formula"""
    if formula.node_type == NodeType.Or:
        reduced = [_reduce(alphabet, expr) for expr in formula.children]
        return _reduce_or(alphabet, Or(*reduced))
    elif formula.node_type == NodeType.And:
        return _reduce(alphabet, formula)
    return formula
