from itertools import product

import z3

from syma.alphabet import Alphabet
from syma.constraint.helpers.smt import to_smt
from syma.constraint.node import BoolConst, Node, NodeType, Or


def _reduce(alphabet: Alphabet, formula: Node) -> Node:
    if formula.node_type not in (NodeType.And, NodeType.Or):
        return formula

    node_type = formula.node_type
    alph_list = list(alphabet.get_z3_vars())

    predicates = formula.children
    # Get the list of predicate indices in the conjunction
    predicate_set = set(range(len(formula.children)))

    for i, j in product(predicate_set, repeat=2):
        # Make sure both, i and j are in the predicate_set
        if (i not in predicate_set) or (j not in predicate_set):
            continue
        if i == j:
            continue
        p = to_smt(predicates[i])
        q = to_smt(predicates[j])
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

    if node_type == NodeType.And:
        expr: Node = BoolConst(True)
        for p in predicates:
            expr &= p
        return expr
    else:  # node_type == NodeType.Or:
        expr: Node = BoolConst(False)
        for p in predicates:
            expr |= p
        return expr


def minimize_formula(alphabet: Alphabet, formula: Node) -> Node:
    """Minimize the number of And in a DNF formula"""
    if formula.node_type == NodeType.Or:
        reduced = [_reduce(alphabet, expr) for expr in formula.children]
        return _reduce(alphabet, Or(*reduced))
    elif formula.node_type == NodeType.And:
        return _reduce(alphabet, formula)
    return formula
