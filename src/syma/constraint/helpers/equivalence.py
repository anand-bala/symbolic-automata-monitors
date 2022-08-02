"""Provides a function to check if two constraints are equivalent.
"""


import z3

from syma.constraint.constraint import Constraint


def is_equivalent(x: Constraint, y: Constraint) -> bool:
    """Check if two constraints are equivalent"""

    assert (
        x.alphabet == y.alphabet
    ), "Cannot compare constraints with different effective boolean alphabets"

    zx = x.expr
    zy = y.expr

    xtoy = z3.Implies(zx, zy)
    ytox = z3.Implies(zy, zx)
    expr = z3.ForAll(list(x.alphabet.get_z3_vars()), z3.And(xtoy, ytox))

    solver = z3.Solver()
    solver.add(expr)
    return solver.check() == z3.sat
