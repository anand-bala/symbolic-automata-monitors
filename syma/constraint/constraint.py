from typing import TYPE_CHECKING, Iterable, Mapping, Tuple, Union

import z3

from syma.constraint.minimization import minimize_and
from syma.constraint.node.node import (BoolConst, BoolVar, Constant, IntVar,
                                       Node, NodeType, RealVar)
from syma.constraint.smt_translator import Formula2SMT
from syma.constraint.transform import to_dnf, to_nnf

if TYPE_CHECKING:
    from syma.alphabet import Alphabet


Value = Union[bool, int, float]
VarNode = Union[BoolVar, IntVar, RealVar]


def formula_to_smt(formula: Node) -> z3.ExprRef:
    return Formula2SMT(formula).translate()


def check_trivially_false(formula: z3.ExprRef) -> bool:
    solver = z3.Solver()
    solver.add(formula)
    result = solver.check()

    return result == z3.unsat


def check_trivially_true(vars: Iterable[z3.ExprRef], expr: z3.ExprRef) -> bool:
    solver = z3.Solver()
    solver.add(z3.ForAll(list(vars), expr))
    result = solver.check()

    return result == z3.sat


class Constraint(object):
    def __init__(self, alphabet: "Alphabet", formula: Union[Node, bool]):
        self._alphabet = alphabet
        if isinstance(formula, bool):
            formula = BoolConst(formula)

        formula = minimize_and(self.alphabet, to_dnf(formula))
        z3_expr = formula_to_smt(formula)

        if check_trivially_false(z3_expr):
            formula = Constant(False)
            z3_expr = z3.BoolVal(False)
        elif check_trivially_true(alphabet.get_z3_vars(), z3_expr):
            formula = Constant(True)
            z3_expr = z3.BoolVal(True)
        else:
            formula = formula

        self._formula = formula
        self._smt_formula: z3.ExprRef = z3_expr

    @property
    def formula(self) -> Node:
        return self._formula

    @property
    def alphabet(self):
        return self._alphabet

    @property
    def expr(self) -> z3.ExprRef:
        return self._smt_formula

    def is_trivially_false(self) -> bool:
        """Check if the formula is trivially false"""
        if self.formula.node_type == NodeType.BoolConst:
            return self.formula.value is False  # type: ignore
        return check_trivially_false(self.expr)

    def is_trivially_true(self) -> bool:
        """Check if the formula is trivially true"""
        if self.formula.node_type == NodeType.BoolConst:
            return self.formula.value  # type: ignore
        return check_trivially_true(self.alphabet.get_z3_vars(), self.expr)

    def check_sat(self, values: Mapping[str, Value]) -> bool:
        def convert(var_name: str, var_val: Value) -> Tuple[z3.ExprRef, z3.ExprRef]:
            if isinstance(var_val, bool):
                val = z3.BoolVal(var_val)
            elif isinstance(var_val, int):
                val = z3.IntVal(var_val)
            elif isinstance(var_val, float):
                val = z3.RealVal(var_val)
            else:
                raise ValueError(f"Unsupported value type: {type(var_val)}")
            var = self._alphabet.get_var(var_name)
            return formula_to_smt(var), val

        # First get a list of Variable to Value tuples
        var_vals = [convert(name, val) for name, val in values.items()]
        # Then use z3.substitute to replace the variables with the values and evaluate
        # it.
        new_expr = z3.substitute(self.expr, *var_vals)

        solver = z3.Solver()
        solver.add(new_expr)
        return solver.check() == z3.sat

    def to_nnf(self) -> "Constraint":
        return Constraint(self.alphabet, to_nnf(self.formula))

    def to_dnf(self) -> "Constraint":
        return Constraint(self.alphabet, to_dnf(self.formula))

    def minimize(self) -> "Constraint":
        dnf = self.to_dnf()
        minim = minimize_and(self.alphabet, dnf.formula)
        return Constraint(self.alphabet, minim)

    def __repr__(self):
        return repr(self._formula)

    def __str__(self):
        return str(self._formula)
