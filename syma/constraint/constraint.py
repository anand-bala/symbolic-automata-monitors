from typing import Mapping, Tuple, Union

import numpy as np
import z3
from z3 import ExprRef, Solver

from syma.alphabet import Alphabet
from syma.constraint.node import BoolVar, IntVar, Node, RealVar
from syma.constraint.smt_translator import Formula2SMT

Value = Union[bool, int, float]
VarNode = Union[BoolVar, IntVar, RealVar]


def formula_to_smt(formula: Node) -> z3.ExprRef:
    return Formula2SMT(formula).translate()


class Constraint(object):
    def __init__(self, alphabet: Alphabet, formula: Node):
        self._alphabet = alphabet
        self._formula = formula
        self._smt_formula: ExprRef = formula_to_smt(self._formula)

    @property
    def formula(self) -> Node:
        return self._formula

    @property
    def alphabet(self):
        return self._alphabet

    @property
    def expr(self) -> ExprRef:
        return self._smt_formula

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
