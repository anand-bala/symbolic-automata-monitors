import rtamt
import spot
from rtamt import STLSpecification

from syma import SymbolicAutomaton

from .to_ltl_string import to_ltl_string


def to_omega_automaton(formula: str) -> spot.twa_graph:
    aut = spot.translate(
        formula, "Buchi", "sbacc", "state-based", "complete", "small", "unambiguous"
    )
    return aut


def to_automaton_gen_code(spec: STLSpecification) -> str:
    ltl_formula, predicate_map = to_ltl_string(spec)
    aut = to_omega_automaton(ltl_formula)

    assert aut.is_deterministic()
    assert aut.prop_complete().is_true()
