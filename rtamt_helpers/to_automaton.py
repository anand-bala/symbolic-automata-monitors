from typing import Dict

import rtamt
import spot
import z3
from rtamt import STLSpecification
from rtamt.node.abstract_node import AbstractNode

from .to_constraint import from_node_to_constraint as to_constraint
from .to_ltl_string import to_ltl_string
from .to_z3_expr import from_node_to_z3


def to_omega_automaton(formula: str) -> spot.twa_graph:
    aut = spot.translate(
        formula,
        "Buchi",
        "sbacc",
        "state-based",
        "complete",
        "unambiguous",
        "deterministic",
    )
    return aut


def get_z3_predicates(
    predicate_map: Dict[str, AbstractNode], spec: STLSpecification
) -> Dict[str, z3.ExprRef]:
    z3_predicates = {
        key: from_node_to_z3(val, spec.var_type_dict)
        for key, val in predicate_map.items()
    }
    return z3_predicates


def print_automaton_gen_code(spec: STLSpecification):
    ltl_formula, predicate_map = to_ltl_string(spec)

    print(f"# STL Formula is: {spec.spec}")
    # print(f"# LTL Formula is:\n\t{ltl_formula}")
    #
    # Convert the rtamt predicates to syma Constraints
    constraint_map = {
        label: to_constraint(pred, spec.var_type_dict)
        for label, pred in predicate_map.items()
    }

    # Convert the LTL formula to an automaton
    aut = to_omega_automaton(ltl_formula)
    assert aut.is_deterministic()  # type: ignore
    assert aut.prop_complete().is_true()  # type: ignore
    # assert aut.prop_terminal().is_true()  # type: ignore
    assert aut.is_unambiguous()  # type: ignore

    # Print Python code to stdout
    print("aut = SymbolicAutomaton()")

    print("")
    print("# Symbolic variable declarations")
    print("# TODO: Change the domain as required!")
    for var_name, var_type in spec.var_type_dict.items():
        type_fn = "real" if var_type == "float" else var_type
        print(f'{var_name} = aut.declare_{type_fn}("{var_name}", "{var_type}")')

    print("")
    print("# Predicate labels")
    for label, expr in constraint_map.items():
        print(f"{label} = {str(expr)}")

    bdict = aut.get_dict()  # type: ignore

    print("")
    print("# Location definitions")
    # Get initial location
    init_state: int = aut.get_init_state_number()  # type: ignore
    for state in range(0, aut.num_states()):  # type: ignore
        initial = state == init_state
        accepting = aut.state_is_accepting(state)  # type: ignore
        print(f"aut.add_location({state}, initial={initial}, accepting={accepting})")

    print("")
    print("# Transition definitions")
    for state in range(0, aut.num_states()):  # type: ignore
        for tr in aut.out(state):  # type: ignore
            guard_str = spot.bdd_format_formula(bdict, tr.cond)
            if guard_str == "1":
                guard_str = "True"
            else:
                guard_str = guard_str.replace("!", "~")
            print(f"aut.add_transition({tr.src}, {tr.dst}, guard=({guard_str}))")
