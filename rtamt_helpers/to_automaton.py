from typing import Dict, Optional, Tuple

import spot
import z3
from rtamt import STLSpecification
from rtamt.node.abstract_node import AbstractNode

from syma.alphabet import Alphabet
from syma.automaton import SymbolicAutomaton
from syma.constraint.constraint import Constraint
from syma.constraint.node.node import Node
from syma.utils.minimize import minimize_sfa

from .to_constraint import from_node_to_constraint as to_constraint
from .to_ltl_string import to_ltl_string
from .to_z3_expr import from_node_to_z3


def get_stl_formula(formula: str, *vars: Tuple[str, str]) -> STLSpecification:
    spec = STLSpecification()

    for var in vars:
        spec.declare_var(*var)

    spec.spec = formula

    spec.parse()

    return spec


def to_omega_automaton(formula: str, *, use_ltlf=False) -> spot.twa_graph:
    if use_ltlf:
        aut = spot.from_ltlf(formula).translate("Buchi", "state-based", "complete")
        # Remove "alive" atomic proposition
        rem = spot.remove_ap()
        rem.add_ap("alive")
        aut = rem.strip(aut)
        # Simplify result and print it.  Use postprocess('ba', 'det')
        # if you always want a deterministic automaton.
        aut = spot.postprocess(aut, "ba", "det", "complete", "unambiguous")
    else:
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


def get_symbolic_automaton(
    spec: STLSpecification,
    *,
    use_ltlf=False,
    alphabet: Optional[Alphabet] = None,
) -> SymbolicAutomaton:
    ltl_formula, predicate_map = to_ltl_string(spec)
    #
    # Convert the rtamt predicates to syma Constraints
    constraint_map = {
        label: to_constraint(pred, spec.var_type_dict)
        for label, pred in predicate_map.items()
    }

    # Convert the LTL formula to an automaton
    omega_aut = to_omega_automaton(ltl_formula, use_ltlf=use_ltlf)
    assert omega_aut.is_deterministic()  # type: ignore
    assert omega_aut.prop_complete().is_true()  # type: ignore
    # assert omega_aut.prop_terminal().is_true()  # type: ignore
    assert omega_aut.is_unambiguous()  # type: ignore

    # Create the symbolic automaton with this omega automaton.
    # NOTE: The domain of the variables don't matter and can be supplied by the user
    # after the code is printed
    sym_aut = SymbolicAutomaton()
    if alphabet is not None:
        sym_aut._alphabet = alphabet
    else:
        alphabet = sym_aut._alphabet
        for var_name, var_type in spec.var_type_dict.items():
            if var_type == "float":
                sym_aut.declare_real(var_name)
            elif var_type == "int":
                sym_aut.declare_int(var_name)
            elif var_type == "bool":
                sym_aut.declare_bool(var_name)
            else:
                raise RuntimeError(f"Unsupported variable type: {(var_name, var_type)}")

    # Add the locations in the omega automaton into the symbolic automaton
    init_state: int = omega_aut.get_init_state_number()  # type: ignore
    for state in range(0, omega_aut.num_states()):  # type: ignore
        initial = state == init_state
        accepting: bool = omega_aut.state_is_accepting(state)  # type: ignore
        sym_aut.add_location(state, initial=initial, accepting=accepting)

    # Global BDD dictionary
    bdict = omega_aut.get_dict()  # type: ignore

    # We will make a map of all transition guards in the omega automaton to the
    # Constraint values. This will minimize some unnecessary computations.
    # NOTE: We will have to use the eval function, but will make sure the context in
    # the eval is only what is required.
    guard_map: Dict[str, Constraint] = dict()
    for state in range(0, omega_aut.num_states()):  # type: ignore
        for tr in omega_aut.out(state):  # type: ignore
            guard_str = spot.bdd_format_formula(bdict, tr.cond)
            if guard_str == "1":
                guard_str = "True"
            else:
                guard_str = guard_str.replace("!", "~")
            if guard_str not in guard_map:
                guard_node: Node = eval(guard_str, None, constraint_map)
                guard_map[guard_str] = Constraint(alphabet, guard_node).minimize()
            guard: Constraint = guard_map[guard_str]

            sym_aut.add_transition(tr.src, tr.dst, guard=guard, minimize=False)

    return sym_aut


def print_automaton_gen_code(spec: STLSpecification, *, use_ltlf=False):
    ltl_formula, predicate_map = to_ltl_string(spec)

    print(f"# STL Formula is: {spec.spec}")
    print(f"# LTL Formula is:\n#\t{ltl_formula}")
    #
    # Convert the rtamt predicates to syma Constraints
    constraint_map = {
        label: to_constraint(pred, spec.var_type_dict)
        for label, pred in predicate_map.items()
    }

    # Convert the LTL formula to an automaton
    aut = to_omega_automaton(ltl_formula, use_ltlf=use_ltlf)
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


def generate_minimal_symaut_code(aut: SymbolicAutomaton):
    aut = minimize_sfa(aut)

    assert aut.is_complete()

    print("aut = SymbolicAutomaton()")
    print("")
    print("# TODO: Symbolic variable declarations")
    print("")

    for q in aut.locations:
        initial = aut.initial == q
        accepting = aut.is_accepting(q)
        print(f"aut.add_location({q}, initial={initial}, accepting={accepting})")

    print("")
    print("# Transition definitions")
    for src, dst in sorted(aut.transitions):
        guard_str = str(aut.get_guard(src, dst))
        print(f"aut.add_transition({src}, {dst}, guard=({guard_str}))")
