import ast
from typing import Dict, Optional, Tuple, Union

import z3
from rtamt import STLSpecification
from rtamt.node.abstract_node import AbstractNode

from syma.alphabet import Alphabet
from syma.automaton import SymbolicAutomaton
from syma.constraint.constraint import Constraint
from syma.constraint.node.node import BoolVar, IntVar, Node, RealVar
from syma.utils.minimize import minimize_sfa

from .to_z3_expr import from_node_to_z3

try:
    import spot
except ImportError as e:
    print(e)
    print("")
    print(
        """
The best way to install SPOT is to using conda:
    conda install spot -c conda-forge
If you are not using conda, see https://spot.lrde.epita.fr/install.html
"""
    )
    raise e


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
    ltl_formula: str,
    *,
    use_ltlf=False,
    alphabet: Optional[Union[Alphabet, Dict[str, str]]] = None,
) -> SymbolicAutomaton:
    """
    :param ltl_formula: A LTL string formula consumable by spot
    :param use_ltlf: Use the LTLf feature from spot (usually set to `False`)
    :param alphabet: An optional domain for the variables.
    """
    #
    # Convert the rtamt predicates to syma Constraints
    # constraint_map = {
    #     label: to_constraint(pred, spec.var_type_dict)
    #     for label, pred in predicate_map.items()
    # }

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
        if isinstance(alphabet, Alphabet):
            sym_aut._alphabet = alphabet
        elif isinstance(alphabet, dict):
            for var_name, var_type in alphabet.items():
                if var_type == "float":
                    sym_aut.declare_real(var_name)
                elif var_type == "int":
                    sym_aut.declare_int(var_name)
                else:  # assume bool
                    sym_aut.declare_bool(var_name)
                # else:
                #     raise RuntimeError(f"Unsupported variable type: {(var_name, var_type)}")
        else:
            raise TypeError(f"Unsupported alphabet type: {type(alphabet)}")
    else:
        # Assume all are bool
        aps = omega_aut.ap()  # type: ignore
        for ap in aps:
            sym_aut.declare_bool(str(ap))

    alphabet = sym_aut._alphabet

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
                guard_str = guard_str.replace('"', "")
            if guard_str not in guard_map:
                guard_node: Node = eval(guard_str, None, sym_aut._alphabet.vars)
                guard_map[guard_str] = Constraint(alphabet, guard_node).minimize()
            guard: Constraint = guard_map[guard_str]

            sym_aut.add_transition(tr.src, tr.dst, guard=guard, minimize=False)

    return sym_aut


def generate_minimal_symaut_code(
    aut: SymbolicAutomaton, aut_name: str = "aut"
) -> ast.Module:
    """Generate the AST for automaton (to easily create it for later use without too much solver overhead).

    `aut_name` should contain the name of the automaton variable in the AST.
    """
    aut = minimize_sfa(aut)

    assert aut.is_complete()

    ret_ast = ast.parse(
        f"""
from syma.automaton import SymbolicAutomaton

{aut_name} = SymbolicAutomaton()

# Symbolic variable declarations
# TODO: Change the domain as required!
        """
    )

    # Declare the symbolic variables
    for var_name, var in aut._alphabet.vars.items():
        if isinstance(var, IntVar):
            type_fn = "int"
        elif isinstance(var, BoolVar):
            type_fn = "bool"
        elif isinstance(var, RealVar):
            type_fn = "real"
        else:
            raise TypeError(f"Unknown variable type in alphabet: {(var_name, var)}")
        statement = ast.parse(
            f'{var_name} = {aut_name}.declare_{type_fn}("{var_name}")'
        ).body
        ret_ast.body.extend(statement)

    # Add the automaton locations
    for q in aut.locations:
        initial = aut.initial == q
        accepting = aut.is_accepting(q)
        statement = ast.parse(
            f"{aut_name}.add_location({q}, initial={initial}, accepting={accepting})"
        ).body
        ret_ast.body.extend(statement)

    # Add the transitions in the automaton
    for src, dst in sorted(aut.transitions):
        guard_str = str(aut.get_guard(src, dst))
        statement = ast.parse(
            f"aut.add_transition({src}, {dst}, guard=({guard_str}))"
        ).body
        ret_ast.body.extend(statement)

    return ret_ast
