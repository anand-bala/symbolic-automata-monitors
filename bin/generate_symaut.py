import argparse
import ast
from pathlib import Path
from typing import Dict, List, NamedTuple, Optional, Tuple

from syma.utils.minimize import minimize_sfa

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

import rtamt
from rtamt.node.abstract_node import AbstractNode

from rtamt_helpers.to_automaton import (
    generate_minimal_symaut_code,
    get_stl_formula,
    get_symbolic_automaton,
    print_automaton_gen_code,
)
from rtamt_helpers.to_ltl_string import to_ltl_string


class Arguments(NamedTuple):
    formula: str
    vars: List[Tuple[str, str]]
    output_file: Optional[Path]
    use_ltlf: bool


def parse_args() -> Arguments:
    parser = argparse.ArgumentParser(
        description="Convert a STL formula into a deterministic finite state automaton",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    parser.add_argument(
        "-o",
        "--output-file",
        help="Output the automaton as a labelled graph",
        type=lambda p: Path(p).resolve(),
        default=None,
    )

    parser.add_argument(
        "--use-ltlf",
        action="store_true",
        help="Use LTLf translation",
    )

    parser.add_argument("formula", help="Temporal Logic formula to parse", type=str)

    parser.add_argument("--var", nargs=2, action="append", type=str)

    args = parser.parse_args()
    vars = args.var if args.var is not None else []

    return Arguments(
        formula=args.formula,
        output_file=args.output_file,
        use_ltlf=args.use_ltlf,
        vars=vars,
    )


def main():
    args = parse_args()
    stl_spec = get_stl_formula(args.formula, *args.vars)
    aut = get_symbolic_automaton(stl_spec, use_ltlf=args.use_ltlf)
    code = generate_minimal_symaut_code(aut, aut_name="aut")
    print(ast.unparse(code))
    # print_automaton_gen_code(stl_spec, use_ltlf=args.use_ltlf)


if __name__ == "__main__":
    main()
