import argparse
import ast
import importlib.util
from pathlib import Path
from typing import List, NamedTuple, Optional, Tuple

from rtamt_helpers.to_ltl_string import to_ltl_string

if importlib.util.find_spec("spot") is None:
    print("`spot` module not found and is required this script.")
    print("")
    print(
        """
The best way to install SPOT is to using conda:

    conda install spot -c conda-forge

If you are not using conda, see https://spot.lrde.epita.fr/install.html
"""
    )
    raise ImportError("`spot` module not found")


from rtamt_helpers.to_automaton import (
    generate_minimal_symaut_code,
    get_stl_formula,
    get_symbolic_automaton,
)


class Arguments(NamedTuple):
    formula: str
    vars: List[Tuple[str, str]]
    output_file: Optional[Path]
    use_ltlf: bool
    use_rtamt: bool


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

    parser.add_argument(
        "--disable-rtamt",
        action="store_false",
        help="Disable use of RTAMT",
    )

    parser.add_argument("formula", help="Temporal Logic formula to parse", type=str)

    parser.add_argument("--var", nargs=2, action="append", type=str)

    args = parser.parse_args()
    vars = args.var if args.var is not None else []

    return Arguments(
        formula=args.formula,
        output_file=args.output_file,
        use_ltlf=args.use_ltlf,
        use_rtamt=args.disable_rtamt,
        vars=vars,
    )


def main():
    args = parse_args()
    if args.use_rtamt:
        stl_spec = get_stl_formula(args.formula, *args.vars)
        ltl_formula, _ = to_ltl_string(stl_spec)
    else:
        ltl_formula = args.formula
    aut = get_symbolic_automaton(
        ltl_formula, use_ltlf=args.use_ltlf, alphabet=dict(args.vars)
    )
    code = generate_minimal_symaut_code(aut, aut_name="aut")
    print(ast.unparse(code))
    # print_automaton_gen_code(stl_spec, use_ltlf=args.use_ltlf)


if __name__ == "__main__":
    main()
