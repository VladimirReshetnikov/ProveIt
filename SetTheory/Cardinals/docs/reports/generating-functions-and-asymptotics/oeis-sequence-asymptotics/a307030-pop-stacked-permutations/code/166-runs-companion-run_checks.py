#!/usr/bin/env python3
"""Bounded JSON-only command line for Report 166's computational companion."""

import argparse
import json
import sys

# Do not create bytecode-cache files when invoked as the documented CLI.
sys.dont_write_bytecode = True

from run_filtration import check_filtration
from run_polynomials import (
    CheckFailure, bounded_integer, check_run_polynomials,
)
from run_slopes import certify_slopes


class _JsonArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        raise ValueError(message)


def _parser():
    parser = _JsonArgumentParser(add_help=False)
    parser.add_argument("command", nargs="?", default="all",
                        choices=("all", "coefficients", "filtration", "slopes"))
    parser.add_argument("--n", type=int, default=12)
    parser.add_argument("--literal", type=int, default=7)
    parser.add_argument("--filtration", type=int, default=None)
    parser.add_argument("--include-data", action="store_true")
    parser.add_argument("--help", action="store_true")
    return parser


def main(argv=None):
    """Print exactly one JSON value and return 0 (success), 1 (check), or 2 (input).

    With no arguments, check complete rows through n=12, literal images through
    n=7, published k<=5 fixtures, and the exact slope certificate. Formal
    filtration is optional for `all`; `filtration` alone defaults to k=5.
    """
    try:
        args = _parser().parse_args(argv)
        if args.help:
            output = {
                "usage": "python -B run_checks.py [all|coefficients|filtration|slopes] [options]",
                "options": {
                    "--n": "0..40; complete polynomial degree bound (default 12)",
                    "--literal": "0..min(n,9); literal image bound (default 7)",
                    "--filtration": "1..12; optional for all, default 5 for filtration",
                    "--include-data": "include complete rows or exponential-polynomial examples",
                },
                "output": "one deterministic JSON object; no file or network I/O",
                "exit_status": {"0": "pass/help", "1": "check failed", "2": "invalid input"},
                "ignored_options": "slopes does not use valid --n/--literal/--include-data; --filtration is unavailable; filtration does not use valid --literal",
            }
        else:
            bounded_integer(args.n, "n", 0, 40)
            bounded_integer(args.literal, "literal", 0, 9)
            if args.filtration is not None:
                bounded_integer(args.filtration, "filtration", 1, 12)
                if args.command in ("coefficients", "slopes"):
                    raise ValueError("--filtration requires command all or filtration")
            output = {"schema": "report166-companion-v1", "command": args.command}
            if args.command in ("all", "coefficients"):
                coefficients = check_run_polynomials(args.n, args.literal, True)
                rows = coefficients["run_polynomials"]
                if not args.include_data:
                    coefficients.pop("run_polynomials")
                    coefficients.pop("literal_run_polynomials")
                output["coefficients"] = coefficients
            if args.command == "filtration" or (args.command == "all" and args.filtration is not None):
                k = args.filtration if args.filtration is not None else 5
                output["filtration"] = check_filtration(
                    k, args.n, rows if args.command == "all" else None,
                    args.include_data)
            if args.command in ("all", "slopes"):
                output["slopes"] = certify_slopes()
            output["passed"] = True
        status = 0
    except ValueError as error:
        output = {"passed": False, "error": str(error), "error_type": "invalid_input"}
        status = 2
    except CheckFailure as error:
        output = {"passed": False, "error": str(error), "error_type": "check_failed"}
        status = 1
    print(json.dumps(output, indent=2, sort_keys=True, ensure_ascii=True))
    return status


if __name__ == "__main__":
    sys.exit(main())
