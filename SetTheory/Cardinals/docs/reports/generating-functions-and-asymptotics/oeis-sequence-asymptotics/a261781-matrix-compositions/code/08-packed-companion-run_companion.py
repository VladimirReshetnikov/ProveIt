#!/usr/bin/env python3
"""Offline, no-clobber command-line entry point; Python standard library only."""
import argparse
from fractions import Fraction
import re
import sys
import packed_matrix as pm


def rational(text):
    if len(text) > 157 or not re.fullmatch(r"[+-]?[0-9]{1,77}(?:/[0-9]{1,77})?", text):
        raise argparse.ArgumentTypeError("Use an integer or p/q with at most 77 digits per part")
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError("Invalid rational or zero denominator") from exc


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    count = subs.add_parser("count", help="one exact count; n=0..800 (both/inclusion: 0..100)")
    count.add_argument("n", type=int)
    count.add_argument("--method", choices=("stirling", "inclusion", "both"), default="both")
    marked = subs.add_parser("marked", help="exact J,K polynomial; transform n=0..8, enumeration 0..4")
    marked.add_argument("n", type=int)
    marked.add_argument("--method", choices=("transform", "enumeration", "both"), default="both")
    coefficient = subs.add_parser("coefficients", help="C0-C3 at exact rational q,R; both routes checked")
    coefficient.add_argument("--q", required=True, type=rational)
    coefficient.add_argument("--R", required=True, type=rational)
    diagnostics = subs.add_parser("diagnostics", help="uncertified rounded Decimal diagnostics")
    diagnostics.add_argument("n", type=int, nargs="+", help="1..800, 1 to 12 distinct indices")
    diagnostics.add_argument("--digits", type=int, default=60, help="significant digits, 30..160")
    diagnostics.add_argument("--output", help="optional NEW output directory; parent must exist")
    generate = subs.add_parser("generate", help="reproduce all supplied JSON files in a NEW directory")
    generate.add_argument("--output", required=True, help="must not exist; its parent must exist")
    generate.add_argument("--digits", type=int, default=60)
    args = parser.parse_args(argv)
    try:
        if args.command == "count":
            if args.method == "stirling":
                value = pm.count_stirling(args.n)
            elif args.method == "inclusion":
                value = pm.count_inclusion(args.n)
            else:
                value = pm.count_inclusion(args.n)
                if value != pm.count_stirling(args.n):
                    raise ArithmeticError("Count routes disagree")
            result = {"n": args.n, "method": args.method, "count": pm.integer_decimal(value), "arithmetic": "exact integers"}
        elif args.command == "marked":
            if args.method == "transform":
                value = pm.marked_transform(args.n)
            elif args.method == "enumeration":
                value = pm.marked_enumeration(args.n)
            else:
                value = pm.marked_enumeration(args.n)
                if value != pm.marked_transform(args.n):
                    raise ArithmeticError("Marked routes disagree")
            result = pm.marked_record(args.n, value)
            result["method"] = args.method
        elif args.command == "coefficients":
            value = pm.rational_coefficients(args.q, args.R)
            if value != pm.rational_coefficients(args.q, args.R, "frozen"):
                raise ArithmeticError("Coefficient routes disagree")
            result = {"q": str(args.q), "R": str(args.R), "C0_C3": [str(c) for c in value],
                      "arithmetic": "exact rational specialization; not the transcendental saddle values"}
        elif args.command == "diagnostics":
            if args.output:
                from pathlib import Path
                output = Path(args.output)
                if output.exists() or output.is_symlink():
                    raise FileExistsError("Output already exists; choose a new directory")
                if not output.parent.is_dir():
                    raise FileNotFoundError("Output parent directory must already exist")
            result = pm.decimal_diagnostics(args.n, args.digits)
            if args.output:
                pm.write_bundle(args.output, {"diagnostics_uncertified.json": result})
        else:
            # Preflight before potentially expensive generation. Exclusive mkdir
            # in write_bundle still enforces no-clobber if the path appears later.
            from pathlib import Path
            output = Path(args.output)
            if output.exists() or output.is_symlink():
                raise FileExistsError("Output already exists; choose a new directory")
            if not output.parent.is_dir():
                raise FileNotFoundError("Output parent directory must already exist")
            pm.bounded_int(args.digits, "digits", pm.MIN_DIGITS, pm.MAX_DIGITS)
            payloads = pm.generated_payloads(args.digits)
            pm.write_bundle(output, payloads)
            result = {"status": "created", "output": str(output), "files": sorted(payloads) + ["manifest.json"]}
    except (ValueError, TypeError, ArithmeticError, OSError) as exc:
        parser.error(str(exc))
    print(pm.json_text(result), end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
