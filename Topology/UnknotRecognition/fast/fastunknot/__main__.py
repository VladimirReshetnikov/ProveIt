"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations

import argparse
import json
import sys

from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .filters import FilterLimit, jones_obstruction
from .recognize import factored_khovanov_rank, recognize
from .scan import khovanov_rank

EXIT = {"UNKNOT": 0, "KNOTTED": 0, "UNKNOWN": 3}


def load(path: str) -> Diagram:
    data = json.load(sys.stdin if path == "-" else open(path, encoding="utf-8"))
    return Diagram.from_json(data)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="fastunknot", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("recognize", help="decide whether a knot diagram is the unknot")
    rec.add_argument("file")
    rec.add_argument("--max-objects", type=int, default=None,
                     help="ceiling on objects of the scanning complex (UNKNOWN when exceeded)")
    rec.add_argument("--seconds", type=float, default=None, help="cooperative time budget")
    rec.add_argument("--no-reduction", action="store_true")
    rec.add_argument("--no-descending", action="store_true")
    rec.add_argument("--no-alexander", action="store_true", help="disable both Alexander stages")
    rec.add_argument("--no-modular", action="store_true", help="disable only the modular Alexander stage")
    rec.add_argument("--no-jones", action="store_true")
    rec.add_argument("--no-factor", action="store_true", help="do not split visible connected sums")
    rec.add_argument("--jones-max-states", type=int, default=4096)
    rec.add_argument("--pivot", choices=("minfill", "lifo"), default="minfill")
    rec.add_argument("--algebra", choices=("bits", "sets"), default="bits")
    rec.add_argument("--tail", type=int, default=0)
    rec.add_argument("--check-d2", action="store_true", help="verify d^2=0 after every crossing")
    rec.add_argument("--output", help="write the JSON result to this file")
    kh = sub.add_parser("khovanov", help="total F2 Khovanov rank by scanning")
    kh.add_argument("file")
    kh.add_argument("--check-d2", action="store_true")
    kh.add_argument("--factor", action="store_true", help="multiply ranks over visible connected summands")
    kh.add_argument("--pivot", choices=("minfill", "lifo"), default="minfill")
    kh.add_argument("--algebra", choices=("bits", "sets"), default="bits")
    kh.add_argument("--tail", type=int, default=0)
    jo = sub.add_parser("jones", help="one-sided modular Kauffman bracket test")
    jo.add_argument("file")
    al = sub.add_parser("alexander", help="Alexander polynomial")
    al.add_argument("file")
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
    except (DiagramError, ValueError, OSError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 2
    if args.command == "recognize":
        result = recognize(diagram, use_reduction=not args.no_reduction,
                           use_descending=not args.no_descending,
                           use_alexander=not args.no_alexander, use_modular=not args.no_modular,
                           use_jones=not args.no_jones, use_factorization=not args.no_factor,
                           jones_max_states=args.jones_max_states, pivot=args.pivot,
                           algebra=args.algebra, tail=args.tail, max_objects=args.max_objects,
                           seconds=args.seconds, check_d_squared=args.check_d2).to_json()
        text = json.dumps(result, indent=1)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as handle:
                handle.write(text + "\n")
        print(text)
        return EXIT[result["status"]]
    if args.command == "khovanov":
        options = dict(check_d_squared=args.check_d2, pivot=args.pivot, algebra=args.algebra, tail=args.tail)
        result = factored_khovanov_rank(diagram, **options) if args.factor else khovanov_rank(diagram.pd, **options)
        print(json.dumps(result, indent=1))
        return 0
    if args.command == "jones":
        try:
            witness = jones_obstruction(diagram, max_states=None, max_transitions=None)
        except FilterLimit as exc:
            witness = {"skipped": str(exc)}
        print(json.dumps({"verdict": "KNOTTED" if witness else "INCONCLUSIVE", "witness": witness}, indent=1))
        return 0
    poly = alexander_polynomial(diagram)
    print(json.dumps({"alexander_polynomial": format_polynomial(poly), "coefficients": poly}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
