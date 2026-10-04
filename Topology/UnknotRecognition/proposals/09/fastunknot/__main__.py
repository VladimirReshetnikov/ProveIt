"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations

import argparse
import json
import sys

from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .recognize import recognize
from .scan import khovanov_rank, ScanLimit
from .jones import jones_residue, JonesLimit

EXIT = {"UNKNOT": 0, "KNOTTED": 0, "UNKNOWN": 3}


def load(path: str) -> Diagram:
    if path == "-":
        data = json.load(sys.stdin)
    else:
        with open(path, encoding="utf-8") as handle:
            data = json.load(handle)
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
    rec.add_argument("--no-alexander", action="store_true")
    rec.add_argument("--no-determinant", action="store_true")
    rec.add_argument("--no-jones", action="store_true")
    rec.add_argument("--no-factors", action="store_true")
    rec.add_argument("--max-jones-states", type=int, default=8192)
    rec.add_argument("--max-jones-transitions", type=int, default=250000)
    rec.add_argument("--check-d2", action="store_true", help="verify d^2=0 after every crossing")
    rec.add_argument("--output", help="write the JSON result to this file")
    kh = sub.add_parser("khovanov", help="total F2 Khovanov rank by scanning")
    kh.add_argument("file")
    kh.add_argument("--check-d2", action="store_true")
    kh.add_argument("--no-factors", action="store_true")
    kh.add_argument("--seconds", type=float)
    kh.add_argument("--max-objects", type=int)
    jo = sub.add_parser("jones", help="exact modular Jones evaluation; equality is inconclusive")
    jo.add_argument("file")
    jo.add_argument("--max-states", type=int, default=8192)
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
                           use_alexander=not args.no_alexander,
                           use_determinant=not args.no_determinant, use_jones=not args.no_jones,
                           use_factors=not args.no_factors, max_jones_states=args.max_jones_states,
                           max_jones_transitions=args.max_jones_transitions, max_objects=args.max_objects,
                           seconds=args.seconds, check_d_squared=args.check_d2).to_json()
        text = json.dumps(result, indent=1)
        if args.output:
            with open(args.output, "w", encoding="utf-8") as handle:
                handle.write(text + "\n")
        print(text)
        return EXIT[result["status"]]
    if args.command == "khovanov":
        print(json.dumps(khovanov_rank(diagram.pd, check_d_squared=args.check_d2,
                                       factor=not args.no_factors, seconds=args.seconds,
                                       max_objects=args.max_objects), indent=1))
        return 0
    if args.command == "jones":
        print(json.dumps(jones_residue(diagram, max_states=args.max_states), indent=1))
        return 0
    poly = alexander_polynomial(diagram)
    print(json.dumps({"alexander_polynomial": format_polynomial(poly), "coefficients": poly}))
    return 0


def entrypoint(argv: list[str] | None = None) -> int:
    """Apply identical error/limit handling for python -m and console scripts."""
    try:
        return main(argv)
    except (ScanLimit, JonesLimit, MemoryError) as exc:
        print(json.dumps({"status": "UNKNOWN", "reason": str(exc)}))
        return 3
    except (ValueError, OSError) as exc:
        print(f"invalid input or option: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(entrypoint())
