"""Command line: python -m fastunknot recognize FILE [options]."""
from __future__ import annotations

import argparse
import json
import sys

from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .filters import FilterLimit, jones_evaluation
from .recognize import recognize
from .scan import ScanLimit, khovanov_rank

EXIT = {"UNKNOT": 0, "KNOTTED": 0, "UNKNOWN": 3}


def load(path: str) -> Diagram:
    if path == "-":
        return Diagram.from_json(json.load(sys.stdin))
    with open(path, encoding="utf-8") as stream:
        return Diagram.from_json(json.load(stream))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="fastunknot", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("recognize", help="decide whether a knot diagram is the unknot")
    rec.add_argument("file")
    rec.add_argument("--max-objects", type=int, default=None)
    rec.add_argument("--seconds", type=float, default=None, help="cooperative time budget")
    rec.add_argument("--no-reduction", action="store_true")
    rec.add_argument("--no-descending", action="store_true")
    rec.add_argument("--no-alexander", action="store_true", help="skip the full symbolic Alexander polynomial")
    rec.add_argument("--no-filters", action="store_true", help="skip both new modular prefilters")
    rec.add_argument("--jones-max-states", type=int, default=50_000)
    rec.add_argument("--jones-max-transitions", type=int, default=1_000_000)
    rec.add_argument("--check-d2", action="store_true")
    rec.add_argument("--output")
    kh = sub.add_parser("khovanov", help="full F2 Khovanov rank, bypassing all preprocessing")
    kh.add_argument("file")
    kh.add_argument("--check-d2", action="store_true")
    kh.add_argument("--max-objects", type=int, default=None)
    kh.add_argument("--seconds", type=float, default=None)
    al = sub.add_parser("alexander", help="full Alexander polynomial")
    al.add_argument("file")
    jo = sub.add_parser("jones", help="one-sided modular Jones evaluation, not an unknot test")
    jo.add_argument("file")
    jo.add_argument("--max-states", type=int, default=50_000)
    jo.add_argument("--max-transitions", type=int, default=1_000_000)
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
        if args.command == "recognize":
            result = recognize(diagram, use_reduction=not args.no_reduction,
                               use_descending=not args.no_descending,
                               use_alexander=not args.no_alexander, use_filters=not args.no_filters,
                               max_objects=args.max_objects, seconds=args.seconds,
                               check_d_squared=args.check_d2, jones_max_states=args.jones_max_states,
                               jones_max_transitions=args.jones_max_transitions).to_json()
            text = json.dumps(result, indent=2)
            if args.output:
                with open(args.output, "w", encoding="utf-8") as stream:
                    stream.write(text + "\n")
            print(text)
            return EXIT[result["status"]]
        if args.command == "khovanov":
            result = khovanov_rank(diagram.pd, check_d_squared=args.check_d2,
                                  max_objects=args.max_objects, seconds=args.seconds)
        elif args.command == "jones":
            result = jones_evaluation(diagram, max_states=args.max_states,
                                      max_transitions=args.max_transitions)
        else:
            poly = alexander_polynomial(diagram)
            result = {"alexander_polynomial": format_polynomial(poly), "coefficients": poly}
        print(json.dumps(result, indent=2))
        return 0
    except (DiagramError, ValueError, TypeError, KeyError, OSError) as exc:
        print(f"invalid input or options: {exc}", file=sys.stderr)
        return 2
    except (ScanLimit, FilterLimit, MemoryError) as exc:
        print(json.dumps({"status": "UNKNOWN", "reason": str(exc) or "memory allocation failed"}))
        return 3


if __name__ == "__main__":
    sys.exit(main())
