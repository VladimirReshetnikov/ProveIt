"""Command line: python -m fastunknot {recognize,khovanov,jones,alexander} FILE."""
from __future__ import annotations
import argparse
import json
import sys
from time import monotonic
from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .jones import normalized_bracket_mod
from .recognize import recognize
from .scan import khovanov_rank, ScanLimit

EXIT = {"UNKNOT": 0, "KNOTTED": 0, "UNKNOWN": 3}


def load(path: str) -> Diagram:
    if path == "-":
        return Diagram.from_json(json.load(sys.stdin))
    with open(path, encoding="utf-8") as handle:
        return Diagram.from_json(json.load(handle))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="fastunknot", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("recognize", help="exact verdict, or UNKNOWN on a resource ceiling")
    rec.add_argument("file")
    rec.add_argument("--max-objects", type=int)
    rec.add_argument("--seconds", type=float, help="cooperative time budget")
    for flag in ("reduction", "descending", "alexander", "jones", "decompose"):
        rec.add_argument("--no-" + flag, action="store_true")
    rec.add_argument("--jones-max-states", type=int, default=4096)
    rec.add_argument("--tail-crossings", type=int, default=2)
    rec.add_argument("--check-d2", action="store_true")
    rec.add_argument("--output")
    kh = sub.add_parser("khovanov", help="total F2 Khovanov rank (filters not used)")
    kh.add_argument("file")
    kh.add_argument("--check-d2", action="store_true")
    kh.add_argument("--max-objects", type=int)
    kh.add_argument("--seconds", type=float)
    kh.add_argument("--tail-crossings", type=int, default=2)
    kh.add_argument("--no-decompose", action="store_true")
    jo = sub.add_parser("jones", help="exact normalized bracket at A=2 modulo 1000000007")
    jo.add_argument("file")
    jo.add_argument("--max-states", type=int, default=4096)
    jo.add_argument("--seconds", type=float)
    al = sub.add_parser("alexander", help="exact Alexander polynomial")
    al.add_argument("file")
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
        if args.command == "recognize":
            result = recognize(diagram, use_reduction=not args.no_reduction,
                               use_descending=not args.no_descending,
                               use_alexander=not args.no_alexander,
                               use_jones=not args.no_jones, decompose=not args.no_decompose,
                               jones_max_states=args.jones_max_states,
                               tail_crossings=args.tail_crossings,
                               max_objects=args.max_objects, seconds=args.seconds,
                               check_d_squared=args.check_d2).to_json()
            text = json.dumps(result, indent=2)
            if args.output:
                with open(args.output, "w", encoding="utf-8") as handle:
                    handle.write(text + "\n")
            print(text)
            return EXIT[result["status"]]
        if args.command == "khovanov":
            result = khovanov_rank(diagram.pd, check_d_squared=args.check_d2,
                                    max_objects=args.max_objects, seconds=args.seconds,
                                    tail_crossings=args.tail_crossings,
                                    decompose=not args.no_decompose)
        elif args.command == "jones":
            if args.seconds is not None:
                from math import isfinite
                if not isfinite(args.seconds) or args.seconds < 0:
                    raise ValueError("seconds must be finite and nonnegative")
            result = normalized_bracket_mod(diagram, max_states=args.max_states,
                deadline=None if args.seconds is None else monotonic() + args.seconds)
        else:
            poly = alexander_polynomial(diagram)
            result = {"alexander_polynomial": format_polynomial(poly), "coefficients": poly}
        print(json.dumps(result, indent=2))
        return 3 if result.get("completed") is False else 0
    except (DiagramError, ValueError, TypeError, KeyError, OSError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 2
    except (ScanLimit, MemoryError) as exc:
        print(json.dumps({"status": "UNKNOWN", "reason": str(exc) or "memory allocation failed"}))
        return 3
    except ArithmeticError as exc:
        print(json.dumps({"status": "ERROR", "reason": str(exc)}))
        return 4


if __name__ == "__main__":
    sys.exit(main())
