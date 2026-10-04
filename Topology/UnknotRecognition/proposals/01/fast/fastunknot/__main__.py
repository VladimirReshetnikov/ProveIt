"""Command line for exact unknot recognition and reproducible experiments."""
from __future__ import annotations

import argparse
import json
import sys

from .alexander import alexander_polynomial, format_polynomial
from .diagram import Diagram, DiagramError
from .jones import JonesLimit, jones_evaluations
from .recognize import recognize, verify_rejection
from .scan import ScanLimit, khovanov_rank

EXIT = {"UNKNOT": 0, "KNOTTED": 0, "UNKNOWN": 3}


def load(path: str) -> Diagram:
    if path == "-":
        return Diagram.from_json(json.load(sys.stdin))
    with open(path, encoding="utf-8") as handle:
        return Diagram.from_json(json.load(handle))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="fastunknot", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("recognize", help="decide whether a knot diagram is the unknot")
    rec.add_argument("file")
    rec.add_argument("--max-objects", type=int, default=None,
                     help="ceiling on a scanning factor's live objects")
    rec.add_argument("--seconds", type=float, default=None, help="cooperative total time budget")
    rec.add_argument("--max-jones-states", type=int, default=4096,
                     help="optional filter's state cap; exhaustion falls through, 0 disables")
    for name in ("reduction", "descending", "alexander", "modular", "jones", "factors"):
        rec.add_argument("--no-" + name, action="store_true")
    rec.add_argument("--pivot", choices=("markowitz", "lifo"), default="markowitz")
    rec.add_argument("--check-d2", action="store_true", help="verify d^2=0 during Khovanov scanning")
    rec.add_argument("--output", help="also write the JSON result to a file")
    kh = sub.add_parser("khovanov", help="total F2 Khovanov ranks, without R1/R2 preprocessing")
    kh.add_argument("file")
    kh.add_argument("--check-d2", action="store_true")
    kh.add_argument("--no-factors", action="store_true")
    kh.add_argument("--pivot", choices=("markowitz", "lifo"), default="markowitz")
    kh.add_argument("--seconds", type=float)
    kh.add_argument("--max-objects", type=int)
    al = sub.add_parser("alexander", help="full exact Alexander polynomial")
    al.add_argument("file")
    jo = sub.add_parser("jones-evaluate", help="exact finite-field Jones evaluations, not a full polynomial")
    jo.add_argument("file")
    jo.add_argument("--max-states", type=int)
    ve = sub.add_parser("verify", help="replay and verify a modular rejection certificate")
    ve.add_argument("file")
    ve.add_argument("result")
    args = parser.parse_args(argv)
    try:
        diagram = load(args.file)
        if args.command == "recognize":
            result = recognize(
                diagram, use_reduction=not args.no_reduction,
                use_descending=not args.no_descending, use_alexander=not args.no_alexander,
                use_modular=not args.no_modular, use_jones=not args.no_jones,
                factor_connected=not args.no_factors, max_jones_states=args.max_jones_states,
                max_objects=args.max_objects, seconds=args.seconds,
                check_d_squared=args.check_d2, pivot=args.pivot).to_json()
            text = json.dumps(result, indent=2)
            if args.output:
                with open(args.output, "w", encoding="utf-8") as handle:
                    handle.write(text + "\n")
            print(text)
            return EXIT[result["status"]]
        if args.command == "khovanov":
            result = khovanov_rank(diagram.pd, check_d_squared=args.check_d2,
                                   factor_connected=not args.no_factors, pivot=args.pivot,
                                   seconds=args.seconds, max_objects=args.max_objects)
        elif args.command == "jones-evaluate":
            result = jones_evaluations(diagram, max_states=args.max_states)
            result['certifies_knotted'] = any(x != 1 for x in result['normalized'])
        elif args.command == "verify":
            with open(args.result, encoding="utf-8") as handle:
                result = json.load(handle)
            verified = verify_rejection(diagram, result)
            print(json.dumps({"verified": verified, "scope": "modular rejection and R1/R2 trace"}))
            return 0 if verified else 1
        else:
            poly = alexander_polynomial(diagram)
            result = {"alexander_polynomial": format_polynomial(poly), "coefficients": poly}
        print(json.dumps(result, indent=2))
        return 0
    except (ScanLimit, JonesLimit, MemoryError) as exc:
        print(json.dumps({"status": "UNKNOWN", "reason": str(exc) or "memory allocation failed"}))
        return 3
    except (DiagramError, TypeError, ValueError, OSError) as exc:
        print(f"invalid input or option: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
