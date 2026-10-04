"""CLI. An inconclusive resource-limited computation exits 2, never answers NO."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .diagrams import InvalidDiagram, PlanarDiagram
from .hierarchy_bounds import HierarchyBound
from .khovanov import Limits, ResourceLimit, recognize
from .patterns import BallPattern, InvalidPattern, decide_ball_pattern, verify_violation


def positive(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("A positive integer is required")
    return parsed


def read_json(path: str) -> object:
    if path == "-":
        return json.load(sys.stdin)
    return json.loads(Path(path).read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=(
        "Exact reference recognizer and hierarchy subroutines. "
        "NOT a quasi-polynomial unknot recognition implementation."))
    sub = parser.add_subparsers(dest="command", required=True)
    rec = sub.add_parser("recognize", help="Recognize a classical knot; exponential worst case")
    rec.add_argument("input", help="JSON PD/braid file, or - for stdin")
    rec.add_argument("--no-filter", action="store_true", help="Always compute reduced Kh")
    rec.add_argument("--check-d2", action="store_true", help="Also verify d squared is zero")
    rec.add_argument("--basepoint", type=int, help="Original PD edge label")
    rec.add_argument("--max-states", type=positive, default=65536)
    rec.add_argument("--max-generators", type=positive, default=200000)
    rec.add_argument("--max-matrix-bits", type=positive, default=128000000)
    rec.add_argument("--unlimited", action="store_true",
                     help="Remove all ceilings: exact decider, potentially very expensive")
    pattern = sub.add_parser("pattern", help="Test a pattern on an already KNOWN 3-ball")
    pattern.add_argument("input")
    verify = sub.add_parser("verify-pattern", help="Check a negative pattern witness")
    verify.add_argument("input")
    verify.add_argument("certificate")
    audit = sub.add_parser("bound", help="Conditional arithmetic only, not a topology proof")
    audit.add_argument("digit_bound", type=int)
    audit.add_argument("depth_bound", type=positive)
    args = parser.parse_args(argv)
    try:
        if args.command == "recognize":
            pd = PlanarDiagram.from_json(read_json(args.input))
            limits = (Limits(None, None, None) if args.unlimited else
                      Limits(args.max_states, args.max_generators, args.max_matrix_bits))
            result = recognize(pd, limits, args.check_d2, not args.no_filter, args.basepoint)
        elif args.command == "pattern":
            result = decide_ball_pattern(BallPattern.from_json(read_json(args.input)))
        elif args.command == "verify-pattern":
            pattern = BallPattern.from_json(read_json(args.input))
            witness = read_json(args.certificate)
            if isinstance(witness, dict) and "certificate" in witness:
                witness = witness["certificate"]
            accepted = verify_violation(pattern, witness)
            result = {"accepted": accepted, "ambient_manifold_assumption": "known-3-ball"}
            print(json.dumps(result, indent=2))
            return 0 if accepted else 3
        else:
            bound = HierarchyBound(args.digit_bound, args.depth_bound)
            result = {"conditional_only": True, "phase_bound": bound.phase_bound(),
                      "visit_bound": bound.visit_bound(),
                      "establishes_unknot_runtime": False}
        print(json.dumps(result, indent=2))
        return 0
    except ResourceLimit as exc:
        print(json.dumps({"status": "unknown", "is_unknot": None, "reason": str(exc),
                          "quasipolynomial_guarantee": False}, indent=2))
        return 2
    except (InvalidDiagram, InvalidPattern, ValueError, OSError) as exc:
        print(json.dumps({"status": "invalid-input", "is_unknot": None,
                          "reason": str(exc)}, indent=2))
        return 3
    except ArithmeticError as exc:
        print(json.dumps({"status": "internal-error", "is_unknot": None,
                          "reason": str(exc)}, indent=2))
        return 4


if __name__ == "__main__":
    raise SystemExit(main())
