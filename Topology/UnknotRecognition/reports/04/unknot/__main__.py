"""Command-line interface. Run `python -m unknot --help`."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .diagram import Diagram, DiagramError
from .khovanov import InternalInvariantError, Limits, recognize
from .pattern import PatternError, classify_ball_pattern


def load_json(filename: str):
    if filename == "-":
        return json.load(sys.stdin)
    return json.loads(Path(filename).read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact EXPONENTIAL unknot recognition and a ball-pattern component. "
                    "This is NOT an n^O(log n) implementation.")
    sub = parser.add_subparsers(dest="command", required=True)
    solve = sub.add_parser("recognize", help="reduced Khovanov homology over F2")
    solve.add_argument("input", help="JSON file, or - for standard input")
    solve.add_argument("--max-states", type=int)
    solve.add_argument("--max-generators", type=int)
    solve.add_argument("--seconds", type=float)
    solve.add_argument("--verify-d2", action="store_true")
    convert = sub.add_parser("normalize", help="validate and output normalized PD")
    convert.add_argument("input")
    pattern = sub.add_parser("pattern", help="classify a pattern on an ALREADY KNOWN ball")
    pattern.add_argument("input")
    args = parser.parse_args(argv)
    try:
        value = load_json(args.input)
        if args.command == "pattern":
            if not isinstance(value, dict) or "vertices" not in value:
                raise PatternError("pattern input must be an object containing vertices")
            if set(value) - {"vertices", "circles", "name", "description"}:
                raise PatternError("unexpected pattern keys")
            answer = classify_ball_pattern(value["vertices"], value.get("circles", 0))
            print(json.dumps(answer.to_json(), indent=2))
            return 0
        diagram = Diagram.from_json(value)
        if args.command == "normalize":
            print(json.dumps(diagram.to_json(), indent=2))
            return 0
        limits = Limits(args.max_states, args.max_generators, args.seconds)
        answer = recognize(diagram, limits, verify_d2=args.verify_d2)
        print(json.dumps(answer.to_json(), indent=2))
        return 3 if answer.status == "UNKNOWN" else 0
    except (DiagramError, PatternError, ValueError, OSError, TypeError) as exc:
        print(json.dumps({"status": "INVALID_INPUT", "reason": str(exc)}), file=sys.stderr)
        return 2
    except InternalInvariantError as exc:
        print(json.dumps({"status": "INTERNAL_ERROR", "reason": str(exc)}), file=sys.stderr)
        return 4
    except (KeyboardInterrupt, MemoryError) as exc:
        print(json.dumps({"status": "UNKNOWN", "reason": type(exc).__name__}))
        return 3


if __name__ == "__main__":
    raise SystemExit(main())
