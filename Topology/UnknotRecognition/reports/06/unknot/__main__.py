"""Command line interface. No requested quasipolynomial bound is claimed."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any

from .diagram import Diagram
from .khovanov import recognize, verify_report
from .limits import Limits
from .patterns import BallPattern, classify_pattern


def read_json(path: str) -> Any:
    text = sys.stdin.read() if path == "-" else Path(path).read_text(encoding="utf-8")
    return json.loads(text)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact exponential unknot recognition; NOT a quasipolynomial implementation.")
    commands = parser.add_subparsers(dest="command", required=True)
    run = commands.add_parser("recognize", help="Compute reduced Khovanov homology over F_2")
    run.add_argument("input", help="JSON input path, or - for stdin")
    run.add_argument("--check-d2", action="store_true", help="Exhaustively check d*d=0")
    verify = commands.add_parser("verify", help="Recompute an algebraic report; not a short certificate")
    verify.add_argument("input", help="JSON report path, or - for stdin")
    pattern = commands.add_parser("pattern", help="Test a pattern on a known 3-ball boundary")
    pattern.add_argument("input", help="JSON pattern path, or - for stdin")
    for command in (run, verify):
        command.add_argument("--max-states", type=int, default=None)
        command.add_argument("--max-generators", type=int, default=None)
        command.add_argument("--seconds", type=float, default=None,
                             help="Cooperative budget, not a hard real-time deadline")
    arguments = parser.parse_args(argv)
    try:
        value = read_json(arguments.input)
        if arguments.command == "pattern":
            result = classify_pattern(BallPattern.from_json(value))
            exit_code = 0
        else:
            limits = Limits(arguments.max_states, arguments.max_generators, arguments.seconds)
            if arguments.command == "recognize":
                result = recognize(Diagram.from_json(value), limits=limits,
                                   check_d_squared=arguments.check_d2)
                exit_code = 3 if result["status"] == "unknown" else 0
            else:
                if not isinstance(value, dict):
                    raise ValueError("A report must be a JSON object")
                valid = verify_report(value, limits=limits)
                result = {"report_verified": valid,
                          "method": "recomputation, including an exhaustive d^2 check",
                          "note": "false can also mean the verification budget was exhausted"}
                exit_code = 0 if valid else 1
        print(json.dumps(result, indent=2, allow_nan=False))
        return exit_code
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({"status": "error", "reason": str(error)}), file=sys.stderr)
        return 2
    except ArithmeticError as error:
        print(json.dumps({"status": "error", "reason": "Arithmetic invariant or size failure: "
                          + str(error)}), file=sys.stderr)
        return 2
    except MemoryError:
        print('{"status":"unknown","reason":"Memory allocation failed"}', file=sys.stderr)
        return 3
    except KeyboardInterrupt:
        print('{"status":"unknown","reason":"Interrupted by user"}', file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
