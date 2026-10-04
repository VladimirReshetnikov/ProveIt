"""Command line interface: python -m unknot --help."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from .grid import Grid
from .pattern import BallPattern, assess_pattern
from .recognize import recognize, verify_certificate


def load(path: str) -> Any:
    text = sys.stdin.read() if path == "-" else Path(path).read_text(encoding="utf-8")
    return json.loads(text)


def emit(value: Any, path: str | None = None) -> None:
    text = json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n"
    if path:
        Path(path).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Exact grid unknot recognition (NOT a quasipolynomial implementation).")
    sub = parser.add_subparsers(dest="command", required=True)
    search = sub.add_parser("recognize", help="exact finite monotone search")
    search.add_argument("input", help="JSON diagram path, or - for stdin")
    search.add_argument("--max-states", type=int)
    search.add_argument("--timeout", type=float, help="soft seconds limit")
    search.add_argument("--no-determinant", action="store_true")
    search.add_argument("--no-certificate", action="store_true",
                        help="omit potentially large certificate data")
    search.add_argument("--certificate", help="also save a standalone certificate")
    search.add_argument("--output", help="save result JSON instead of printing")
    verify = sub.add_parser("verify", help="replay a standalone or result-embedded certificate")
    verify.add_argument("certificate")
    verify.add_argument("--input", help="bind certificate to this diagram")
    show = sub.add_parser("show", help="print an ASCII rectangular diagram")
    show.add_argument("input")
    pattern = sub.add_parser("pattern", help="assess a boundary pattern of a known ball")
    pattern.add_argument("input")
    normal = sub.add_parser("normal", help="compressed surface dual to a simplicial cocycle")
    normal.add_argument("input")
    args = parser.parse_args()
    try:
        if args.command == "recognize":
            if args.no_certificate and args.certificate:
                parser.error("--no-certificate conflicts with --certificate")
            grid = Grid.from_json(load(args.input))
            result = recognize(grid, max_states=args.max_states, timeout=args.timeout,
                               use_determinant=not args.no_determinant,
                               include_certificate=not args.no_certificate)
            if args.certificate and "certificate" in result:
                emit(result["certificate"], args.certificate)
            if args.certificate and "certificate" not in result:
                print("no certificate written: result is UNKNOWN; any existing file is unchanged",
                      file=sys.stderr)
            emit(result, args.output)
            return 0 if result["verdict"] != "UNKNOWN" else 2
        if args.command == "verify":
            value = load(args.certificate)
            if isinstance(value, dict) and "certificate" in value:
                value = value["certificate"]
            expected = Grid.from_json(load(args.input)) if args.input else None
            emit(verify_certificate(value, expected))
            return 0
        if args.command == "show":
            grid = Grid.from_json(load(args.input))
            print(grid.ascii())
            print(f"\n{grid.size} rows; {grid.crossing_count()} crossings; "
                  f"{grid.components()} component(s). Vertical strands pass over.")
            return 0
        if args.command == "normal":
            from .normal import from_cocycle
            from .cohomology import rational_cohomology_basis
            value = load(args.input)
            if not isinstance(value, dict) or not isinstance(value.get("tetrahedra"), list):
                raise ValueError("normal input requires a tetrahedra array")
            tetrahedra = value["tetrahedra"]
            data = {"manifoldness_checked": False, "connected_component_extraction": False}
            if "cocycle" not in value:
                basis = rational_cohomology_basis(tetrahedra)
                data["first_betti_number"] = len(basis)
                cocycle = basis[0] if basis else {}
            else:
                entries = value["cocycle"]
                if not isinstance(entries, list) or any(not isinstance(e, list) or len(e) != 3
                                                        for e in entries):
                    raise ValueError("cocycle must contain [u,v,integer] triples")
                if any(type(x) is not int for e in entries for x in e):
                    raise ValueError("cocycle entries must be integers")
                cocycle = {(u, v): c for u, v, c in entries}
                if len(cocycle) != len(entries):
                    raise ValueError("duplicate cocycle edge")
            coordinates = from_cocycle(tetrahedra, cocycle)
            data["cocycle"] = [[u, v, c] for (u, v), c in sorted(cocycle.items())]
            data["coordinates"] = coordinates.coordinates
            data["face_matching"] = coordinates.check_matching()
            emit(data)
            return 0
        emit(assess_pattern(BallPattern.from_json(load(args.input))))
        return 0
    except (ValueError, TypeError, OSError, ArithmeticError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("interrupted: no new conclusion", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
