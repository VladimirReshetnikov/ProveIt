"""JSON command line interface. Invalid/limited inputs are never knot verdicts."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from .diagram import read_diagram
from .normal import SimplicialTriangulation
from .pattern import SphericalPattern
from .reduction import verify_reduction_trace
from .solver import recognize


def _load(path: str) -> object:
    if path == "-":
        return json.load(sys.stdin)
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _emit(result: dict, output: str | None) -> None:
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if output:
        Path(output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=(
        "Exact unknot recognition (exponential baseline) and partial hierarchy kernels. "
        "NOT an implementation with a quasipolynomial worst-case guarantee."))
    commands = parser.add_subparsers(dest="command", required=True)
    rec = commands.add_parser("recognize", help="Complete exact recognizer; optional caps yield UNKNOWN")
    rec.add_argument("input", help="JSON file, or - for stdin")
    rec.add_argument("--no-reduce", action="store_true")
    rec.add_argument("--no-determinant", action="store_true")
    rec.add_argument("--max-resolutions", type=int)
    rec.add_argument("--max-basis", type=int)
    rec.add_argument("--check-d2", action="store_true", help="Exhaustively verify d squared equals zero")
    rec.add_argument("--output")
    pat = commands.add_parser("pattern", help="Essential boundary pattern on a KNOWN 3-ball")
    pat.add_argument("input")
    pat.add_argument("--output")
    normal = commands.add_parser("normal", help="Cocycle basis and compressed dual normal coordinates")
    normal.add_argument("input")
    normal.add_argument("--output")
    verify = commands.add_parser("verify-reductions", help="Replay the local-move trace in a result JSON")
    verify.add_argument("input")
    verify.add_argument("result")
    verify.add_argument("--output")
    args = parser.parse_args(argv)
    try:
        data = _load(args.input)
        if args.command == "recognize":
            result = recognize(read_diagram(data), reduce=not args.no_reduce,
                               determinant=not args.no_determinant,
                               max_resolutions=args.max_resolutions, max_basis=args.max_basis,
                               check_d_squared=args.check_d2)
        elif args.command == "pattern":
            if not isinstance(data, dict) or "rotations" not in data:
                raise ValueError("Pattern JSON requires 'rotations' and optional 'circle_components'.")
            pattern = SphericalPattern(data["rotations"], data.get("circle_components", 0))
            verdict = pattern.classify()
            result = verdict.to_json()
            if not verdict.essential:
                result["negative_witness_verified"] = pattern.verify_witness(verdict)
        elif args.command == "normal":
            if not isinstance(data, dict) or "tetrahedra" not in data:
                raise ValueError("Normal-surface JSON requires 'tetrahedra'.")
            triangulation = SimplicialTriangulation(data["tetrahedra"])
            basis = triangulation.cocycle_basis()
            result = {"scope": "ordinary simplicial 3-manifold; no hierarchy construction",
                      "tetrahedra": triangulation.tetrahedra, "edges": triangulation.edges,
                      "first_betti_number": len(basis),
                      "basis_kind": "Q-basis represented by integral cocycles; not a Z-lattice basis",
                      "surfaces": []}
            for cocycle in basis:
                coords = triangulation.normal_from_cocycle(cocycle)
                result["surfaces"].append({"cocycle": cocycle, "normal_coordinates": coords,
                                           "summary": triangulation.normal_summary(coords)})
        else:
            saved = _load(args.result)
            if not isinstance(saved, dict) or "reduction_trace" not in saved:
                raise ValueError("The saved result must contain 'reduction_trace'.")
            final = verify_reduction_trace(read_diagram(data), saved["reduction_trace"])
            result = {"trace_valid": True, "final_diagram": final.to_json(),
                      "proves_unknot": final.n == 0,
                      "scope": "local reduction trace only, not other fields of the saved result"}
        _emit(result, args.output)
        return 3 if result.get("status") == "UNKNOWN" else 0
    except (ValueError, TypeError, OSError, KeyError, OverflowError) as exc:
        _emit({"error": "invalid input or I/O failure", "message": str(exc)}, None)
        return 2
    except MemoryError:
        _emit({"status": "UNKNOWN", "is_unknot": None,
               "error": "out of memory", "quasipolynomial_guarantee": False}, None)
        return 3
    except ArithmeticError as exc:
        _emit({"error": "internal consistency check failed", "message": str(exc)}, None)
        return 4


if __name__ == "__main__":
    raise SystemExit(main())
