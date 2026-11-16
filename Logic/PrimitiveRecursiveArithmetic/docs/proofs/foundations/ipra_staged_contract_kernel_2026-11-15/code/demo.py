from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from staged_contracts import (
    StaticNode,
    bounded_demand_closure,
    compile_static_schedule,
    cubic_bisection,
    fraction_json,
    least_viable_path,
)


def main() -> None:
    root = Path(__file__).resolve().parents[1]

    def demand_step(q):
        input_precision, branch_horizon, final_precision = q
        return (
            max(input_precision, min(8, final_precision + 2)),
            max(branch_horizon, min(8, input_precision + 1)),
            max(final_precision, 4),
        )

    fixed, demand_trace = bounded_demand_closure((0, 0, 0), demand_step, (8, 8, 8))

    graph = [
        StaticNode("decode", ("input",), "Decoded(x)", payload={"arity": 2}),
        StaticNode("demand", ("decode",), "ClosedDemand(q)", payload={"arity": 3}),
        StaticNode("trace", ("demand",), "TraceInvariant(t,s)", local_rule="qf-induction"),
        StaticNode("observe", ("trace",), "StableOutput(y)"),
    ]
    proofs = compile_static_schedule(graph, {"input"})

    levels = [[0, 1, 2], [10, 11, 12], [20, 21]]
    edges = [lambda a, b: b == a + 10, lambda a, b: (a, b) in {(10, 20), (12, 21)}]
    path = least_viable_path(levels, edges)

    bracket, bracket_trace = cubic_bisection(Fraction(7, 3), 10)
    evidence = {
        "demand_closure": {
            "fixed_point": list(fixed),
            "trace": [list(q) for q in demand_trace],
        },
        "proof_schedule": {
            name: {
                "rule": proof.rule,
                "conclusion": proof.conclusion,
                "proof_nodes": proof.node_count(),
            }
            for name, proof in proofs.items()
        },
        "viable_path": path,
        "cubic_bisection": {
            "x": fraction_json(bracket.x),
            "steps": 10,
            "lo": fraction_json(bracket.lo),
            "hi": fraction_json(bracket.hi),
            "width": fraction_json(bracket.width),
            "all_brackets_valid": all(b.valid() for b in bracket_trace),
        },
    }
    out = root / "examples" / "demo_evidence.json"
    out.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
