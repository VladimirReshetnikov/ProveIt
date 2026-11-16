"""Regenerate the JSON fixtures shipped with the FINER-iPRA artifact."""
from __future__ import annotations

import json
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path
from typing import Any

from finer_reference import (
    TreeEdge,
    backward_viability,
    cubic_bisection,
    monotone_demand_closure,
    spanning_tree_distances,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "examples"


def frac(q: Fraction) -> dict[str, int]:
    return {"numerator": q.numerator, "denominator": q.denominator}


def write(name: str, value: Any) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def demand_example() -> None:
    caps = (4, 5, 3)

    def transformer(x: tuple[int, ...]) -> tuple[int, ...]:
        a, b, c = x
        return min(4, b), min(5, c + 2), min(3, a + 1)

    cert = monotone_demand_closure(caps, transformer)
    write(
        "cyclic_demand.json",
        {
            "capacities": list(cert.capacities),
            "trace": [list(x) for x in cert.trace],
            "closure": list(cert.closure),
            "stabilized_at": cert.stabilized_at,
            "transformer": "F(a,b,c)=(min(4,b),min(5,c+2),min(3,a+1))",
        },
    )


def viability_example() -> None:
    layers = [[0, 1], [0, 1, 2], [0, 1, 2, 3]]
    edge = lambda _i, x, y: y in {x, x + 1}
    accept = lambda x: x == 3
    cert = backward_viability(layers, edge, accept)
    write(
        "relational_path.json",
        {
            "layers": [list(layer) for layer in cert.layers],
            "viable": [sorted(layer) for layer in cert.viable],
            "least_path": list(cert.path) if cert.path is not None else None,
            "edge": "y=x or y=x+1",
            "accept": "final=3",
        },
    )


def metric_example() -> None:
    edges = [
        TreeEdge("A", "B", Fraction(1, 10)),
        TreeEdge("B", "C", Fraction(1, 20)),
        TreeEdge("B", "D", Fraction(1, 8)),
    ]
    distances = spanning_tree_distances("A", edges)
    write(
        "metric_gluing.json",
        {
            "root": "A",
            "edges": [{"u": e.u, "v": e.v, "error": frac(e.error)} for e in edges],
            "root_distance_bounds": {str(k): frac(v) for k, v in distances.items()},
        },
    )


def cubic_example() -> None:
    cert = cubic_bisection(Fraction(2), Fraction(0), Fraction(2), 12)
    write(
        "cubic_bisection.json",
        {
            "equation": "y^3+y=2",
            "x": frac(cert.x),
            "initial_lo": frac(cert.initial_lo),
            "initial_hi": frac(cert.initial_hi),
            "steps": [
                {
                    "lo": frac(step.lo),
                    "hi": frac(step.hi),
                    "mid": frac(step.mid),
                    "sign": step.sign,
                }
                for step in cert.steps
            ],
            "final_lo": frac(cert.final_lo),
            "final_hi": frac(cert.final_hi),
        },
    )


def main() -> None:
    demand_example()
    viability_example()
    metric_example()
    cubic_example()


if __name__ == "__main__":
    main()
