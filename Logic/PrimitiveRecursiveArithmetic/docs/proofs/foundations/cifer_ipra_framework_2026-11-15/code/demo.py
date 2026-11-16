from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from cifer import (
    Node,
    ProofGraph,
    backward_viability,
    cubic_bisect,
    demand_closure,
    residual_report,
)


def frac(q: Fraction) -> str:
    return f"{q.numerator}/{q.denominator}"


def main() -> None:
    graph = ProofGraph(
        (
            Node("curve-code", kind="input", statement="a coded smooth curve"),
            Node(
                "height-producer",
                kind="boundary",
                statement="a primitive-recursive height cutoff with proof",
            ),
            Node(
                "bounded-points",
                ("curve-code", "height-producer"),
                statement="complete bounded enumeration",
            ),
            Node(
                "point-verification",
                ("bounded-points",),
                statement="every listed code is a point and every point occurs",
            ),
            Node(
                "finite-list-theorem",
                ("point-verification",),
                kind="final",
                statement="the rational points equal the displayed finite list",
            ),
            Node(
                "irrelevant-analytic-bound",
                kind="boundary",
                statement="not used by this query",
            ),
        )
    )

    fixed, demand_trace = demand_closure(
        (0, 0, 4),
        (16, 16, 16),
        lambda d: (max(d[0], d[1] + 2), max(d[1], d[2] + 3), d[2]),
    )

    levels = [
        (Fraction(-2), Fraction(-1), Fraction(0)),
        (Fraction(-3, 2), Fraction(-1), Fraction(-1, 2)),
        (Fraction(-5, 4), Fraction(-1), Fraction(-3, 4)),
    ]
    viable, path = backward_viability(
        levels, lambda k, x, y: abs(x - y) <= Fraction(1, 2 ** (k + 1))
    )

    interval, cubic_trace = cubic_bisect(Fraction(7, 5), 10)

    out = {
        "framework": "CIFER",
        "residual_compilation": residual_report(graph, "finite-list-theorem"),
        "demand_closure": {
            "fixed_point": list(fixed),
            "trace": [list(v) for v in demand_trace],
        },
        "relational_viability": {
            "viable_levels": [sorted(frac(x) for x in level) for level in viable],
            "least_path": None if path is None else [frac(x) for x in path],
        },
        "cubic_bisection": {
            "x": "7/5",
            "steps": 10,
            "final_interval": [frac(interval.lo), frac(interval.hi)],
            "width": frac(interval.width),
            "trace_length": len(cubic_trace),
        },
    }

    target = Path(__file__).resolve().parents[1] / "examples" / "demo.json"
    target.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
