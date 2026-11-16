from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from native_clause_framework import (
    DemandNode,
    backward_demands,
    bounded_monotone_closure,
    relational_viability,
    stable_observation,
)


def main() -> None:
    bounds = (6, 6, 4)

    def transformer(x):
        return (min(6, x[1] + 1), min(6, x[0]), min(4, (x[0] + x[1]) // 3))

    fixed, history = bounded_monotone_closure(bounds, transformer)

    graph = [
        DemandNode("coefficients", (), lambda d: {}),
        DemandNode("polynomial", ("coefficients",), lambda d: {"coefficients": (d[0] + 2, d[1])}),
        DemandNode("root_cloud", ("polynomial",), lambda d: {"polynomial": (d[0] + 3, d[1] + 1)}),
        DemandNode("observer", ("root_cloud",), lambda d: {"root_cloud": (d[0] + 2, d[1] + 2)}),
    ]
    demands = backward_demands(graph, "observer", (5, 3))

    layers = [
        (Fraction(0), Fraction(1, 10)),
        (Fraction(1, 20), Fraction(3, 20)),
        (Fraction(3, 40), Fraction(7, 40)),
    ]
    viability = relational_viability(
        layers,
        lambda q, x, y: abs(x - y) <= Fraction(1, 8),
    )
    representative, diameter = stable_observation(
        viability.viable[-1],
        lambda x: x * x,
        lambda x, y: abs(x - y),
        Fraction(1, 20),
    )

    result = {
        "cyclic_demand": {
            "bounds": list(bounds),
            "fixed_point": list(fixed),
            "history": [list(x) for x in history],
        },
        "backward_demand": {k: list(v) for k, v in demands.items()},
        "relational": {
            "viable": [[str(x) for x in sorted(layer)] for layer in viability.viable],
            "least_path": [str(x) for x in viability.least_path] if viability.least_path else None,
            "observer_representative": str(representative),
            "observer_diameter": str(diameter),
        },
    }
    out = Path(__file__).resolve().parents[1] / "examples" / "example_run.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
