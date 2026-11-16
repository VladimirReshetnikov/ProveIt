from __future__ import annotations

import json
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path
from typing import Any

from pcog import RationalInterval, build_cubic_graph, finite_horizon_paths


def encode(value: Any) -> Any:
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, RationalInterval):
        return {"lo": encode(value.lo), "hi": encode(value.hi)}
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    graph = build_cubic_graph()
    run = graph.run({"observable": 10}, {"x": Fraction(1), "apartness_bits": 0})

    clouds = (
        (Fraction(0), Fraction(1)),
        (Fraction(0), Fraction(1, 2), Fraction(1)),
        (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)),
        (Fraction(3, 8), Fraction(1, 2), Fraction(5, 8)),
    )
    compatibility = lambda _level, a, b: abs(a - b) <= Fraction(1, 2)
    paths = finite_horizon_paths(clouds, compatibility)

    output = {
        "purpose": "finite execution evidence only; not an iPRA proof",
        "graph": {
            "requested": encode(run.requested),
            "demands": encode(run.demands),
            "outputs": encode(run.outputs),
        },
        "relational_example": {
            "clouds": encode(clouds),
            "least_paths_by_horizon": encode(paths),
        },
    }
    path = root / "examples" / "example_run.json"
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(path)


if __name__ == "__main__":
    main()
