"""Run the package's exact checks; write a reproducible JSON results file."""

import json
import platform
import random
import sys
from fractions import Fraction as F
from pathlib import Path

from check_polynomials import check_all
from rational_geometry import (
    finite_heron, finite_trigonometry, invariants,
    json_safe, root_floor, root_floor_scan,
)


def run():
    identities = check_all()
    root_checks = 0
    scan_checks = 0
    for p in range(33):
        for den in range(1, 17):
            for k in range(7):
                r = root_floor(F(p, den), k)
                assert r*r <= F(p, den) < (r+F(1, 1 << k))**2
                root_checks += 1
                if p <= 6 and den <= 5 and k <= 3:
                    assert r == root_floor_scan(F(p, den), k)
                    scan_checks += 1
    named_cases = [
        ("right_3_4_5", (3, 0, 0, 4)),
        ("obtuse", (2, 0, -1, 1)),
        ("clockwise", (0, 4, 3, 0)),
        ("rational", (F(2, 3), F(-1, 7), F(4, 5), F(3, 8))),
        ("very_thin", (1, 0, F(3, 2), F(1, 1 << 25))),
        ("collinear", (1, 2, 2, 4)),
        ("coincident_vertices", (0, 0, 2, 1)),
        ("all_zero", (0, 0, 0, 0)),
    ]
    rng = random.Random(20261114)
    cases = named_cases + [
        (f"rational_sample_{i:02d}",
         tuple(F(rng.randint(-5, 5), rng.randint(1, 9)) for _ in range(4)))
        for i in range(40)
    ]
    heron_count = sine_count = 0
    summary = []
    for name, coords in cases:
        for k in (0, 5, 12):
            h = finite_heron(coords, k)
            heron_count += 1
            if invariants(coords)[-1] != 0:
                s = finite_trigonometry(coords, k)
                sine_count += 1
            else:
                s = None
            if name in {n for n, _ in named_cases} and k == 12:
                summary.append({"case": name, "coordinates": coords,
                                "heron": h, "trigonometry": s})
    result = {
        "status": "all exact Python checks passed",
        "scope": "Exact computational evidence; not a Lean build or an iPRA proof certificate.",
        "python": platform.python_version(),
        "polynomial_identity_checks": len(identities),
        "root_bracket_checks": root_checks,
        "root_binary_vs_scan_checks": scan_checks,
        "finite_heron_instances": heron_count,
        "finite_cosine_and_extended_sine_instances": sine_count,
        "lean_compilation": "not run: Lean and Lake unavailable in delivery environment",
        "identities": identities,
        "selected_examples": summary,
    }
    return json_safe(result)


if __name__ == "__main__":
    result = run()
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else (
        Path(__file__).resolve().parents[1] / "verification" / "results.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("selected_examples", "identities")}, indent=2))
