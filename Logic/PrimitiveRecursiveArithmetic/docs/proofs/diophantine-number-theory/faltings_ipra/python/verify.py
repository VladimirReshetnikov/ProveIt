#!/usr/bin/env python3
"""Cross-check two independent finite-search methods and known resultants."""
from bounded_points import (Quintic, Point, bounded_points,
                            independent_fraction_search, discriminant,
                            determinant, is_point)
import json
from pathlib import Path


def main() -> None:
    cases = [Quintic(1,-1,0,0,0), Quintic(1,0,0,0,0),
             Quintic(0,-1,0,0,0), Quintic(-2,2,1,-1,1)]
    checks = []
    for f in cases:
        for B in [0, 1, 3, 8, 12]:
            direct = sorted(bounded_points(f, B))
            independent = independent_fraction_search(f, B)
            assert direct == independent
            assert len(direct) == len(set(direct))
            assert all(is_point(f, p) and p.height() <= B for p in direct)
            checks.append({"coefficients": list(f.__dict__.values()),
                           "bound": B, "points": len(direct)})
    assert discriminant(Quintic(1,-1,0,0,0)) == 2869
    assert discriminant(Quintic(1,0,0,0,0)) == 3125
    assert discriminant(Quintic(0,0,0,0,0)) == 0
    assert determinant([[0,1],[1,0]]) == -1
    assert determinant([]) == 1
    assert not is_point(cases[0], Point(0,0,1,1))
    assert not is_point(cases[0], Point(0,2,1,1))
    assert not is_point(cases[0], Point(0,1,2,2))
    output = {"result": "PASS", "independent_search_comparisons": len(checks),
              "checks": checks,
              "scope": "finite code validation only; no global height bound proved"}
    path = Path(__file__).resolve().parents[1]/"verification"/"python.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(output, indent=2)+"\n")
    print(json.dumps({"result": "PASS", "comparisons": len(checks)}))


if __name__ == "__main__":
    main()
