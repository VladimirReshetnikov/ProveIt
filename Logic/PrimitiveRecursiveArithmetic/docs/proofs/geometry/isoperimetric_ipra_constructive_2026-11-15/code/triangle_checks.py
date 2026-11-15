#!/usr/bin/env python3
"""Exact arithmetic diagnostics for the triangle section, not an iPRA proof.

All comparisons use integer polynomials. The complete universal argument
is in the LaTeX/PDF report; finite examples only check formulas and edge cases.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def heron16(a: int, b: int, c: int) -> int:
    return (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c)


def run(bound: int = 24) -> dict:
    cases = strict = weak_eq = strong_eq = degenerate_eq = 0
    for a in range(bound+1):
        for b in range(bound+1):
            for c in range(bound+1):
                if max(a, b, c)*2 > a+b+c:
                    continue
                h = heron16(a, b, c)
                expanded = 2*(a*a*b*b+b*b*c*c+c*c*a*a)-a**4-b**4-c**4
                assert h == expanded and h >= 0
                assert 27*h <= (a+b+c)**4
                assert h**3 <= 27*(a*b*c)**4
                cases += 1
                nondegenerate = min(a,b,c)>0 and max(a,b,c)*2 < a+b+c
                if nondegenerate:
                    strict += 1
                    assert (27*h == (a+b+c)**4) == (a == b == c)
                    assert (h**3 == 27*(a*b*c)**4) == (a == b == c)
                weak_eq += 27*h == (a+b+c)**4
                strong_eq += h**3 == 27*(a*b*c)**4
                degenerate_eq += (not nondegenerate and h**3 == 27*(a*b*c)**4)
    identity_cases = 0
    for x in range(13):
        for y in range(13):
            for z in range(13):
                p, q, r = x+y+z, x*y+y*z+z*x, x*y*z
                w = (x+y)*(y+z)*(z+x)
                assert w == p*q-r
                assert p*q-9*r == x*(y-z)**2+y*(z-x)**2+z*(x-y)**2
                assert q**3 >= 27*r*r
                assert 9*w >= 8*p*q
                assert p*q**4 >= 243*r**3
                assert 27*w**4 >= 4096*p**3*r**3
                identity_cases += 1
    return {
        "status": "passed",
        "interpretation": "Finite exact diagnostics, not a formal or universal proof",
        "integer_side_range": [0, bound],
        "triangles_including_degenerate": cases,
        "nondegenerate_triangles": strict,
        "weak_equality_cases": weak_eq,
        "strong_equality_cases": strong_eq,
        "degenerate_strong_equalities": degenerate_eq,
        "substitution_identity_cases": identity_cases,
        "nondegenerate_equality_classification": "equilateral, verified in tested range",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    serialized = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized)
    print(serialized, end="")

