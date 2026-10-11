#!/usr/bin/env python3
"""Exact partial-fraction and polylogarithm derivative checks.

The normal convergence and resonance removability arguments are analytic
proofs in the article.  This script checks their finite algebraic formulas.
"""
import json
from pathlib import Path

import sympy as sp


def main():
    z,j=sp.symbols("z j",positive=True)
    checks=[]
    for r in range(1,7):
        amplitude=sp.prod(1/(z-q) for q in range(1,r+1))
        fractions=sum(sp.Rational((-1)**(r-q),
                    sp.factorial(q-1)*sp.factorial(r-q))/(z-q)
                      for q in range(1,r+1))
        residual=sp.cancel(amplitude-fractions)
        checks.append({"name":"partial-fraction-amplitude","r":r,
                       "passed":residual==0})
    for k in range(6):
        primitive=-sp.factorial(k)*sum(
            (-sp.log(z))**h/sp.factorial(h)*sp.polylog(k+1-h,z/j)
            for h in range(k+1))
        residual=sp.diff(primitive,z)-(-sp.log(z))**k/(z-j)
        residual=residual.subs(sp.polylog(0,z/j),(z/j)/(1-z/j))
        residual=sp.simplify(residual)
        checks.append({"name":"spectral-polylogarithm-primitive","k":k,
                       "passed":residual==0})
    report={"description":"Exact checks for normalized shift-germ primitives",
            "sympy_version":sp.__version__,"checks":checks,
            "summary":{"exact_count":len(checks),
                       "all_passed":all(c["passed"] for c in checks)}}
    output=Path(__file__).resolve().parents[1]/"results"/"shift_primitives.json"
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report["summary"],indent=2))
    if not report["summary"]["all_passed"]:
        raise SystemExit(1)


if __name__=="__main__":
    main()
