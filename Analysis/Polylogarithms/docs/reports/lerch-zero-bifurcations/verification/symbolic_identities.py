#!/usr/bin/env python3
"""Optional exact symbolic tables; not needed for interval certificates.

Z2, Z3, ... denote zeta values as formal symbols, and Y = X + EulerGamma.
The formal Stieltjes symbols gamma_0, gamma_1, ... stand for gamma_j(a).
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Optional dependency missing: install sympy, or skip this script.") from exc


def main(out: Path, degree: int = 10) -> None:
    if not 1 <= degree <= 16:
        raise ValueError("Choose degree between 1 and 16.")
    Y, X, t = sp.symbols("Y X t")
    z = {r: sp.Symbol(f"Z{r}") for r in range(2, degree + 2)}
    R = [sp.Integer(1)]
    Q = [sp.Integer(1)]
    checks = 0
    for m in range(degree):
        R.append(sp.expand(Y * R[m] + sum(
            sp.binomial(m, r) * sp.factorial(r) * z[r + 1] * R[m-r]
            for r in range(1, m+1))))
        Q.append(sp.expand(Y * Q[m] + sum(
            (-1)**r * sp.binomial(m, r) * sp.factorial(r) * z[r + 1] * Q[m-r]
            for r in range(1, m+1))))
        assert sp.expand(sp.diff(R[m+1], Y) - (m+1)*R[m]) == 0
        assert sp.expand(sp.diff(Q[m+1], Y) - (m+1)*Q[m]) == 0
        checks += 2
    # Independent truncated product of exponential cumulant factors.
    def truncated(expr):
        return sp.Add(*[
            sp.expand(expr).coeff(t, j)*t**j for j in range(degree+1)])
    for family, sign in ((R, False), (Q, True)):
        gen = sum(Y**j*t**j/sp.factorial(j) for j in range(degree+1))
        for r in range(2, degree+1):
            c = ((-1)**(r+1) if sign else 1)*z[r]/r
            factor = sum(c**j*t**(r*j)/sp.factorial(j)
                         for j in range(degree//r+1))
            gen = truncated(gen*factor)
        for m in range(degree+1):
            assert sp.expand(sp.factorial(m)*gen.coeff(t,m)-family[m]) == 0
            checks += 1
    gammas = sp.symbols(f"gamma_0:{degree+1}")
    constants = {}
    elementary = {}
    for k in range(1, 6):
        p = sp.Poly(sp.prod(1+t/sp.Integer(j) for j in range(1,k+1)), t)
        for n in range(degree+1):
            C = sp.factorial(n)*p.nth(n+1) + sum(
                sp.factorial(n)*p.nth(j)*(-1)**(n-j)*gammas[n-j]/sp.factorial(n-j)
                for j in range(min(n,k)+1))
            constants[f"n={n},k={k}"] = str(sp.expand(C))
            g = sp.expand(sp.factorial(k)*sum(
                sp.factorial(n)*p.nth(j)*(-X)**(n-j)/sp.factorial(n-j)
                for j in range(min(n,k)+1)))
            elementary[f"n={n},k={k}"] = str(g)
    out.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "all optional symbolic assertions passed",
        "assertions": checks,
        "degree": degree,
        "conventions": {"Y":"X + EulerGamma", "Zr":"zeta(r)",
                        "gamma_j":"generalized Stieltjes constant gamma_j(a)",
                        "elementary_X":"log(a)"},
        "R": {str(m):str(v) for m,v in enumerate(R)},
        "Q": {str(m):str(v) for m,v in enumerate(Q)},
        "C": constants, "elementary_numerators": elementary,
        "sympy_version": sp.__version__}
    (out/"symbolic_identities.json").write_text(json.dumps(report,indent=2)+"\n")
    print(f"{checks} optional symbolic assertions passed; degree {degree}.")

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out",type=Path,default=Path(__file__).resolve().parents[1]/"certificates")
    parser.add_argument("--degree",type=int,default=10)
    args=parser.parse_args()
    main(args.out,args.degree)
