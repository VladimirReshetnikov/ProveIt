#!/usr/bin/env python3
"""Generate exact positivity certificates for the A279619 Hankel theorem.

Run from any directory: python code/generate_certificates.py
Requires SymPy. No network access, floating-point arithmetic, or pickle files.
The independent standard-library checker is verify_certificates.py.
"""
from __future__ import annotations
import json
from fractions import Fraction
from math import comb
from pathlib import Path
import sympy as sp
from sympy.polys.matrices import DomainMatrix

ROOT = Path(__file__).resolve().parents[1]
n, R = sp.symbols("n R")

def formal_ratios(order: int) -> list[Fraction]:
    b = [Fraction(27)]
    for m in range(1, order + 1):
        t = b + [Fraction(0)]
        v = [t[0]] + [sum((t[k]*comb(j-1,k-1) for k in range(1,j+1)), Fraction(0))
                      for j in range(1,m+1)]
        w = [sum((t[k]*v[j-k] for k in range(j+1)), Fraction(0))
             for j in range(m+1)]
        coefficient = w[m] + 2*w[m-1] - 26*v[m] - 13*v[m-1]
        if m >= 2:
            coefficient += w[m-2] - 2*v[m-2]
        if m == 1:
            coefficient += 27
        if m == 2:
            coefficient -= 6
        b.append(-coefficient / 28)
    return b

def rational(x: Fraction) -> sp.Rational:
    return sp.Rational(x.numerator, x.denominator)

def serialize_polynomial(P: sp.Poly, shift: int = 5) -> dict:
    """P(n) = scale * sum coefficients[k]*(n-shift)**k."""
    shifted = P.shift(shift)
    denominator, integral = shifted.clear_denoms(convert=True)
    content, primitive = integral.primitive()
    coefficients = list(reversed(primitive.all_coeffs()))
    assert content > 0 and all(c > 0 for c in coefficients)
    scale = sp.Rational(content, denominator)
    return {"degree": int(primitive.degree()), "shift": shift,
            "scale": str(scale), "coefficients": [str(c) for c in coefficients]}

def main() -> None:
    b = formal_ratios(12)
    K = 2*abs(b[11]) + 1
    A = sp.Poly(n**11, n)
    ell = sp.Poly(sum(rational(b[j])*n**(11-j) for j in range(11)) - rational(K), n)
    h = ell + 2*rational(K)
    p = lambda x: 26*x*x + 13*x + 2
    q = lambda x: 27*x*x - 27*x + 6
    le, he = ell.as_expr(), h.as_expr()
    lower = sp.Poly((p(n+1)*he + q(n+1)*n**11)*(n+1)**11
                    - (n+2)**2*he*le.subs(n,n+1), n)
    upper = sp.Poly((n+2)**2*le*he.subs(n,n+1)
                    - (p(n+1)*le+q(n+1)*n**11)*(n+1)**11, n)
    certificates = {"ell": serialize_polynomial(ell),
                    "induction_lower": serialize_polynomial(lower),
                    "induction_upper": serialize_polynomial(upper)}
    field = sp.QQ.frac_field(n, R)
    x = [field.one, field.from_sympy(R)]
    for k in range(1, 8):
        xx = (field.from_sympy(p(n+k))*x[k] + field.from_sympy(q(n+k))*x[k-1])
        x.append(xx/field.from_sympy((n+k+1)**2))
    denominator_exponents = {
        2: [2], 3: [6,4,2], 4: [8,8,6,4,2], 5: [10,10,10,8,6,4,2]}
    for r in range(2,6):
        matrix = DomainMatrix([[x[i+j] for j in range(r)] for i in range(r)],
                              (r,r), field)
        d = sp.cancel(field.to_sympy(matrix.det()))
        num, den = sp.fraction(d)
        expected = sp.prod((n+j)**v for j,v in enumerate(denominator_exponents[r],2))
        assert sp.expand(den-expected) == 0
        qr = [sp.Poly(0,n) for _ in range(r+1)]
        for (j,), coefficient in sp.Poly(num,R).terms():
            pc = sp.Poly(coefficient,n)*A**(r-j)
            for k in range(j+1):
                qr[k] += pc*ell**(j-k)*comb(j,k)*(2*rational(K))**k
        for k in range(r+1):
            bern = sum((qr[j]*sp.Rational(comb(k,j),comb(r,j))
                        for j in range(k+1)), sp.Poly(0,n))
            certificates[f"H{r}_B{k}"] = serialize_polynomial(bern)
    data = {
        "format": "A279619-Hankel-exact-certificates-v1",
        "description": "Rational polynomial identities and positive coefficients; see article.",
        "ratio_coefficients": [str(x) for x in b], "barrier_order": 10,
        "K": str(K), "tail_start": 5,
        "determinant_denominator_exponents": denominator_exponents,
        "polynomials": certificates,
    }
    target = ROOT / "data" / "certificates.json"
    target.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    count = sum(len(v["coefficients"]) for v in certificates.values())
    print(f"Generated {len(certificates)} polynomials, {count} positive coefficients.")
    print(f"Wrote {target.name}; verify with the independent checker.")

if __name__ == "__main__":
    main()
