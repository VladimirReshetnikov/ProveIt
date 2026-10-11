"""Independent construction of the (2,8) ordinary harmonic-tail identity.

The exact matrix/polynomial equalities are certificates for this fixed example.
The high-precision sums are diagnostics; the article proves the all-order result.
"""
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp

x = sp.Symbol("x")
b = 4
q = 2*b


def entry(j, k):
    d = 2*j+1
    e = d-2-q+2*k+1
    if e < 0:
        return sp.S.Zero
    return sp.bernoulli(e)*sum(
        (sp.binomial(u, v)/u for u, v in [(d-q+1, 2-2*k),
                                        (d-1, q-2*k)] if 2 <= v <= u),
        sp.S.Zero,
    )


matrix = sp.Matrix(b, b, lambda t, k: entry(b+t, k))
weights = sp.Matrix([[sp.binomial(2*b-1, 2*t) for t in range(b)]])
expected = sp.zeros(1, b)
expected[0, 0] = sp.Rational(2*b-1, 2)*(2-sp.bernoulli(2*b-2))
assert weights*matrix == expected

S = sp.expand(x**(2*b+1)*((1+x)**(2*b-1)+(1-x)**(2*b-1))/2)
W = sp.Poly(sp.expand(S.subs(x, x+sp.Rational(1, 2))
                      - S.subs(x, x-sp.Rational(1, 2))), x)
scale = sp.ilcm(*[v.q for v in W.all_coeffs()])
P = sp.Poly(scale*W.as_expr(), x)


def tail_coeff(p, k):
    if k == 0:
        return sp.Rational(1, p-1)
    return sp.bernoulli(2*k, sp.Rational(1, 2))*sp.rf(p, 2*k-1)/sp.factorial(2*k)


# A_2(n) A_q(n) ~ sum c_k x^(-q-2k), x=n+1/2.
K = 46
c = [sum(tail_coeff(2, j)*tail_coeff(q, k-j) for j in range(k+1))
     for k in range(K+1)]
product = {}
for (power,), coeff in P.terms():
    for k, ck in enumerate(c):
        exponent = power-q-2*k
        product[exponent] = product.get(exponent, 0)+coeff*ck
sub = sp.Poly(sum(v*x**e for e, v in product.items() if e >= 0), x)
rhs = -sp.Rational(scale*(2*b-1), 4)*(2-sp.bernoulli(2*b-2))
assert P.as_expr() == (547+129756*x**2+3657584*x**4+27896512*x**6
                      +71997696*x**8+66311168*x**10
                      +20500480*x**12+1720320*x**14)
assert rhs == -sp.Rational(169984, 3)


def mprat(value):
    value = sp.Rational(value)
    return mp.mpf(int(value.p))/int(value.q)


def numeric(dps, cutoff, terms):
    mp.mp.dps = dps
    pv = [mprat(v) for v in P.all_coeffs()]
    sv = [mprat(v) for v in sub.all_coeffs()]
    val = mp.mpf(0)
    for n in range(cutoff):
        xn = mp.mpf(n)+mp.mpf("0.5")
        val += mp.polyval(pv, xn)*mp.zeta(2, n+1)*mp.zeta(q, n+1)-mp.polyval(sv, xn)
    # Each omitted asymptotic monomial is summed by an ordinary Hurwitz zeta.
    # This is a numerical acceleration, not an interval-arithmetic proof.
    for k in range(1, terms+1):
        val += mprat(product[-2*k])*mp.zeta(2*k, mp.mpf(cutoff)+mp.mpf("0.5"))
    return {"dps": dps, "cutoff": cutoff, "asymptotic_terms": terms,
            "value": mp.nstr(val, 60),
            "absolute_error": mp.nstr(abs(val-mprat(rhs)), 8)}


result = {
    "scope": "Fixed (2,8) exact certificate plus uncertified floating-point diagnostics",
    "matrix": [[str(matrix[i, j]) for j in range(b)] for i in range(b)],
    "determinant": str(matrix.det()),
    "binomial_annihilator": [str(v) for v in weights],
    "exact_checks_passed": True,
    "polynomial": str(P.as_expr()),
    "subtraction": str(sub.as_expr()),
    "rhs": str(rhs),
    "diagnostics": [numeric(80, 80, 24), numeric(100, 120, 32)],
}
path = Path(__file__).resolve().parent.parent / "results" / "independent_tail_28.json"
path.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
