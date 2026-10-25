"""Exact sparse substitution with one final coefficient-map cleanup.

The contract is extensional polynomial equality, not dictionary iteration order.
All supplied polynomial operations are the authenticated old con/mul/v functions.
"""


def substitute(p, i, r, *, con, mul, v):
    coefficients = {}
    for m, c in p.items():
        a = con(c)
        for j in m:
            a = mul(a, r if j == i else v(j))
        for monomial, coefficient in a.items():
            coefficients[monomial] = coefficients.get(monomial, 0) + coefficient
    return {m: c for m, c in coefficients.items() if c}
