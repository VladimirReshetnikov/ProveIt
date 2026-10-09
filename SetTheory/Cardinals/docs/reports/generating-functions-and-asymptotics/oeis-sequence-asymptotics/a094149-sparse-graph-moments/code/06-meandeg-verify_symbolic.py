#!/usr/bin/env python3
"""Exact symbolic checks for the collision polynomials and forest identities."""
from pathlib import Path
import json
from math import comb, factorial
import sympy as sp

c, q, z, n, s = sp.symbols("c q z n s", positive=True)
order = 6
rows = [[sp.Integer(1)]]


def cut(t, color):
    return sum(rows[t][ell] * sp.rf(color, ell) / factorial(ell)
               for ell in range(t + 1))


for k in range(1, order + 1):
    row = [sp.Integer(0)]
    for m in range(1, k + 1):
        expression = 0
        for color in range(1, m + 1):
            for a in range(k - m + 1):
                b = k - color - a
                if m - color < len(rows[b]):
                    expression += (c * comb(m - 1, color - 1)
                                   * cut(a, color) * rows[b][m - color])
        row.append(sp.expand(expression))
    rows.append(row)

d = []
P = []
for h in range(order + 1):
    dh = sp.factor(sum((-1)**(h-t) * cut(t, q) / c**t
                       * sp.rf(q+t, h-t) / factorial(h-t)
                       for t in range(h+1)))
    d.append(dh)
    ph = sum(sum((-1)**(u-v) * comb(u, v) * dh.subs(q, v)
                 for v in range(u+1)) * z**u / factorial(u)
             for u in range(h+1))
    P.append(sp.factor(ph))

assert sp.simplify(d[2] - (q*(q+1)/(2*c) + q)) == 0
assert sp.simplify(P[2] - z*(z+2+2*c)/(2*c)) == 0
assert sp.Poly(d[3], q).coeff_monomial(q**3) == 1/(6*c**2)
for h in range(2, order+1):
    assert sp.degree(d[h], q) <= h
    assert sp.simplify(d[h].subs(q, 0)) == 0
    touchard = [sum(rows[j]) if j == 0 else rows[j][j] for j in range(h+1)]
    centered = sum(comb(h, j)*(-c)**(h-j)*touchard[j]
                   for j in range(h+1))
    leading = sp.Poly(d[h], q).coeff_monomial(q**h)
    assert sp.simplify(leading - centered/(c**h*factorial(h))) == 0

newton_checks = 0
for t in range(order+1):
    rebuilt = sum(d[h] * factorial(h)/sp.rf(q, h) * comb(t, h)
                  for h in range(t+1))
    expected = cut(t, q)/(c**t * sp.rf(q, t)/factorial(t))
    assert sp.simplify(rebuilt-expected) == 0
    newton_checks += 1

forest_checks = 0
for nn in range(1, 12):
    for ss in range(0, 12):
        forest = sp.Rational(nn*comb(nn+2*ss, ss), nn+2*ss)
        k = nn+ss
        fresh = comb(k-1, ss)
        product = sp.prod(1+sp.Rational(ss, k-ss+j) for j in range(1, ss))
        assert sp.simplify(forest/fresh-product) == 0
        forest_checks += 1

destination = Path(__file__).resolve().parents[1]/"data"
destination.mkdir(parents=True, exist_ok=True)
result = {
    "status": "PASS", "maximum_collision_block_order": order,
    "symbolic_Newton_equalities": newton_checks,
    "Catalan_product_equalities": forest_checks,
    "d_polynomials": {str(h): str(d[h]) for h in range(order+1)},
    "P_polynomials": {str(h): str(P[h]) for h in range(order+1)},
    "symbolic_first_rows": [[str(v) for v in row] for row in rows],
    "scope": "Exact identities and finite polynomial coefficients; no asymptotic claim is inferred from these checks."
}
(destination/"symbolic_checks.json").write_text(json.dumps(result, indent=2)+"\n")
with (destination/"collision_polynomials.tex").open("w") as out:
    for h in range(2, 5):
        out.write("\\[P_{"+str(h)+"}(z;c)="+sp.latex(P[h])+".\\]\n")
print(json.dumps({key: result[key] for key in result if key not in
                 ["d_polynomials", "P_polynomials", "symbolic_first_rows"]}, indent=2))
print("P2 =", P[2])
print("P3 =", P[3])
