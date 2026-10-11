#!/usr/bin/env python3
"""Exact formal checks for the ordered Hurwitz finite-part formulas.

All special-function values and derivatives are algebraically independent
formal symbols here. The verification is supplementary algebra, not a
replacement for the analytic proof of normal convergence/continuation.
Uses Newton's elementary-symmetric recurrence, rather than differentiating
the displayed exponential generating function.
"""

from __future__ import annotations

import json
from pathlib import Path
import sympy as sp


MAX_DEPTH = 7
t = sp.Symbol("t")
p, q = sp.symbols("p q", nonzero=True)
g = sp.symbols(f"g0:{MAX_DEPTH + 1}")
z = {(m, j): sp.Symbol(f"z{m}_{j}")
     for m in range(2, MAX_DEPTH + 1)
     for j in range(MAX_DEPTH + 1)}


def truncate(expr, low=-MAX_DEPTH, high=MAX_DEPTH):
    out = sp.S.Zero
    for term in sp.Add.make_args(sp.expand(expr)):
        power = term.as_powers_dict().get(t, 0)
        if low <= power <= high:
            out += term
    return sp.expand(out)


def coeff(expr, degree):
    return sp.expand(expr).coeff(t, degree)


def power_sum(m, regular=True):
    if m == 1:
        base = sum((-1)**j * g[j] * t**j / sp.factorial(j)
                   for j in range(MAX_DEPTH + 1))
        return base if regular else 1/t + base
    return sum(m**j * z[m, j] * t**j / sp.factorial(j)
               for j in range(MAX_DEPTH + 1))


def elementary(regular):
    vals = [sp.S.One]
    for d in range(1, MAX_DEPTH + 1):
        # Keep the full Laurent range needed by subsequent recurrence.
        val = sum((-1)**(m-1)*power_sum(m, regular)*vals[d-m]
                  for m in range(1, d+1))/d
        vals.append(truncate(val))
    return vals


regular = elementary(True)
ordinary = elementary(False)
B = [coeff(v, 0) for v in regular]


def family(d, pp=p, qq=q):
    result = B[d]
    denominator = sp.S.One
    for k in range(1, d):
        denominator *= pp + (k-1)*qq
        result += qq**k*coeff(regular[d-k], k)/denominator
    return result


G, g1, g2, g3, g4 = g[:5]
Z2, Z3, Z4, Z5 = (z[m, 0] for m in range(2, 6))
z21, z22, z23 = (z[2, j] for j in range(1, 4))
z31, z32, z41 = z[3, 1], z[3, 2], z[4, 1]

printed_B = {
    1: G,
    2: (G**2-Z2)/2,
    3: (G**3-3*G*Z2+2*Z3)/6,
    4: (G**4-6*G**2*Z2+3*Z2**2+8*G*Z3-6*Z4)/24,
    5: (G**5-10*G**3*Z2+15*G*Z2**2+20*G**2*Z3
        -20*Z2*Z3-30*G*Z4+24*Z5)/120,
}

A41 = (-G**3*g1/6 + G*g1*Z2/2 - G**2*z21/2
       + Z2*z21/2 - g1*Z3/3 + G*z31 - z41)
A32 = (G*g1**2/2 + G**2*g2/4 - g2*Z2/4
       + g1*z21-G*z22+sp.Rational(3, 2)*z32)
A23 = -G*g3/6-g1*g2/2-sp.Rational(2, 3)*z23
printed_family = {
    2: printed_B[2]-q*g1/p,
    3: printed_B[3]-q*(G*g1+z21)/p+q**2*g2/(2*p*(p+q)),
    4: (printed_B[4]+q/p*(-G**2*g1/2+g1*Z2/2-G*z21+z31)
        + q**2/(p*(p+q))*((g1**2+G*g2)/2-z22)
        - q**3*g3/(6*p*(p+q)*(p+2*q))),
    5: (printed_B[5]+q*A41/p+q**2*A32/(p*(p+q))
        + q**3*A23/(p*(p+q)*(p+2*q))
        + q**4*g4/(24*p*(p+q)*(p+2*q)*(p+3*q))),
}

checks = []


def check(name, residual):
    zero = sp.cancel(sp.expand(residual)) == 0
    checks.append({"name": name, "exact_zero": bool(zero)})
    if not zero:
        raise AssertionError((name, sp.factor(residual)))


for d, formula in printed_B.items():
    check(f"Gamma polynomial B{d}", formula-B[d])
for d, formula in printed_family.items():
    check(f"Printed depth-{d} p,q family", formula-family(d))
for d in range(1, MAX_DEPTH+1):
    check(f"Independent diagonal Laurent recurrence depth {d}",
          family(d, sp.S.One, sp.S.One)-coeff(ordinary[d], 0))
    check(f"Zero trailing slopes depth {d}", family(d, p, sp.S.Zero)-B[d])

# Entire diagonal meromorphic identity, checked at enough Laurent powers
# to ensure that each negative coefficient and the finite part agree.
for d in range(1, MAX_DEPTH+1):
    decomposed = sum(regular[d-k]/(sp.factorial(k)*t**k)
                     for k in range(d+1))
    for j in range(-d, 1):
        check(f"Diagonal canonical coefficient depth {d}, degree {j}",
              coeff(ordinary[d]-decomposed, j))

# Independent cubic stuffle identity: all six orders, formal slopes.
from itertools import permutations
c = sp.symbols("c1:4", nonzero=True)
eta = sp.Symbol("eta")


def cubic(c1, c2, c3):
    return (B[3]-c3*(G*g1+z21)/c1
            + c3**2*g2/(2*c1*(c1+c2))+(c2-c3)*eta/c1)


sum_ordered = sum(cubic(*v) for v in permutations(c))
zetas = [1/(ci*t)+sum((-1)**j*g[j]*(ci*t)**j/sp.factorial(j)
                         for j in range(3)) for ci in c]
stuffle = sp.prod(zetas)
for i in range(3):
    remaining = [j for j in range(3) if j != i]
    slope = c[remaining[0]]+c[remaining[1]]
    stuffle -= zetas[i]*(Z2+slope*z21*t)
stuffle += 2*Z3
check("Six-order cubic stuffle finite part", sum_ordered-coeff(stuffle, 0))
check("Cubic equal trailing slopes", cubic(p, q, q)-family(3))

result = {
    "status": "all exact formal checks passed",
    "method": "independent Newton elementary-symmetric recurrence",
    "symbolic_depths_checked": list(range(1, MAX_DEPTH+1)),
    "number_of_checks": len(checks),
    "checks": checks,
    "scope": ("Verifies algebraic coefficients and Laurent extraction. "
              "Analytic continuation and normal convergence are proved "
              "in article Sections 2 and 3, not inferred from computation."),
}
out = Path(__file__).resolve().parent.parent / "results" / "ordered_core_exact_checks.json"
out.parent.mkdir(exist_ok=True)
out.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
print(json.dumps({"status": result["status"],
                  "checks": len(checks), "receipt": str(out)}, indent=2))
