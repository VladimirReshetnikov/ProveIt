#!/usr/bin/env python3
"""Exact independent Jacobi/Selberg trace-cumulant check.

The Schur average is equation (4.1) of Albion, Rains and Warnaar,
Elliptic A_n Selberg Integrals, DOI: 10.1007/s00365-025-09705-8.
https://doi.org/10.1007/s00365-025-09705-8

It supplies finite-N moments of T=sum(t_j), independently of the endpoint
variation formula. Comparing its first three cumulants checks the linear,
quadratic and cubic terms of c_rel for f(t)=lambda*t. No analytic asymptotic
remainder is certified by this finite symbolic calculation.
"""

import json
import sympy as S


def verify():
    N, s, z, lam, a = S.symbols("N s z lambda a", positive=True)
    b = S.Rational(1, 2)

    def schur_average(partition):
        # Hook-content formula for the dimension s_partition(1^N).
        dimension = S.Integer(1)
        for i, row in enumerate(partition, 1):
            for j in range(1, row+1):
                hook = row-j + sum(lower >= j for lower in partition[i:]) + 1
                dimension *= (N+j-i)/hook
        value = dimension
        for i, row in enumerate(partition, 1):
            for j in range(row):
                value *= ((s+1)*N-i+1+j) / ((s+2)*N+b-i+1+j)
        return S.factor(value)

    m1 = schur_average([1])
    m2 = schur_average([2]) + schur_average([1, 1])
    m3 = (schur_average([3]) + 2*schur_average([2, 1])
          + schur_average([1, 1, 1]))
    cumulants = [m1, S.factor(m2-m1*m1), S.factor(m3-3*m2*m1+2*m1**3)]
    coefficients = [S.simplify(S.series(k.subs(N, 1/z), z, 0, 2)
                               .removeO().coeff(z, 1)) for k in cumulants]
    c1, c2, c3 = coefficients
    assert S.simplify(c1-(s+1)/(4*(s+2)**3)) == 0
    assert S.simplify(c2-s*s*(s+1)/(2*(s+2)**5)) == 0
    assert S.simplify(c3+2*s*s*(s+1)**2/(s+2)**7) == 0
    exact = S.factor(lam*c1 + lam*lam*c2/2 + lam**3*c3/6)

    U = lam*(1+a)/2
    energy = lam*lam*(1-a)**2/16
    D = 2*a**S.Rational(3, 2)*(1-a)*S.diff(U, a)/s
    functional = (D*S.diff(energy, a)/6 + D*S.diff(U, a)/8
                  + D/24*(1/(1-a) + S.Rational(3, 2)/a)
                  + a**S.Rational(3, 2)/(12*s)
                  * ((1-a)*S.diff(U, a, 2) - S.diff(U, a)))
    functional = S.factor(functional.subs(a, (s/(s+2))**2))
    assert S.simplify(functional-exact) == 0
    return {
        "status": "PASS: exact mean, variance and third-cumulant coefficients",
        "source": "Albion–Rains–Warnaar, equation (4.1), DOI 10.1007/s00365-025-09705-8",
        "mean_1_over_N": str(S.factor(c1)),
        "variance_1_over_N": str(S.factor(c2)),
        "third_cumulant_1_over_N": str(S.factor(c3)),
        "c_rel": str(exact),
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
