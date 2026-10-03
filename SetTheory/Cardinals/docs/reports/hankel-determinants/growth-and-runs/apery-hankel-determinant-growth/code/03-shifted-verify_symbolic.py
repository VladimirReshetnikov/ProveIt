#!/usr/bin/env python3
"""Finite exact identities and numerical equilibrium-mass checks.

The identities verify normalizations, not the analytic asymptotic theorem.
The displayed 1/N term is for the unperturbed Jacobi gamma product ONLY;
it is not a full first correction for the Apéry determinant.
"""

import json

import mpmath as mp
import sympy as S


def verify():
    s = S.symbols("s", positive=True)
    C = 17 + 12*S.sqrt(2)
    critical = S.simplify(2 / (C - 1))
    a = (s / (s + 2))**2
    assert S.simplify(critical - (3*S.sqrt(2)/4 - 1)) == 0
    assert S.simplify(a.subs(s, critical) - C**-2) == 0
    assert S.simplify(1/a - 1 - 4*(s+1)/s**2) == 0
    q = (1 - S.sqrt(a)) / (1 + S.sqrt(a))
    assert S.simplify(q - 1/(s+1)) == 0

    A = ((s+1)*S.log(C) + (s+1)**2*S.log(s+1)
         - s*s*S.log(s)/2 - (s+2)**2*S.log(s+2)/2)
    derivative = (S.log(C) + 2*(s+1)*S.log(s+1)
                  - s*S.log(s) - (s+2)*S.log(s+2))
    assert S.simplify(S.diff(A, s) - derivative) == 0
    assert S.simplify(S.expand_log(
        S.diff(A, s, 2) - S.log((s+1)**2/(s*(s+2))), force=True)) == 0

    # Each (sign,q,d) denotes sign*log G(q*N+d+1). The remaining factor
    # -log G(3/2) is N-independent and does not enter these cancellations.
    factors = [(1, 1, 0), (1, s+1, 0), (-1, s, 0),
               (1, 1, S.Rational(1, 2)), (1, s+1, S.Rational(1, 2)),
               (-1, s+2, S.Rational(1, 2))]
    assert S.simplify(sum(sign*q*q for sign, q, d in factors)) == 0
    assert S.simplify(sum(sign*q*d for sign, q, d in factors)) == 0
    logarithm = sum(sign*(d*d/2 - S.Rational(1, 12))
                    for sign, q, d in factors)
    assert S.simplify(logarithm + S.Rational(1, 24)) == 0
    jacobi_c1 = S.simplify(sum(sign*d*(2*d*d-1)/(12*q)
                             for sign, q, d in factors))
    assert S.simplify(jacobi_c1 + S.Rational(1, 48)
                      * (1 + 1/(s+1) - 1/(s+2))) == 0

    checks = []
    with mp.workdps(60):
        for text in ("0.1", "0.2", "1", "3"):
            slope = mp.mpf(text)
            lower = (slope / (slope + 2))**2

            def angular_density(theta):
                t = (1+lower)/2 + (1-lower)*mp.cos(theta)/2
                return (slope+2)*(1-lower)*mp.cos(theta/2)**2 / (2*mp.pi*t)

            mass_error = abs(mp.quad(angular_density, [0, mp.pi]) - 1)
            assert mass_error < mp.mpf("1e-55")
            checks.append({"s": text, "mass_error": str(mass_error)})
    return {
        "status": "PASS: exact symbolic and 60-digit normalization checks",
        "critical": str(critical),
        "barnes_first_log_correction": str(jacobi_c1),
        "correction_scope": "unperturbed Jacobi determinant only; not the Apéry correction",
        "equilibrium_mass": checks,
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
