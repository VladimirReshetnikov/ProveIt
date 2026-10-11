#!/usr/bin/env python3
"""Independent numerical checks for the harmonic Newton and boundary formulas.

The proof in sections/02_harmonic.tex establishes convergence. These are
numerical cross-checks, not interval certificates. Finite binomial differences
are ill-conditioned at large index; a deliberately high working precision is
used. No assertion of high precision is made from a fixed truncation alone.
"""

from __future__ import annotations

import json
import argparse
import math
from pathlib import Path

import mpmath as mp


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results/harmonic.json")
args = parser.parse_args()

mp.mp.dps = 180
N = 240


def spectral_differences(s, derivative=0, count=N):
    """A_j^(derivative)(s), via a finite-difference table."""
    row = [mp.mpf(0)] + [
        mp.power(k, 1 - s) * (-mp.log(k)) ** derivative
        for k in range(1, count + 1)
    ]
    result = []
    for j in range(1, count + 1):
        row = [row[k + 1] - row[k] for k in range(len(row) - 1)]
        result.append(row[0])
    return result


def generalized_binomials(a, count=N):
    a = mp.mpmathify(a)
    c = mp.mpf(1)
    result = []
    for j in range(1, count + 1):
        c *= (a - j) / j
        result.append(c)
    return result


def newton(differences, a, u=0, count=N):
    coefficients = generalized_binomials(a, count)
    return -mp.fsum(
        coefficients[j - 1] * differences[j - 1] / (u + j)
        for j in range(1, count + 1)
    )


def newton_depth(differences, a, depth, count=N):
    coefficients = generalized_binomials(a, count)
    return (-1) ** (depth + 1) * mp.fsum(
        coefficients[j - 1] * differences[j - 1] / mp.mpf(j) ** (depth + 1)
        for j in range(1, count + 1)
    )


def integer_u_reference(s, a, u, derivative):
    def zeta_difference(z):
        # Native order derivatives avoid a numerical issue with infinitesimal
        # mp.diff at the special point s=0 in some mpmath versions.
        return mp.zeta(z, a, derivative=derivative) - mp.zeta(z, derivative=derivative)

    if u == 0:
        return zeta_difference(s)
    if u == 1:
        return zeta_difference(s - 1) / a
    if u == 2:
        return (
            zeta_difference(s - 2)
            + zeta_difference(s - 1)
        ) / (a * (a + 1))
    raise ValueError(u)


def remainder_kernel(t, a, u):
    if t == 0:
        return -(a - 1) / (1 + u)
    if t <= 1:
        w = -mp.expm1(-t)
        return -(a - 1) / (1 + u) * mp.exp(-a * t) * mp.hyp2f1(
            1, a + u, 2 + u, w
        )
    z = mp.exp(-t)
    gamma_factor = mp.gamma(a) * mp.gamma(1 + u) / mp.gamma(a + u)
    return (
        mp.exp(-a * t) * mp.hyp2f1(1, a + u, a, z)
        - gamma_factor * z / mp.power(1 - z, 1 + u)
    )


def reference_integral(s, a, u):
    return mp.quad(
        lambda t: mp.power(t, s - 1) * remainder_kernel(t, a, u),
        [0, 1, mp.inf],
    ) / mp.gamma(s)


def serial(z):
    if isinstance(z, (int, str, bool)):
        return z
    if abs(mp.im(z)) == 0:
        return mp.nstr(mp.re(z), 32)
    return {"real": mp.nstr(mp.re(z), 32), "imag": mp.nstr(mp.im(z), 32)}


checks = []


def record(name, actual, reference, **parameters):
    error = abs(actual - reference)
    item = {
        "name": name,
        "parameters": {key: serial(value) for key, value in parameters.items()},
        "computed": serial(actual),
        "reference": serial(reference),
        "absolute_error": mp.nstr(error, 12),
    }
    checks.append(item)
    print(name, "absolute error", mp.nstr(error, 8), flush=True)
    return error


# The nonpositive-spectral-order derivatives are checked against finite,
# ordinary Hurwitz-zeta derivative reductions at u=0,1,2. Finite differences
# for s=-m, k=0 are exactly terminating; k>0 is the substantive test.
a = mp.mpf("7.25")
for m, k in [(0, 1), (0, 2), (1, 1), (2, 2)]:
    values = spectral_differences(-m, k)
    for u in [0, 1, 2]:
        expected = integer_u_reference(-m, a, u, k)
        actual = newton(values, a, u)
        error = record(
            "spectral Newton vs Hurwitz reduction",
            actual, expected, a=a, s=-m, derivative=k, u=u, terms=N
        )
        assert error < mp.mpf("1e-13")

# A complex noninteger u is checked against the independent hypergeometric
# Mellin kernel, outside the original Dirichlet half-plane.
s = mp.mpc("0.65", "0.2")
a = mp.mpc("6.4", "0.3")
u = mp.mpc("0.31", "-0.17")
values = spectral_differences(s)
with mp.workdps(65):
    expected = reference_integral(s, a, u)
actual = newton(values, a, u)
error = record(
    "Newton vs hypergeometric Mellin remainder",
    actual, expected, a=a, s=s, u=u, terms=N
)
assert error < mp.mpf("1e-12")

# At positive integer common shift the Newton sum must terminate. Check
# against the source's finite weighted Dirichlet formula for complex s,u.
s = mp.mpc("-1.7", "0.4")
u = mp.mpc("0.37", "0.2")
for A in [2, 4, 7]:
    for k in [0, 1, 2]:
        values = spectral_differences(s, k, A - 1)
        gamma_factor = mp.gamma(A) * mp.gamma(1 + u) / mp.gamma(A + u)
        expected = -gamma_factor * mp.fsum(
            mp.rf(1 + u, n - 1) / mp.factorial(n - 1)
            * mp.power(n, -s) * (-mp.log(n)) ** k
            for n in range(1, A)
        )
        actual = newton(values, A, u, A - 1)
        error = record(
            "integer shift finite identity",
            actual, expected, a=A, s=s, u=u, derivative=k
        )
        assert error < mp.mpf("1e-150")


def complete_homogeneous(m, length, degree):
    coefficients = [mp.mpf(0)] * (degree + 1)
    coefficients[0] = mp.mpf(1)
    for nu in range(1, length + 1):
        value = mp.mpf(1) / (m + nu)
        # Ascending update permits repeated powers of this variable.
        for j in range(1, degree + 1):
            coefficients[j] += value * coefficients[j - 1]
    return coefficients


def primitive(x, m, k, q):
    h = complete_homogeneous(m, q - 1, k)
    return mp.factorial(k) / mp.rf(m + 1, q - 1) * mp.fsum(
        h[k - j] / mp.factorial(j)
        * mp.zeta(1 - m - q, x, derivative=j)
        for j in range(k + 1)
    )


def boundary_jet(x, m, k):
    if m == 0:
        return -mp.mpf(1) if k == 0 else (-1) ** k * k * mp.stieltjes(k - 1, x)
    first = m * mp.zeta(1 - m, x, derivative=k)
    return first if k == 0 else first - k * mp.zeta(1 - m, x, derivative=k - 1)


# Differentiate the proposed finite antiderivative with respect to x and
# compare with independently evaluated generalized Stieltjes constants.
with mp.workdps(45):
    for x, m, k, q in [
        (mp.mpf("0.7"), 0, 1, 1),
        (mp.mpf("0.7"), 0, 2, 2),
        (mp.mpf("1.3"), 1, 1, 3),
        (mp.mpf("1.3"), 2, 2, 2),
    ]:
        actual = mp.diff(lambda xx: primitive(xx, m, k, q), x, q)
        expected = boundary_jet(x, m, k)
        error = record(
            "finite repeated primitive vs boundary jet",
            actual, expected, x=x, m=m, derivative=k, integration_order=q
        )
        assert error < mp.mpf("1e-35")

result = {
    "working_precision_decimal_digits": 180,
    "newton_terms": N,
    "interpretation": (
        "Numerical cross-checks, not interval certificates. Newton truncation "
        "errors are reported against independent special-function identities; "
        "convergence and termwise differentiation are proved in the article."
    ),
    "all_thresholds_passed": True,
    "checks": checks,
}
output = args.output
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print("Wrote", output, flush=True)
