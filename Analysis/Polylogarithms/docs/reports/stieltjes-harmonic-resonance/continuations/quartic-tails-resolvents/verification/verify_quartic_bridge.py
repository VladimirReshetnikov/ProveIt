"""Independent finite algebra and numerical checks for the quartic digamma bridge.

The analytic proofs live in quartic_bridge.tex.  Floating point checks do not
replace them.  The displayed arithmetic truncation bound is analytic; rounding
in mpmath is not interval enclosed.  Run on a copy to preserve recorded output.
"""
from __future__ import annotations

import json
from pathlib import Path
import time

import mpmath as mp
import sympy as sp


def exact_checks():
    e, t, b, c, d, v, g, z2, z3, z4 = sp.symbols(
        "e t b c d v gamma zeta2 zeta3 zeta4"
    )
    checks = []

    def check(name, expr):
        reduced = sp.cancel(sp.expand(expr))
        if reduced != 0:
            raise AssertionError((name, reduced))
        checks.append(name)

    local = -1 / e + b + c * e + d * e**2 + v * e**3
    pp = e**-4 - 4 * b * e**-3 + (6 * b**2 - 4 * c) * e**-2
    pp += 4 * (-b**3 + 3 * b * c - d) / e
    expanded = sp.expand(local**4)
    for degree in range(-4, 0):
        check(f"principal_coefficient_{degree}", expanded.coeff(e, degree)
              - pp.coeff(e, degree))
    check("local_constant", expanded.coeff(e, 0)
          - (b**4 - 12 * b**2 * c + 6 * c**2 + 12 * b * d - 4 * v))

    alpha = -b**3 + 3 * b * c - d
    alpha_next = alpha.subs({b: b + t, c: c + t**2, d: d + t**3},
                           simultaneous=True)
    check("residue_difference", alpha_next - alpha - 3 * (c - b**2) * t - t**3)
    q = 6 * b**2 - 4 * c
    q_next = q.subs({b: b + t, c: c + t**2}, simultaneous=True)
    check("double_pole_difference", q_next - q - 12 * b * t - 2 * t**2)

    # Finite summation identity; symbols gamma, zeta2, zeta3 remain independent.
    h = [sp.Rational(0)] * 5
    elementary = [sp.Rational(1)] + [sp.Rational(0)] * 4
    h21 = h211 = h31 = sp.Rational(0)
    sum_alpha = sp.Rational(0)
    for n in range(1, 26):
        nn = sp.Integer(n)
        h211 += elementary[2] / nn**2
        h21 += elementary[1] / nn**2
        h31 += elementary[1] / nn**3
        for j in range(4, 0, -1):
            elementary[j] += elementary[j - 1] / nn
        for j in range(1, 5):
            h[j] += nn**-j
        bn, cn, dn = h[1] - g, z2 + h[2], h[3] - z3
        an = -bn**3 + 3 * bn * cn - dn
        sum_alpha += an / nn
        rhs = (-6 * elementary[4] + 6 * g * elementary[3]
               + 3 * (z2 - g**2) * elementary[2]
               + (g**3 - 3 * g * z2 + z3) * h[1] + h[1] * h[3]
               - 6 * h211 + 6 * g * h21
               + 3 * (z2 - g**2) * h[2] - h31)
        check(f"finite_summation_N_{n}", sum_alpha - rhs)

    ell, H = sp.symbols("ell H")
    e2 = (H**2 - z2) / 2
    e3 = (H**3 - 3 * H * z2 + 2 * z3) / 6
    e4 = (H**4 - 6 * H**2 * z2 + 3 * z2**2
          + 8 * H * z3 - 6 * z4) / 24
    asym = (-6 * e4 + 6 * g * e3 + 3 * (z2 - g**2) * e2
            + (g**3 - 3 * g * z2 + z3) * H + H * z3
            - 6 * z4 + 6 * g * z3 + 3 * (z2 - g**2) * z2 - z4 / 4)
    constant_a = g**4 / 4 - sp.Rational(9, 2) * g**2 * z2
    constant_a += 8 * g * z3 - sp.Rational(23, 8) * z4
    target = -ell**4 / 4 + 3 * z2 * ell**2 + constant_a
    check("asymptotic_constant_A", sp.expand(asym.subs(H, ell + g) - target)
          .subs(z2**2, sp.Rational(5, 2) * z4))

    local_constant = g**4 - 12 * g**2 * z2 + 6 * z2**2 + 12 * g * z3 - 4 * z4
    sum_b3 = sp.Rational(5, 4) * z4 - g * z3
    sum_bprev2 = z3 - g * z2
    sum_bsq2 = sp.Rational(17, 4) * z4 - 4 * g * z3 + g**2 * z2
    sum_c2 = sp.Rational(3, 2) * z2**2 + z4 / 2
    base = (local_constant - z4 - 2 * z3 + 4 * sum_b3
            + 12 * sum_bprev2 + 2 * z3 - 6 * sum_bsq2 + 4 * sum_c2)
    base_target = (g**4 - 18 * g**2 * z2 - 12 * g * z2
                   + 32 * g * z3 + 12 * z3 + sp.Rational(13, 2) * z4)
    check("integrated_lower_poles", sp.expand(base - base_target)
          .subs(z2**2, sp.Rational(5, 2) * z4))
    check("endpoint_constant_cancellation", base_target - 4 * constant_a
          - (12 * z3 - 12 * g * z2 + 18 * z4))

    u, eta, theta, g1, g2, g3 = sp.symbols("u eta theta gamma1 gamma2 gamma3")
    zs = 1 / u + g - g1 * u + g2 * u**2 / 2 - g3 * u**3 / 6
    zdouble = 1 / u**2 + g / u + (g**2 - z2) / 2 + eta * u
    ztriple = (1 / u**3 + g / u**2 + (g**2 - z2) / (2 * u)
               + (g**3 - 3 * g * z2 + 2 * z3) / 6 + theta * u)
    f = sp.expand(2 * ztriple - 2 * g * zdouble + (g**2 - z2) * zs)
    f1 = 2 * theta - 2 * g * eta - (g**2 - z2) * g1
    check("Laurent_pole_three", f.coeff(u, -3) - 2)
    check("Laurent_pole_two", f.coeff(u, -2))
    check("Laurent_pole_one", f.coeff(u, -1) + 2 * z2)
    check("Laurent_linear_coefficient", f.coeff(u, 1) - f1)
    d1 = f1 + g3 - 2 * z2 * g1
    check("convergent_series_conversion", 12 * g3 - 24 * z2 * g1 - 12 * d1
          - (-24 * theta + 24 * g * eta + 12 * (g**2 - z2) * g1))

    zz, nn = sp.symbols("z n", positive=True)
    for j in range(2, 5):
        primitive = ((nn + zz)**(1 - j) - nn**(1 - j)) / (1 - j) - zz / nn**j
        check(f"primitive_j_{j}", sp.diff(primitive, zz)
              - ((nn + zz)**-j - nn**-j))
    check("primitive_log", sp.diff(sp.log(1 + zz / nn) - zz / nn, zz)
          - ((nn + zz)**-1 - nn**-1))
    return {"passed": len(checks), "checks": checks}


def arithmetic_value(N, K):
    """Finite head + exact summation of a Binet asymptotic polynomial."""
    g, z2 = mp.euler, mp.zeta(2)
    total = mp.fsum((mp.digamma(n)**2 + mp.polygamma(1, n) - mp.log(n)**2)
                   * mp.log(n) / n for n in range(1, N))
    a = {1: -mp.mpf(1) / 2}
    for k in range(1, K + 1):
        a[2 * k] = -mp.bernoulli(2 * k) / (2 * k)
    p = {1: mp.mpf(1), 2: mp.mpf(1) / 2}
    for k in range(1, K + 1):
        p[2 * k + 1] = mp.bernoulli(2 * k)
    nonlog = dict(p)
    for j, aj in a.items():
        for k, ak in a.items():
            nonlog[j + k] = nonlog.get(j + k, mp.mpf(0)) + aj * ak
    for j, aj in a.items():
        total += 2 * aj * mp.zeta(j + 1, N, derivative=2)
    for j, pj in nonlog.items():
        total -= pj * mp.zeta(j + 1, N, derivative=1)

    bn = abs(mp.bernoulli(2 * K + 2))
    epsi = bn / (2 * K + 2)
    abound = mp.fsum(abs(aj) / mp.mpf(N)**j for j, aj in a.items())
    analytic_bound = 2 * epsi * mp.zeta(2 * K + 3, N, derivative=2)
    analytic_bound -= 2 * abound * epsi * mp.zeta(2 * K + 3, N, derivative=1)
    analytic_bound -= epsi**2 * mp.zeta(4 * K + 5, N, derivative=1)
    analytic_bound -= bn * mp.zeta(2 * K + 4, N, derivative=1)
    ordinary = (12 * mp.zeta(3) - 12 * g * z2 + 18 * mp.zeta(4)
                + 4 * mp.zeta(3, derivative=1))
    q4 = ordinary + 12 * mp.stieltjes(3) - 24 * z2 * mp.stieltjes(1) + 12 * total
    return q4, 12 * analytic_bound, total


def quad_value(delta, order):
    """Independent local Taylor integral, followed by ordinary quadrature.

    The series has radius one.  This uses neither harmonic Laurent data nor
    the Mittag--Leffler expansion, and avoids subtracting huge endpoint terms.
    """
    # x*psi(x) has a regular expansion at the origin.
    coeff = [mp.mpf(-1), -mp.euler]
    coeff.extend((-1)**j * mp.zeta(j) for j in range(2, order + 5))
    power = [mp.mpf(1)]
    for _ in range(4):
        out = [mp.mpf(0)] * min(len(power) + len(coeff) - 1, order + 5)
        for i, ai in enumerate(power):
            for j, bj in enumerate(coeff[:len(out) - i]):
                out[i + j] += ai * bj
        power = out
    local = mp.fsum(ck * (mp.log(delta) if k == 3 else delta**(k - 3) / (k - 3))
                   for k, ck in enumerate(power))
    regular = mp.quad(lambda x: mp.digamma(x)**4, [delta, mp.mpf('0.25'),
                                                mp.mpf('0.5'), 1])
    return local + regular


def numerical_checks():
    mp.mp.dps = 100
    records = []
    arith = []
    for N, K in [(48, 26), (64, 34)]:
        q, error, series = arithmetic_value(N, K)
        arith.append(q)
        records.append({"method": "harmonic_Binet_tail", "N": N, "K": K,
                        "value": mp.nstr(q, 91), "series": mp.nstr(series, 91),
                        "analytic_truncation_bound": mp.nstr(error, 8)})
    quads = []
    for delta, order in [(mp.mpf(1) / 8, 100), (mp.mpf(1) / 16, 90)]:
        value = quad_value(delta, order)
        quads.append(value)
        records.append({"method": "local_Taylor_and_quadrature",
                        "delta": str(delta), "order": order,
                        "value": mp.nstr(value, 91)})
    discrepancy = max(abs(q - arith[-1]) for q in quads)
    if discrepancy > mp.mpf('1e-78'):
        raise AssertionError(("arithmetic/quadrature disagreement", discrepancy))
    return {"mpmath_dps": mp.mp.dps, "records": records,
            "max_quadrature_discrepancy": mp.nstr(discrepancy, 8),
            "arithmetic_stability": mp.nstr(abs(arith[1] - arith[0]), 8),
            "warning": "Floating point results; analytic truncation error excludes rounding."}


def main():
    start = time.time()
    result = {"theorem": "quartic digamma / strict depth-three harmonic bridge",
              "versions": {"sympy": sp.__version__, "mpmath": mp.__version__},
              "exact": exact_checks(), "numeric": numerical_checks()}
    result["elapsed_seconds"] = round(time.time() - start, 3)
    output = Path(__file__).with_name("quartic_results.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"exact_passed": result["exact"]["passed"],
                      "numeric": result["numeric"], "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
