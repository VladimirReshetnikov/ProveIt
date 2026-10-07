"""Optional, explicitly uncertified numerical reproduction for Report227.

Run ``python numerics.py --order 3 --precision 60`` or import
``numerical_diagnostics(order=3, precision=60)``. Only mpmath is required for
numerical work; import and the exact formal checks use the standard library.
The public cap is 0 <= order <= 8 and 30 <= precision <= 120 decimal digits.
All guards are explicit and remain active under ``python -O``.

This is a finite implementation of the report's fixed-order construction. It
does not prove the all-orders theorem, certify any decimal by intervals, supply
effective asymptotic remainder constants, or justify rounding a Lambert-W
estimate. Finite integer comparisons in the inverse examples are exact.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial
import json
import platform

MAX_ORDER = 8
MIN_PRECISION = 30
MAX_PRECISION = 120
EXACT_THRESHOLD_CAP = 512
GUARD_DIGITS = 30


def require(condition, message):
    """A correctness check which is deliberately not a Python assertion."""
    if not condition:
        raise ValueError(message)


def _pad(a, n):
    return list(a[:n + 1]) + [Q(0)] * max(0, n + 1 - len(a))


def _mul(a, b, n):
    c = [Q(0)] * (n + 1)
    for i, x in enumerate(a[:n + 1]):
        if x:
            for j, y in enumerate(b[:n - i + 1]):
                c[i + j] += x * y
    return c


def _power_unit(a, exponent, n):
    """Truncated a(t)**exponent, requiring a(0)=1; exact for Fractions."""
    require(a[0] == 1, "Unit-series power requires constant coefficient one")
    a = _pad(a, n)
    b = [Q(1)] + [Q(0)] * n
    for k in range(1, n + 1):
        b[k] = sum((((exponent + 1) * j - k) * a[j] * b[k - j]
                    for j in range(1, k + 1)), Q(0)) / k
    return b


def _exp_zero(a, n):
    require(a[0] == 0, "Formal exponential requires constant coefficient zero")
    a = _pad(a, n)
    b = [Q(1)] + [Q(0)] * n
    for k in range(1, n + 1):
        b[k] = sum((j * a[j] * b[k - j] for j in range(1, k + 1)), Q(0)) / k
    return b


def _log_unit(a, n):
    require(a[0] == 1, "Formal logarithm requires constant coefficient one")
    a = _pad(a, n)
    inverse = _power_unit(a, Q(-1), n)
    derivative = [(i + 1) * a[i + 1] for i in range(n)]
    quotient = _mul(derivative, inverse, n - 1)
    return [Q(0)] + [quotient[i - 1] / i for i in range(1, n + 1)]


def _compose(a, b, n):
    require(b[0] == 0, "Composition requires inner constant coefficient zero")
    result = [Q(0)] * (n + 1)
    power = [Q(1)] + [Q(0)] * n
    for coefficient in a[:n + 1]:
        for i in range(n + 1):
            result[i] += coefficient * power[i]
        power = _mul(power, b, n)
    return result


@lru_cache(maxsize=None)
def _universal_w(n):
    """w=1-R as a series in p, where p²=-2(log(1-w)+w)."""
    base = [Q(2, j + 2) for j in range(n)]
    result = [Q(0)]
    for k in range(1, n + 1):
        result.append(_power_unit(base, -Q(k, 2), k - 1)[k - 1] / k)
    return tuple(result)


def _bernoulli_numbers(n):
    numbers = [Q(1)]
    for m in range(1, n + 1):
        numbers.append(-sum(Q(comb(m + 1, k)) * numbers[k]
                            for k in range(m)) / (m + 1))
    return numbers


@lru_cache(maxsize=None)
def _gamma_coefficients(n):
    bernoulli = _bernoulli_numbers(n + 1)

    def polynomial(k, x):
        return sum(comb(k, j) * bernoulli[j] * x ** (k - j)
                   for j in range(k + 1))

    logarithm = [Q(0)]
    for j in range(1, n + 1):
        logarithm.append((-1) ** (j + 1) *
                         (polynomial(j + 1, Q(1, 2)) - polynomial(j + 1, Q(1))) /
                         (j * (j + 1)))
    return tuple(_exp_zero(logarithm, n))


def _inverse_residual(delta, log_corrections, lam, n):
    # t=1/m0; delta=m-m0. The equation is
    # lam*delta - log(1+t*delta)/2 + sum ell_j*t^j/(1+t*delta)^j=0.
    unit = [Q(1)] + _pad(delta, n - 1)
    unit = _pad(unit, n)
    logarithm = _log_unit(unit, n)
    residual = [lam * v - logarithm[i] / 2
                for i, v in enumerate(_pad(delta, n))]
    for j in range(1, min(n + 1, len(log_corrections))):
        power = _power_unit(unit, Q(-j), n - j)
        for k, value in enumerate(power):
            residual[j + k] += log_corrections[j] * value
    return residual


def _inverse_coefficients(log_corrections, lam, n):
    require(lam > 0, "The inverse requires lambda > 0")
    delta = [Q(0)] * (n + 1)
    for j in range(1, n + 1):
        delta[j] = -_inverse_residual(delta, log_corrections, lam, j)[j] / lam
    return delta


def formal_self_checks():
    """Exact finite identities through MAX_ORDER, using no optional package.

    These are reproducible algebraic checks of this implementation, not a
    proof that a finite asymptotic expansion controls an infinite remainder.
    """
    for order in range(MAX_ORDER + 1):
        degree = 2 * order + 1
        w = _universal_w(degree)
        one_minus_w = [Q(1)] + [-x for x in w[1:]]
        logarithm = _log_unit(one_minus_w, degree + 1)
        residual = [logarithm[j] + (w[j] if j < len(w) else 0)
                    for j in range(degree + 2)]
        residual[2] += Q(1, 2)
        require(all(x == 0 for x in residual),
                f"Universal Puiseux identity failed at order {order}")

        b = list(_gamma_coefficients(order))
        inner = [Q(0)] + [Q((-1) ** (j - 1)) for j in range(1, order + 2)]
        left = _compose(b, inner, order + 1)
        right = _mul(_mul([Q(1), Q(1, 2)],
                          _power_unit([Q(1), Q(1)], -Q(1, 2), order + 1),
                          order + 1), b, order + 1)
        require(left == right,
                f"Bernoulli/Gamma normalized recurrence failed at order {order}")
        bplus = _mul([Q(1), Q(1, 2)], b, order)
        plus_left = _compose(bplus, inner, order + 1)
        plus_right = _mul(_mul([Q(1), Q(3, 2)],
                               _power_unit([Q(1), Q(1)], -Q(3, 2), order + 1),
                               order + 1), bplus, order + 1)
        require(plus_left == plus_right,
                f"Second-sector Gamma normalized recurrence failed at order {order}")

        # Check the exact polynomial Gamma-shift denominators in two forms.
        direct = [Q(1)]
        rising = [Q(1)]
        for j in range(1, order + 1):
            direct = _mul(direct, [-Q(2 * j - 1, 2), Q(1)], order)
        for j in range(order):
            rising = _mul(rising, [Q(1, 2) - order + j, Q(1)], order)
        require(_pad(direct, order) == _pad(rising, order),
                f"Gamma denominator identity failed at order {order}")
        prefactor = Q(1)
        for j in range(1, order + 1):
            prefactor *= Q(1, 2) - j
        require(prefactor == Q((-1) ** order * factorial(2 * order),
                               4 ** order * factorial(order)),
                f"Half-integer Gamma prefactor failed at order {order}")

        # Rational finite-data tests of the inverse recursion at every order.
        ell = [Q(0)] + [Q(j, j + 1) for j in range(1, order + 1)]
        delta = _inverse_coefficients(ell, Q(3, 2), order)
        require(all(x == 0 for x in _inverse_residual(delta, ell, Q(3, 2), order)),
                f"Formal inverse recursion failed at order {order}")
    require(_gamma_coefficients(3) == (Q(1), -Q(1, 8), Q(1, 128), Q(5, 1024)),
            "First Bernoulli/Gamma coefficients differ from the report")
    # After factoring C^2*(1+rho)/((1-rho)*beta^2), the s^-2
    # coefficient from H^2 G^2 is +1 and that from z R H^2 G^3/2
    # is (1/2)*(-2)=-1. In R G^3, 3*(1/3)-1=0 first.
    require(3 * Q(1, 3) - 1 == 0 and Q(1) + Q(1, 2) * (-2) == 0,
            "Exact second-sector s^-2 coefficient cancellation failed")
    return {
        "passed": True,
        "orders_checked": list(range(MAX_ORDER + 1)),
        "universal_puiseux_residual_through_degree": 2 * MAX_ORDER + 2,
        "gamma_recurrence_residual_through_degree": MAX_ORDER + 1,
        "gamma_shifts_checked": ["1/2", "3/2"],
        "inverse_check": "exact rational test data at every supported order",
        "arithmetic": "fractions.Fraction; no optional package; guards survive -O",
        "defect_cancellation": "3*(1/3)-1=0 in R*G^3; normalized sum 1+(1/2)*(-2)=0",
    }


def _rooted_coefficients(n):
    require(n >= 1, "At least one rooted coefficient is required")
    r = [0] * (n + 1)
    r[1] = 1
    sigma = [0] * (n + 1)
    for k in range(1, n + 1):
        if k > 1:
            numerator = sum(sigma[j] * r[k - j] for j in range(1, k))
            r[k], remainder = divmod(numerator, k - 1)
            require(remainder == 0 and r[k] > 0,
                    f"Rooted-tree recurrence failed at index {k}")
        for j in range(k, n + 1, k):
            sigma[j] += k * r[k]
    return r


def _exact_f(r, n):
    require(len(r) > n + 1, "Exact f requires r through n+1")
    divisor_sum = [0] * (n + 1)
    for k in range(1, n + 1):
        for j in range(k, n + 1, k):
            divisor_sum[j] += k * r[k + 1]
    h, g, f = [1] + [0] * n, [1] + [0] * n, [1] + [0] * n
    for k in range(1, n + 1):
        numerator = sum(divisor_sum[j] * h[k - j] for j in range(1, k + 1))
        h[k], remainder = divmod(numerator, k)
        require(remainder == 0, f"Forest recurrence failed at index {k}")
        g[k] = sum(r[j] * g[k - j] for j in range(1, k + 1))
        f[k] = sum(h[j] * g[k - j] for j in range(k + 1))
        require(f[k] > f[k - 1], f"Finite monotonicity check failed at index {k}")
    require(f[:12] == [1, 2, 6, 17, 50, 143, 416, 1199, 3474, 10049, 29119, 84377],
            "Initial exact f coefficients failed their regression check")
    return f


def _mpq(mp, x):
    return mp.mpf(x.numerator) / x.denominator if isinstance(x, Q) else mp.mpf(x)


def _analytic_tails(mp, cutoff, r):
    # At exponent k, E_k=(1/k) sum_{n|k,n<k} n*r_n. The same
    # formula for D replaces r_n with r_{n+1}. No double infinite sum
    # is used or silently treated as exact: exponents > cutoff are omitted.
    en, dn, jn = ([0] * (cutoff + 1) for _ in range(3))
    for n in range(1, cutoff // 2 + 1):
        for k in range(2 * n, cutoff + 1, n):
            en[k] += n * r[n]
            dn[k] += n * r[n + 1]
            jn[k] += n * r[n + 2]
    e = [mp.mpf(0)] + [mp.mpf(en[k]) / k for k in range(1, cutoff + 1)]
    d = [mp.mpf(0)] + [mp.mpf(dn[k]) / k for k in range(1, cutoff + 1)]
    jt = [mp.mpf(0)] + [mp.mpf(jn[k]) / k for k in range(1, cutoff + 1)]
    return e, d, jt


def _numeric_engine(mp, cutoff, r, f):
    order = MAX_ORDER
    degree = 2 * order + 1
    e, decoration, j2tail = _analytic_tails(mp, cutoff, r)
    rho = mp.findroot(lambda z: mp.log(z) + 1 + mp.polyval(e[::-1], z),
                      (mp.mpf("0.33"), mp.mpf("0.35")))
    require(0 < rho < 1, "Numerical critical point is not in (0,1)")
    root_residual = abs(mp.log(rho) + 1 + mp.polyval(e[::-1], rho))
    ej, dj, tj = ([mp.mpf(0)] * (degree + 2) for _ in range(3))
    rho_power = mp.mpf(1)
    for k in range(cutoff + 1):
        if k:
            rho_power *= rho
        for q in range(min(k, order + 1) + 1):
            weight = (-1) ** q * comb(k, q) * rho_power
            ej[2 * q] += e[k] * weight
            dj[2 * q] += decoration[k] * weight
            tj[2 * q] += j2tail[k] * weight
    # p(s)^2=-2(log(1-s²)+E(rho(1-s²))-E(rho)).
    p_squared = [mp.mpf(0)] * (degree + 2)
    for q in range(1, order + 2):
        p_squared[2 * q] = 2 * (mp.mpf(1) / q - ej[2 * q])
    beta = mp.sqrt(p_squared[2])
    require(beta > 0, "Positive square-root branch was not obtained")
    root_unit = [p_squared[k + 2] / beta ** 2 for k in range(degree)]
    root_unit[0] = mp.mpf(1)
    p = [mp.mpf(0)] + [beta * x for x in _power_unit(root_unit, Q(1, 2), degree - 1)]
    w = _compose([_mpq(mp, c) for c in _universal_w(degree)], p, degree)
    rjet = [mp.mpf(1)] + [-x for x in w[1:]]
    hlog = [sum(rjet[j - 2 * q] for q in range(j // 2 + 1)) / rho + dj[j]
            for j in range(degree)]
    hlog[0] -= 1
    C = mp.exp(hlog[0])
    hlog[0] = mp.mpf(0)
    hjet = [C * x for x in _exp_zero(hlog, degree - 1)]
    w_over_s = w[1:]
    unit_denominator = [x / beta for x in w_over_s]
    unit_denominator[0] = mp.mpf(1)
    sfjet = [x / beta for x in _mul(hjet,
                                   _power_unit(unit_denominator, Q(-1), degree - 1),
                                   degree - 1)]
    K = sfjet[0] / mp.sqrt(mp.pi)
    # Compute the finite exact-Gamma transfer product, then its Bernoulli jet.
    transfer = [mp.mpf(0)] * (order + 1)
    for ell in range(order + 1):
        factor = Q((-1) ** ell * factorial(2 * ell), 4 ** ell * factorial(ell))
        piece = [Q(1)] + [Q(0)] * (order - ell)
        for q in range(1, ell + 1):
            piece = _mul(piece, _power_unit([Q(1), -Q(2 * q - 1, 2)],
                                            Q(-1), order - ell), order - ell)
        for j, v in enumerate(piece):
            transfer[ell + j] += sfjet[2 * ell] / sfjet[0] * _mpq(mp, factor * v)
    d = _mul([_mpq(mp, x) for x in _gamma_coefficients(order)], transfer, order)
    d[0] = mp.mpf(1)
    shifted = [mp.mpf(0)] * (order + 1)
    for j in range(order + 1):
        for k, value in enumerate(_power_unit([Q(1), Q(-1)], -Q(2 * j + 1, 2), order - j)):
            shifted[j + k] += d[j] * _mpq(mp, value)
    log_d = _log_unit(d, order)
    lam = -mp.log(rho)
    inverse = [_mpq(mp, x) for x in _inverse_coefficients(log_d, lam, order)]
    # The second sector: construct s^3 B from the report's four signed terms.
    # The J2 tail uses r_(n+2); F(z^2) is safely inside F's convergence disk.
    njet = degree - 1
    j2log = [sum((q + 1) * rjet[j - 2 * q] for q in range(j // 2 + 1)) / rho ** 2
             + tj[j] - (1 / rho if j % 2 == 0 else 0) for j in range(njet + 1)]
    j2log[0] -= 1
    j2constant = mp.exp(j2log[0])
    j2log[0] = mp.mpf(0)
    j2jet = [j2constant * x for x in _exp_zero(j2log, njet)]
    f2jet = [mp.mpf(0)] * (njet + 1)
    for n in range(cutoff // 2 + 1):
        weight = f[n] * rho ** (2 * n)
        for q in range(min(2 * n, order) + 1):
            f2jet[2 * q] += weight * (-1) ** q * comb(2 * n, q)
    zjet = [rho, mp.mpf(0), -rho]
    plus_z = [1 + rho, mp.mpf(0), -rho]
    inverse_one_minus_z = [_mpq(mp, x) / (1 - rho) for x in _power_unit(
        [mp.mpf(1), mp.mpf(0), rho / (1 - rho)], Q(-1), njet)]
    sg = [_mpq(mp, x) / beta for x in _power_unit(unit_denominator, Q(-1), njet)]
    sf_squared = _mul(sfjet, sfjet, njet)
    pref1 = _mul(zjet, inverse_one_minus_z, njet)
    pref2 = _mul(plus_z, inverse_one_minus_z, njet)
    pref3 = [x / 2 for x in _mul(zjet, pref2, njet)]
    term1 = _mul(pref1, _mul(j2jet, sg, njet), njet)
    term2 = _mul(pref2, sf_squared, njet)
    term3 = _mul(pref3, _mul(rjet, _mul(sf_squared, sg, njet), njet), njet)
    term4 = [-x / 2 for x in _mul(zjet, _mul(rjet, _mul(sg, f2jet, njet), njet), njet)]
    bjet = [term3[j] + (term2[j - 1] if j >= 1 else 0)
            + (term1[j - 2] + term4[j - 2] if j >= 2 else 0)
            for j in range(njet + 1)]
    A = rho * (1 + rho) * C ** 2 / (2 * (1 - rho) * beta ** 3)
    L = 2 * A / mp.sqrt(mp.pi)
    btransfer = [mp.mpf(0)] * (order + 1)
    gamma_prefactor = Q(1)
    for ell in range(order + 1):
        if ell:
            gamma_prefactor *= Q(3, 2) - ell
        piece = [Q(1)] + [Q(0)] * (order - ell)
        for q in range(1, ell + 1):
            piece = _mul(piece, _power_unit([Q(1), Q(3, 2) - q], Q(-1), order - ell), order - ell)
        for j, value in enumerate(piece):
            btransfer[ell + j] += bjet[2 * ell] / A * _mpq(mp, gamma_prefactor * value)
    gamma_three_halves = _mul([Q(1), Q(1, 2)], list(_gamma_coefficients(order)), order)
    bcorrections = _mul([_mpq(mp, x) for x in gamma_three_halves], btransfer, order)
    bcorrections[0] = mp.mpf(1)
    # Coefficientwise numeric residual checks, scaled to accommodate large jets.
    implicit = _log_unit(rjet, degree + 1)
    for j in range(degree + 2):
        implicit[j] += w[j] if j < len(w) else 0
        implicit[j] += p_squared[j] / 2
    product = _mul(w_over_s, sfjet, degree - 1)
    residuals = {
        "critical_equation": root_residual,
        "puiseux_implicit_scaled": max(abs(x) for x in implicit) /
            max(mp.mpf(1), max(abs(x) for x in p_squared)),
        "forest_quotient_scaled": max(abs(product[j] - hjet[j]) for j in range(degree)) /
            max(mp.mpf(1), max(abs(x) for x in hjet)),
        "inverse_formal_scaled": max(abs(x) for x in _inverse_residual(inverse, log_d, lam, order)) /
            max(mp.mpf(1), max(abs(x) for x in inverse)),
        "second_puiseux_coefficient": abs(rjet[2] - beta ** 2 / 3),
        "K_normalization": abs(K - C / (beta * mp.sqrt(mp.pi))),
        "defect_leading_scaled": abs(bjet[0] - A) / A,
        "defect_s_minus_2_cancellation_scaled": abs(bjet[1]) / A,
    }
    return {"rho": rho, "beta": beta, "C": C, "K": K, "lambda": lam,
            "rjet": rjet, "sfjet": sfjet, "d": d, "e": shifted,
            "inverse": inverse, "log_d": log_d, "residuals": residuals,
            "bjet": bjet, "bcorrections": bcorrections, "A": A, "L": L,
            "defect_canceling_terms": [term2[0], term3[1]]}


def numerical_diagnostics(order=3, precision=60):
    """Return JSON-serializable, unvalidated decimals plus finite self-checks.

    ``order`` selects reported coefficients. Every invocation also checks the
    whole supported range 0..8, and repeats the cap-order computation with 80
    more analytic-tail terms and 20 more working digits. Agreement is empirical
    evidence only, explicitly not an interval error bound or a proof.
    """
    require(type(order) is int and 0 <= order <= MAX_ORDER,
            f"order must be an integer in [0,{MAX_ORDER}]")
    require(type(precision) is int and MIN_PRECISION <= precision <= MAX_PRECISION,
            f"precision must be an integer in [{MIN_PRECISION},{MAX_PRECISION}]")
    try:
        import mpmath as mp
    except ImportError as exc:
        raise RuntimeError("Optional numerical diagnostics require mpmath; exact checks do not") from exc
    formal = formal_self_checks()
    cutoff = 6 * (precision + 35) + 12 * MAX_ORDER
    exact_r_degree = max((cutoff + 80) // 2 + 2, EXACT_THRESHOLD_CAP + 1)
    r = _rooted_coefficients(exact_r_degree)
    f = _exact_f(r, exact_r_degree - 1)
    with mp.workdps(precision + GUARD_DIGITS):
        first = _numeric_engine(mp, cutoff, r, f)
    with mp.workdps(precision + GUARD_DIGITS + 20):
        result = _numeric_engine(mp, cutoff + 80, r, f)
        tolerance = mp.power(10, -(precision - 5))
        stability = mp.mpf(0)
        for name in ("rho", "beta", "C", "K", "lambda", "A", "L"):
            stability = max(stability, abs(result[name] - first[name]) / max(1, abs(result[name])))
        for name in ("rjet", "sfjet", "d", "e", "inverse", "bjet", "bcorrections"):
            for a, b in zip(result[name], first[name]):
                stability = max(stability, abs(a - b) / max(1, abs(a)))
        require(stability < tolerance, "Empirical precision/tail-cutoff agreement failed")
        require(all(value < tolerance for value in result["residuals"].values()),
                "A numeric coefficient residual exceeded the requested tolerance")
        expected = ("-6.8282646484775676846346784546012941",
                    "68.441092016175542628147308094548358",
                    "-792.76888464734142614319322548664545")
        regression_tolerance = mp.power(10, -min(29, precision - 5))
        require(all(abs(result["d"][j] - mp.mpf(expected[j - 1])) < regression_tolerance
                    for j in range(1, 4)), "The displayed d_1,d_2,d_3 regression failed")
        gamma_error = mp.mpf(0)
        for ell in range(MAX_ORDER + 1):
            for m in (MAX_ORDER + 2, 37, 100):
                lhs = mp.gamma(m - ell + mp.mpf("0.5")) / mp.gamma(m + mp.mpf("0.5"))
                rhs = 1 / mp.fprod(mp.mpf(m) - q + mp.mpf("0.5") for q in range(1, ell + 1))
                gamma_error = max(gamma_error, abs(lhs - rhs) / max(1, abs(lhs)))
        require(gamma_error < tolerance, "Numeric half-integer Gamma identity check failed")

        def decimal(x):
            x = _mpq(mp, x)
            require(mp.isfinite(x), "A nonfinite numerical result was produced")
            return mp.nstr(x, precision)

        rho, beta, C, K, lam = (result[k] for k in ("rho", "beta", "C", "K", "lambda"))
        comparisons = []
        for m in (40, 80, 160, EXACT_THRESHOLD_CAP):
            leading = K * rho ** (-m) / mp.sqrt(m)
            relative = sum(result["d"][j] / mp.mpf(m) ** j for j in range(order + 1))
            gamma_sum = rho ** (-m) * sum(
                result["sfjet"][2 * ell] * mp.gamma(m - ell + mp.mpf("0.5")) /
                (mp.gamma(mp.mpf("0.5") - ell) * mp.gamma(m + 1))
                for ell in range(order + 1))
            comparisons.append({"m": m, "exact_f_m": str(f[m]),
                                "power_series_relative_error": decimal(leading * relative / f[m] - 1),
                                "finite_Gamma_sum_relative_error": decimal(gamma_sum / f[m] - 1)})
        inverse_examples = []
        targets = [10 ** 10, 10 ** 30, 10 ** 60, f[64], f[64] + 1, f[500], f[500] + 1]
        for target in targets:
            argument = -2 * lam * (K / target) ** 2
            require(-1 / mp.e < argument < 0, "Lambert W_-1 real-domain condition failed")
            value = mp.lambertw(argument, -1)
            require(abs(mp.im(value)) < tolerance, "Lambert W_-1 returned a nonreal value")
            m0 = -mp.re(value) / (2 * lam)
            corrected = m0 + sum(result["inverse"][j] / m0 ** j for j in range(1, order + 1))
            def smooth_equation(x):
                multiplier = sum(result["d"][j] / x ** j for j in range(order + 1))
                return K * mp.exp(lam * x) / mp.sqrt(x) * multiplier / target - 1
            smooth_root = mp.findroot(smooth_equation, (m0, m0 + 1))
            require(abs(mp.im(smooth_root)) < tolerance and mp.re(smooth_root) > 0,
                    "The selected smooth asymptotic inverse root is not positive real")
            smooth_root = mp.re(smooth_root)
            require(abs(smooth_equation(smooth_root)) < tolerance,
                    "The numerical smooth inverse residual check failed")
            threshold = next((m for m, v in enumerate(f[:EXACT_THRESHOLD_CAP + 1]) if v >= target), None)
            require(threshold is not None and threshold > 0, "Exact finite threshold cap was exceeded")
            require(f[threshold - 1] < target <= f[threshold], "Exact threshold bracket failed")
            inverse_examples.append({
                "target": str(target), "Lambert_W_branch": -1,
                "leading_m0": decimal(m0), "corrected_m": decimal(corrected),
                "smooth_truncated_expansion_root": decimal(smooth_root),
                "smooth_root_minus_exact_integer_threshold": decimal(smooth_root - threshold),
                "smooth_equation_relative_residual": decimal(smooth_equation(smooth_root)),
                "uncertified_ceiling_of_smooth_root": int(mp.ceil(smooth_root)),
                "corrected_minus_exact_integer_threshold": decimal(corrected - threshold),
                "uncertified_ceiling_of_corrected_m": int(mp.ceil(corrected)),
                "exact_integer_threshold": threshold,
                "exact_f_previous": str(f[threshold - 1]), "exact_f_at_threshold": str(f[threshold]),
                "exact_comparison": "f[m-1] < target <= f[m]",
                "leading_equation_relative_residual": decimal(K * mp.exp(lam * m0) / mp.sqrt(m0) / target - 1),
            })
        constants = {name: decimal(result[name]) for name in ("rho", "beta", "C", "K", "lambda")}
        constants.update({"rho_K": decimal(rho * K), "b": decimal(beta / mp.sqrt(rho)),
                          "2C_over_beta_squared": decimal(2 * C / beta ** 2)})
        output = {
            "status": "UNCERTIFIED NUMERICAL DIAGNOSTICS; finite exact comparisons labeled separately",
            "requested_order": order, "requested_decimal_digits": precision,
            "caps": {"order": MAX_ORDER, "precision": [MIN_PRECISION, MAX_PRECISION],
                     "exact_threshold_index": EXACT_THRESHOLD_CAP},
            "dependencies": {"python": platform.python_version(), "mpmath": mp.__version__,
                             "sympy": "not used"},
            "construction": {"analytic_exponent_cutoffs": [cutoff, cutoff + 80],
                             "working_decimal_digits": [precision + GUARD_DIGITS, precision + GUARD_DIGITS + 20],
                             "rooted_integer_coefficients_through": exact_r_degree,
                             "computed_order_for_self_checks": MAX_ORDER,
                             "cost": "O(M^2) integer recurrence plus finite polynomial arithmetic; M is the stated rooted degree",
                             "runtime_guidance": "Typically seconds to a minute on a modern CPU; platform-dependent, no timeout guarantee"},
            "constants": constants,
            "R_Puiseux": {str(j): decimal(result["rjet"][j]) for j in range(2 * order + 2)},
            "F_Puiseux": {str(j - 1): decimal(result["sfjet"][j]) for j in range(2 * order + 1)},
            "Bernoulli_Gamma_coefficients_exact": [str(x) for x in _gamma_coefficients(order)],
            "d_coefficients": [decimal(x) for x in result["d"][:order + 1]],
            "e_coefficients": [decimal(x) for x in result["e"][:order + 1]],
            "log_correction_coefficients": [decimal(x) for x in result["log_d"][:order + 1]],
            "inverse_delta_coefficients": [decimal(x) for x in result["inverse"][:order + 1]],
            "second_sector": {
                "A": decimal(result["A"]), "L": decimal(result["L"]),
                "L_over_K": decimal(result["L"] / K),
                "B_Puiseux": {str(j - 3): decimal(result["bjet"][j]) for j in range(2 * order + 1)},
                "relative_power_series_coefficients": [decimal(x) for x in result["bcorrections"][:order + 1]],
                "s_minus_2_contributions": [decimal(x) for x in result["defect_canceling_terms"]],
                "s_minus_2_sum": decimal(result["bjet"][1]),
                "normalization": "b_r ~ L*rho^(-r)*sqrt(r); B(s) begins A*s^(-3), and its s^(-2) coefficient cancels",
            },
            "inverse_convention": "lambda=-log(rho); m0=-W_-1(-2*lambda*(K/target)^2)/(2*lambda); m=m0+sum q_j/m0^j",
            "smooth_inverse_convention": "Numerically solve K*rho^(-x)/sqrt(x)*(1+sum_{j=1}^J d_j/x^j)=target near m0; this differs from truncating the formal Lambert-centered inverse",
            "self_checks": {"formal": formal, "numerical": "passed through supported order cap",
                            "normalized_residuals": {k: decimal(v) for k, v in result["residuals"].items()},
                            "empirical_double_run_scaled_difference": decimal(stability),
                            "numeric_Gamma_identity_max_difference": decimal(gamma_error),
                            "numeric_tolerance": decimal(tolerance),
                            "initial_exact_f_terms_checked": 12,
                            "strict_f_monotonicity_checked_through": EXACT_THRESHOLD_CAP,
                            "guards_survive_python_optimization": True},
            "coefficient_comparisons": comparisons,
            "inverse_examples": inverse_examples,
            "limitations": [
                "Decimal strings are approximations, not interval-certified constants or enclosures",
                "Tail/precision agreement is empirical; omitted tails have not been rigorously bounded here",
                "The full implementation cap is checked, but no finite run proves every arbitrary order",
                "No infinite asymptotic series convergence or effective remainder constant is claimed",
                "Lambert-W estimates and their ceilings are uncertified; only the displayed integer f comparisons settle thresholds",
                "The exact inverse examples concern f_m, not a general finite-(N,k) tree count outside its exact diagonal regime",
            ],
        }
    return output


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=3)
    parser.add_argument("--precision", type=int, default=60)
    parser.add_argument("--formal-only", action="store_true",
                        help="Run exact finite formal checks without importing mpmath")
    args = parser.parse_args(argv)
    try:
        output = formal_self_checks() if args.formal_only else numerical_diagnostics(args.order, args.precision)
    except (ValueError, RuntimeError) as exc:
        parser.exit(2, f"error: {exc}\n")
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
