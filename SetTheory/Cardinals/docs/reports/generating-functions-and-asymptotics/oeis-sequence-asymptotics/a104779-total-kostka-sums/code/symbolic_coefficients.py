#!/usr/bin/env python3
"""Finite, exact coefficient verification for the Kostka-sum article.

Run with no arguments. The only public computational entry point is
verify_symbolic_coefficients(), with a fixed finite verification scope.
This program writes JSON to stdout only; it reads no reference receipts.
Algebraic identities are checked here. Analytic remainders, global inversion,
and any finite-input rounding certificate require the article's proofs.
"""

import sys

sys.dont_write_bytecode = True
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(640)
if __name__ == "__main__" and len(sys.argv) != 1:
    raise SystemExit("symbolic_coefficients.py accepts no arguments")

import sympy as S

from common import emit, require


_ORDER = 8


def _zeroes(order):
    return [S.Integer(0) for _ in range(order + 1)]


def _mul(a, b, order):
    """Multiply two internally constructed truncated coefficient lists."""
    return [S.expand(sum(a[j] * b[k - j]
                         for j in range(max(0, k - len(b) + 1),
                                        min(k, len(a) - 1) + 1)))
            for k in range(order + 1)]


def _compose_zero_constant(coefficients, z, order):
    require(z[0] == 0, "Internal series composition requires zero constant")
    out = _zeroes(order)
    power = _zeroes(order)
    power[0] = S.Integer(1)
    for c in coefficients:
        out = [S.expand(out[k] + c * power[k]) for k in range(order + 1)]
        power = _mul(power, z, order)
    return out


def _exp_series(b, order):
    require(b[0] == 0, "Internal exponential requires zero constant")
    a = [S.Integer(1)]
    for n in range(1, order + 1):
        a.append(S.expand(sum(k * b[k] * a[n - k]
                              for k in range(1, n + 1)) / n))
    return a


def _log_series(a, order):
    require(a[0] == 1, "Internal logarithm requires unit constant")
    b = [S.Integer(0)]
    for n in range(1, order + 1):
        b.append(S.expand(a[n] - sum(k * b[k] * a[n - k]
                                    for k in range(1, n)) * S.Rational(1, n)))
    return b


def _check(actual, expected, label, checks):
    require(not S.sympify(actual).has(S.Float) and not S.sympify(expected).has(S.Float),
            "Inexact floating-point value in identity: " + label)
    require(S.cancel(S.expand(actual - expected)) == 0,
            "Exact symbolic identity failed: " + label)
    checks.append(label)


def _check_list(actual, expected, label, checks):
    require(len(actual) == len(expected), "Internal coefficient length mismatch")
    for k, (left, right) in enumerate(zip(actual, expected)):
        _check(left, right, "%s[%d]" % (label, k), checks)


def _strings(values):
    return [str(S.factor(value)) for value in values]


def _saddle(checks):
    u = S.Symbol("u")
    p = [S.Integer(0)] + [S.expand(
        (S.I * u) ** (m + 1) / S.factorial(m + 1)
        + 2 ** (m + 1) * (S.I * u) ** (m + 2) / S.factorial(m + 2))
        for m in range(1, _ORDER + 1)]
    q = [S.Integer(1)]
    c = [S.Integer(1)]
    for n in range(1, _ORDER + 1):
        q.append(S.expand(sum(m * p[m] * q[n - m]
                              for m in range(1, n + 1)) / n))
        integral = S.Integer(0)
        for (k,), coefficient in S.Poly(q[n], u).terms():
            if k == 0:
                integral += coefficient
            elif k % 2 == 0:
                integral += coefficient * S.factorial2(k - 1) / 2 ** (k // 2)
        c.append(S.cancel(integral))
    expected = [S.Rational(x) for x in (
        "1", "-1/4", "-7/96", "77/384", "-3989/18432", "3275/24576",
        "1076179/26542080", "-27974437/106168320", "4497152381/10192158720")]
    _check_list(c, expected, "saddle_c", checks)
    return c


def _involution(c, checks):
    # h = 1/r = t(sqrt(1+t^2/4)+t/2), truncated at t^8.
    h = _zeroes(_ORDER)
    h[2] = S.Rational(1, 2)
    for k in range(4):
        h[2 * k + 1] = S.binomial(S.Rational(1, 2), k) / 4 ** k
    log_c = _log_series(_compose_zero_constant(c, h, _ORDER), _ORDER)

    # R/(2t) + asinh(t/2)/t^2 + asinh(t/2) - 1/t + 1/4.
    # The poles and constants cancel exactly; all remaining terms are odd.
    elementary = _zeroes(_ORDER)
    for k in range(1, 5):
        elementary[2 * k - 1] += S.binomial(S.Rational(1, 2), k) / (2 * 4 ** k)
        elementary[2 * k - 1] += (-1) ** k * S.binomial(2 * k, k) / (
            S.Integer(2) ** (4 * k + 1) * (2 * k + 1))
    for k in range(4):
        elementary[2 * k + 1] += (-1) ** k * S.binomial(2 * k, k) / (
            S.Integer(2) ** (4 * k + 1) * (2 * k + 1))
    stirling = _zeroes(_ORDER)
    for k in (1, 2):
        stirling[4 * k - 2] = S.bernoulli(2 * k) / (2 * k * (2 * k - 1))
    b = [S.expand(elementary[k] + stirling[k] + log_c[k])
         for k in range(_ORDER + 1)]
    expected_b = [S.Rational(x) for x in (
        "0", "7/24", "-7/48", "37/1920", "5/128", "-5879/107520",
        "43/1440", "40429/2064384", "-235/4096")]
    _check_list(b, expected_b, "log_I_b", checks)
    alpha = _exp_series(b, _ORDER)
    expected_alpha = [S.Rational(x) for x in (
        "1", "7/24", "-119/1152", "-7933/414720", "1967381/39813120",
        "-57200419/1337720832", "6340449533/687970713600",
        "3840755481827/115579079884800", "-1165106617342939/22191183337881600")]
    _check_list(alpha, expected_alpha, "multiplicative_alpha", checks)
    return b, alpha


def _shift_and_support(b, alpha, checks):
    s = S.Symbol("s")
    d = _zeroes(6)
    # (t^-2-s)log(1-s t^2)/2+s/2, with its constant cancelled.
    for k in range(1, 4):
        d[2 * k] += s ** (k + 1) / (2 * k * (k + 1))
    # (sqrt(1-s t^2)-1)/t.
    for k in range(1, 4):
        d[2 * k - 1] += S.binomial(S.Rational(1, 2), k) * (-s) ** k
    # b(t/sqrt(1-s t^2))-b(t); the k=0 terms cancel.
    for j in range(1, 7):
        for k in range(1, (6 - j) // 2 + 1):
            d[j + 2 * k] += b[j] * S.binomial(-S.Rational(j, 2), k) * (-s) ** k
    expected_d = [S.Integer(0), -s / 2, s ** 2 / 4,
                  -s ** 2 / 8 + 7 * s / 48,
                  s ** 3 / 12 - 7 * s / 48,
                  -s ** 3 / 16 + 7 * s ** 2 / 64 + 37 * s / 1280,
                  s ** 4 / 24 - 7 * s ** 2 / 48 + 5 * s / 64]
    _check_list(d, expected_d, "fixed_shift_log", checks)
    ratio = _exp_series(d, 5)
    expected_ratio = [S.Integer(1), -s / 2, 3 * s ** 2 / 8,
        (-7 * s ** 3 - 6 * s ** 2 + 7 * s) / 48,
        (25 * s ** 4 + 56 * s ** 3 - 28 * s ** 2 - 56 * s) / 384,
        (-81 * s ** 5 - 340 * s ** 4 - 30 * s ** 3 + 700 * s ** 2 + 111 * s) / 3840]
    _check_list(ratio, expected_ratio, "fixed_shift_ratio", checks)

    h3, h4, h5, h6 = S.symbols("H3 H4 H5 H6")
    multiplier = _zeroes(6)
    multiplier[0] = S.Integer(1)
    for j, h in ((3, h3), (4, h4), (5, h5), (6, h6)):
        for k in range(7 - j):
            multiplier[j + k] += h * ratio[k].subs(s, j)
    expected_multiplier = [1, 0, 0, h3, h4 - 3 * h3 / 2,
        h5 - 2 * h4 + 27 * h3 / 8,
        h6 - 5 * h5 / 2 + 6 * h4 - 37 * h3 / 8]
    _check_list(multiplier, expected_multiplier, "generic_H_multiplier", checks)
    a_coefficients = _mul(alpha, multiplier, 6)
    expected_a = [1, S.Rational(7, 24), -S.Rational(119, 1152),
        h3 - S.Rational(7933, 414720),
        h4 - 29 * h3 / 24 + S.Rational(1967381, 39813120),
        h5 - 41 * h4 / 24 + 3265 * h3 / 1152 - S.Rational(57200419, 1337720832),
        h6 - 53 * h5 / 24 + 6121 * h4 / 1152 - 1453513 * h3 / 414720
        + S.Rational(6340449533, 687970713600)]
    _check_list(a_coefficients, expected_a, "generic_H_times_alpha", checks)
    log_multiplier = _log_series(multiplier, 6)
    log_a = [S.expand(b[k] + log_multiplier[k]) for k in range(7)]
    expected_log_a = [0, S.Rational(7, 24), -S.Rational(7, 48),
        h3 + S.Rational(37, 1920), h4 - 3 * h3 / 2 + S.Rational(5, 128),
        h5 - 2 * h4 + 27 * h3 / 8 - S.Rational(5879, 107520),
        h6 - 5 * h5 / 2 + 6 * h4 - 37 * h3 / 8 - h3 ** 2 / 2 + S.Rational(43, 1440)]
    _check_list(log_a, expected_log_a, "generic_H_log_correction", checks)
    return {"shift_log_t0_to_t6": _strings(d),
            "shift_ratio_t0_to_t5": _strings(ratio),
            "relative_to_C_I_t0_to_t6": _strings(multiplier),
            "relative_to_C_B_t0_to_t6": _strings(a_coefficients),
            "log_a_correction_t0_to_t6": _strings(log_a)}, a_coefficients


def _inverse(checks):
    ell, c0, b1, b2, b3 = S.symbols("ell c0 b1 b2 b3")
    variables = S.symbols("A B C D E")
    # v=x^-1/2; delta=A/v+B+C*v+D*v^2+E*v^3; z=delta*v^2.
    z = [S.Integer(0)] + list(variables)
    phi = _compose_zero_constant(
        [S.Integer(0), S.Integer(0)] +
        [S.Rational((-1) ** k, k * (k - 1)) for k in range(2, 6)], z, 5)
    square_root = _compose_zero_constant(
        [S.binomial(S.Rational(1, 2), k) for k in range(6)], z, 5)
    inverse_roots = {
        j: _compose_zero_constant(
            [S.binomial(-S.Rational(j, 2), k) for k in range(6)], z, 5)
        for j in (1, 2, 3)}
    residual = []
    for degree in range(-1, 4):
        coefficient = ell * variables[degree + 1] / 2
        coefficient += phi[degree + 2] / 2 + square_root[degree + 1]
        if degree == 0:
            coefficient += c0
        for j, bj in ((1, b1), (2, b2), (3, b3)):
            if degree >= j:
                coefficient += bj * inverse_roots[j][degree - j]
        residual.append(S.expand(coefficient))
    expected = [
        -2 / ell,
        -2 * (c0 * ell ** 2 - ell + 1) / ell ** 3,
        -(6 * b1 * ell ** 4 - 6 * c0 * ell ** 3 + 12 * c0 * ell ** 2
          + 3 * ell ** 2 - 14 * ell + 12) / (3 * ell ** 5),
        -2 * (6 * b1 * ell ** 4 + 3 * b2 * ell ** 6 + 3 * c0 ** 2 * ell ** 4
              - 12 * c0 * ell ** 3 + 18 * c0 * ell ** 2
              + 6 * ell ** 2 - 20 * ell + 15) / (3 * ell ** 7),
        -(120 * b1 * c0 * ell ** 7 + 240 * b1 * c0 * ell ** 6
          - 60 * b1 * ell ** 6 - 120 * b1 * ell ** 5 + 720 * b1 * ell ** 4
          + 120 * b2 * ell ** 7 + 240 * b2 * ell ** 6 + 120 * b3 * ell ** 8
          - 60 * c0 ** 2 * ell ** 6 - 120 * c0 ** 2 * ell ** 5
          + 720 * c0 ** 2 * ell ** 4 + 60 * c0 * ell ** 5
          + 80 * c0 * ell ** 4 - 2000 * c0 * ell ** 3 + 2400 * c0 * ell ** 2
          - 15 * ell ** 4 - 4 * ell ** 3 + 940 * ell ** 2 - 2520 * ell + 1680)
        / (60 * ell ** 9)]
    solved = {}
    for coefficient, variable, target in zip(residual, variables, expected):
        equation = S.cancel(coefficient.subs(solved))
        _check(S.diff(equation, variable), ell / 2,
               "inverse_linear_factor_" + str(variable), checks)
        derived = S.cancel(-2 * equation.subs(variable, 0) / ell)
        _check(derived, target, "inverse_uncentered_" + str(variable), checks)
        solved[variable] = derived
    # Independent final substitution checks every claimed vanished residual.
    replacement = dict(zip(variables, expected))
    for degree, coefficient in zip(range(-1, 4), residual):
        _check(coefficient.subs(replacement), 0,
               "inverse_uncentered_residual_v^" + str(degree), checks)
    centered = [
        -2 / ell,
        2 / ell ** 2 - 2 / ell ** 3,
        -2 * b1 / ell - 1 / ell ** 3 + S.Rational(14, 3) / ell ** 4 - 4 / ell ** 5,
        -2 * b2 / ell - 4 * b1 / ell ** 3 - 4 / ell ** 5
        + S.Rational(40, 3) / ell ** 6 - 10 / ell ** 7]
    for variable, target, value in zip(variables, centered, expected):
        _check(value.subs(c0, 0), target, "inverse_centered_" + str(variable), checks)
    return {"coefficient_order": ["A", "B", "C", "D", "E"],
            "ansatz": "n=x+A*sqrt(x)+B+C/sqrt(x)+D/x+E/x^(3/2)",
            "ell": "log(x), assumed nonzero for these rational identities",
            "uncentered": _strings(expected),
            "centered_A_to_D": _strings(centered),
            "residual_powers_checked": [-1, 0, 1, 2, 3]}


def _companions(checks):
    j2, j3, j4 = S.symbols("J2 J3 J4")
    shifts = {}
    for s in (2, 3, 4):
        series = [S.Integer(1)] + _zeroes(3)
        for j in range(s):
            series = _mul(series, [S.Integer(j) ** k for k in range(5)], 4)
        shifts[s] = [S.Integer(0)] * s + series[:5 - s]
    expansion = [S.Integer(1)] + [S.Integer(0)] * 4
    for s, js in ((2, j2), (3, j3), (4, j4)):
        expansion = [S.expand(expansion[k] + js * shifts[s][k]) for k in range(5)]
    expected = [1, 0, j2, j2 + j3, j2 + 3 * j3 + j4]
    _check_list(expansion, expected, "factorial_companion_relative", checks)
    log_correction = _log_series(expansion, 4)
    log_correction[1] += S.Rational(1, 12)
    log_correction[3] -= S.Rational(1, 360)
    expected_log = [0, S.Rational(1, 12), j2, j2 + j3 - S.Rational(1, 360),
                    j2 + 3 * j3 + j4 - j2 ** 2 / 2]
    _check_list(log_correction, expected_log, "factorial_companion_log", checks)

    eta2, h3, h4, d4 = S.symbols("eta2 H3 H4 D4")
    plus = [2 * eta2 ** 2, 3 * h3 ** 2, d4 ** 2 / 4 + 2 * h4 ** 2]
    minus = [-2 * eta2 ** 2, 3 * h3 ** 2, -d4 ** 2 / 4 + 2 * h4 ** 2]
    # Factors 2,3,4,8 are z_(2), z_(3), z_(4), z_(2,2).
    for sign, targets in ((1, plus), (-1, minus)):
        actual = [sign * 2 * eta2 ** 2, 3 * h3 ** 2,
                  sign * 4 * (d4 / 4) ** 2 + 8 * (h4 / 2) ** 2]
        _check_list(actual, targets, "companion_J_%+d" % sign, checks)
    substitutions_plus = dict(zip((j2, j3, j4), plus))
    substitutions_minus = dict(zip((j2, j3, j4), minus))
    log_ratio = [S.expand(value.subs(substitutions_plus) - value.subs(substitutions_minus))
                 for value in _log_series(expansion, 4)]
    ratio = _exp_series(log_ratio, 3)
    _check_list(ratio, [1, 0, 4 * eta2 ** 2, 4 * eta2 ** 2],
                "companion_positive_over_binary", checks)
    for k in range(4):
        difference = expansion[k].subs(substitutions_plus) - expansion[k].subs(substitutions_minus)
        _check(difference, 4 * eta2 ** 2 * shifts[2][k],
               "companion_difference_vs_factorial_shift[%d]" % k, checks)

    ell, d0 = S.symbols("ell d0")
    delta = -S.Rational(1, 2) - d0 / ell
    _check(ell * delta + ell / 2 + d0, 0, "companion_first_inverse_constant", checks)
    residual_1 = S.expand(delta ** 2 / 2 + delta / 2 + S.Rational(1, 12))
    _check(residual_1, d0 ** 2 / (2 * ell ** 2) - S.Rational(1, 24),
           "companion_first_inverse_residual_1/x", checks)
    return {"relative_factorial_n0_to_nminus4": _strings(expansion),
            "log_correction_n0_to_nminus4": _strings(log_correction),
            "J2_J3_J4_plus": _strings(plus), "J2_J3_J4_minus": _strings(minus),
            "positive_over_binary_n0_to_nminus3": _strings(ratio),
            "first_inverse_delta": str(delta),
            "first_inverse_residual_coefficient_1/x": str(S.factor(residual_1))}


def _half_axis_sectors(alpha, kostka_coefficients, checks):
    """Check the fixed Gaussian-moment sector algebra, without quadrature."""
    order = 10
    y = S.Symbol("y")
    q = [S.Integer(0)] + [
        S.Rational((-1) ** (m + 1), m + 2) * y ** (m + 2)
        for m in range(1, order + 1)]
    polynomials = [S.Integer(1)]
    for j in range(1, order + 1):
        polynomials.append(S.expand(sum(
            m * q[m] * polynomials[j - m] for m in range(1, j + 1)) / j))
        _check(q[j].subs(y, -y), (-1) ** j * q[j],
               "sector_exponent_parity_q%d" % j, checks)
    # A second, inverse series operation checks the polynomial recursion.
    _check_list(_log_series(polynomials, order), q, "sector_log_of_Q", checks)
    for j, polynomial in enumerate(polynomials):
        _check(polynomial.subs(y, -y), (-1) ** j * polynomial,
               "sector_polynomial_parity_Q%d" % j, checks)

    # Exact moments of a Gaussian with mean sigma/2 and variance 1/2.
    # The largest polynomial degree here is 3*order = 30.
    moments = {}
    beta = {}
    for sigma in (1, -1):
        moments[sigma] = [S.expand(sum(
            S.binomial(d, 2 * k) * S.Rational(sigma, 2) ** (d - 2 * k)
            * S.factorial2(2 * k - 1) / 2 ** k
            for k in range(d // 2 + 1))) for d in range(3 * order + 1)]
        _check(moments[sigma][0], 1, "sector_moment_%+d_0" % sigma, checks)
        _check(moments[sigma][1], S.Rational(sigma, 2),
               "sector_moment_%+d_1" % sigma, checks)
        for d in range(1, 3 * order):
            _check(moments[sigma][d + 1],
                   S.Rational(sigma, 2) * moments[sigma][d]
                   + S.Rational(d, 2) * moments[sigma][d - 1],
                   "sector_moment_recurrence_%+d_%d" % (sigma, d), checks)
        beta[sigma] = [S.expand(sum(
            coefficient * moments[sigma][monomial[0]]
            for monomial, coefficient in S.Poly(polynomial, y).terms()))
            for polynomial in polynomials]
    for j in range(order + 1):
        _check(beta[-1][j], (-1) ** j * beta[1][j],
               "sector_beta_parity_%d" % j, checks)
    # The alpha values came independently from the circular involution saddle.
    _check_list(beta[1][:9], alpha, "sector_beta_matches_involution_alpha", checks)

    # Compute both signs separately from the half-axis composition formula.
    # E_s has removable apparent poles. Its even coefficients do not depend
    # on sigma, while its odd coefficients acquire a factor sigma.
    hs = {0: S.Integer(1), **dict(zip(range(3, 7), S.symbols("H3 H4 H5 H6")))}
    sector = {}
    for sigma in (1, -1):
        result = _zeroes(6)
        for support, h in hs.items():
            local_order = 6 - support
            exponent = _zeroes(local_order)
            for k in range(1, local_order // 2 + 1):
                exponent[2 * k] += S.Rational(1, 2 * k * (k + 1)) * support ** (k + 1)
            for k in range(1, (local_order + 1) // 2 + 1):
                exponent[2 * k - 1] += (sigma * S.binomial(S.Rational(1, 2), k)
                                        * (-support) ** k)
            shifted = _zeroes(local_order)
            for j in range(local_order + 1):
                for k in range((local_order - j) // 2 + 1):
                    shifted[j + 2 * k] += (beta[sigma][j]
                        * S.binomial(-S.Rational(j, 2), k) * (-support) ** k)
            local = _mul(_exp_series(exponent, local_order), shifted, local_order)
            for j, coefficient in enumerate(local):
                result[support + j] += h * sigma ** support * coefficient
        sector[sigma] = [S.expand(value) for value in result]
    _check_list(sector[1], kostka_coefficients, "sector_Kostka_plus_matches_existing", checks)
    _check_list(sector[-1], [(-1) ** j * value
                            for j, value in enumerate(kostka_coefficients)],
                "sector_Kostka_minus_matches_existing", checks)
    _check_list(sector[-1], [(-1) ** j * value for j, value in enumerate(sector[1])],
                "sector_Kostka_composition_parity", checks)
    log_plus = _log_series(sector[1], 2)
    log_minus = _log_series(sector[-1], 2)
    relative_sector = _exp_series([log_minus[j] - log_plus[j] for j in range(3)], 2)
    _check_list(relative_sector, [1, -S.Rational(7, 12), S.Rational(49, 288)],
                "sector_ratio_after_exp_minus_2sqrt_n", checks)
    return {
        "scope": "Finite exact polynomial and Gaussian-moment algebra; no numerical integration or analytic remainder certification",
        "q_m": "(-1)^(m+1)*y^(m+2)/(m+2), m=1,...,10",
        "Q_recursion": "Q_0=1; Q_j=(1/j)*sum(m*q_m*Q_(j-m), m=1,...,j)",
        "gaussian_expectation": "E_sigma[y^d]=sum(binomial(d,2*k)*(sigma/2)^(d-2*k)*(2*k-1)!!/2^k, k=0,...,floor(d/2))",
        "gaussian_moment_degrees_checked": [0, 30],
        "beta_plus_0_to_10": _strings(beta[1]),
        "beta_minus_0_to_10": _strings(beta[-1]),
        "beta_parity_verified_through": order,
        "independent_involution_alpha_match_through": 8,
        "Kostka_plus_0_to_6": _strings(sector[1]),
        "Kostka_minus_0_to_6": _strings(sector[-1]),
        "Kostka_parity_verified_through": 6,
        "A_minus_over_A_plus_after_exp_minus_2sqrt_n_t0_to_t2": _strings(relative_sector)}


def verify_symbolic_coefficients():
    """Return a deterministic receipt for the fixed exact identities above."""
    checks = []
    c = _saddle(checks)
    b, alpha = _involution(c, checks)
    shift_and_support, kostka_coefficients = _shift_and_support(b, alpha, checks)
    inverse = _inverse(checks)
    companion = _companions(checks)
    sectors = _half_axis_sectors(alpha, kostka_coefficients, checks)
    require(len(checks) == len(set(checks)), "Duplicate verification labels")
    return {"status": "PASS", "arithmetic": "exact SymPy rational and symbolic algebra",
            "scope": "Finite coefficient identities only; no analytic remainder or finite-input rounding proof",
            "orders": {"saddle_c": [0, 8], "log_I_b": [1, 8], "multiplicative_alpha": [0, 8],
                       "fixed_shift_log": [0, 6], "fixed_shift_ratio": [0, 5],
                       "generic_H_corrections": [0, 6], "inverse_uncentered": "A through E",
                       "inverse_centered": "A through D", "companion_factorial": [0, 4],
                       "half_axis_beta": [0, 10], "half_axis_Kostka": [0, 6]},
            "saddle_c0_to_c8": _strings(c), "log_I_b1_to_b8": _strings(b[1:]),
            "alpha0_to_alpha8": _strings(alpha), "shift_and_support": shift_and_support,
            "inverse": inverse, "companion": companion, "half_axis_sectors": sectors,
            "identities_checked": len(checks), "checks": checks}


def main():
    require(len(sys.argv) == 1, "symbolic_coefficients.py accepts no arguments")
    emit(verify_symbolic_coefficients())


if __name__ == "__main__":
    main()
