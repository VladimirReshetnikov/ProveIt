#!/usr/bin/env python3
"""Exact, standard-library coefficient checks for Report174.

Run ``python symbolic_checks.py`` or ``python -O symbolic_checks.py``.  Both
execute the same checks and emit deterministic JSON.  Importers may call
``run_symbolic_checks()``.  A failed identity raises VerificationError, rather
than relying on Python assertions, which disappear under optimization.

The algebraic checks are identities in formal indeterminates.  The independent
ordered-composition checks cover only the stated finite range of defects.  This
program does not establish analytic error bounds, compute the full king count
A(h,w), or treat a numerical marked-star sum as A(h,w).  In particular, the
critical base-sum constant and the additional Schur term are kept separate.

The mathematical identities are stated in Report174, in the marked-run,
supercritical-expansion and critical-window sections. There is no mandatory
computer-algebra dependency.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
import sys


class VerificationError(RuntimeError):
    """An exact verification failed, in ordinary or optimized Python."""


def _require(condition, message):
    if not condition:
        raise VerificationError(message)


# Univariate polynomials over Q, coefficients in increasing powers of q.
def _trim(a):
    result = list(map(Fraction, a))
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result) if result else (Fraction(0),)


def _uadd(a, b):
    return _trim(
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(max(len(a), len(b)))
    )


def _uscale(a, value):
    return _trim(c * value for c in a)


def _umul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return _trim(out)


def _udivmod(a, b):
    a, b = _trim(a), _trim(b)
    if b == (0,):
        raise ZeroDivisionError("zero polynomial divisor")
    quotient = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while a != (0,) and len(a) >= len(b):
        degree = len(a) - len(b)
        coefficient = a[-1] / b[-1]
        quotient[degree] += coefficient
        a = _uadd(a, (Fraction(0),) * degree + _uscale(b, -coefficient))
    return _trim(quotient), a


def _ugcd(a, b):
    while b != (0,):
        _, remainder = _udivmod(a, b)
        a, b = b, remainder
    return _uscale(a, 1 / a[-1]) if a != (0,) else (Fraction(1),)


def _uderivative(a):
    return _trim(i * a[i] for i in range(1, len(a)))


class _RationalQ:
    """Small reduced rational-function field Q(q); no floating-point arithmetic."""

    def __init__(self, numerator=(0,), denominator=(1,)):
        if isinstance(numerator, (int, Fraction)):
            numerator = (numerator,)
        if isinstance(denominator, (int, Fraction)):
            denominator = (denominator,)
        numerator, denominator = _trim(numerator), _trim(denominator)
        if denominator == (0,):
            raise ZeroDivisionError("zero rational-function denominator")
        if numerator == (0,):
            self.numerator, self.denominator = (Fraction(0),), (Fraction(1),)
            return
        common = _ugcd(numerator, denominator)
        numerator, rem_n = _udivmod(numerator, common)
        denominator, rem_d = _udivmod(denominator, common)
        _require(rem_n == (0,) and rem_d == (0,), "polynomial gcd division failed")
        scale = 1 / denominator[-1]
        self.numerator = _uscale(numerator, scale)
        self.denominator = _uscale(denominator, scale)

    @staticmethod
    def coerce(other):
        return other if isinstance(other, _RationalQ) else _RationalQ(other)

    def __add__(self, other):
        other = self.coerce(other)
        return _RationalQ(
            _uadd(_umul(self.numerator, other.denominator),
                  _umul(other.numerator, self.denominator)),
            _umul(self.denominator, other.denominator),
        )

    __radd__ = __add__

    def __neg__(self):
        return _RationalQ(_uscale(self.numerator, -1), self.denominator)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return _RationalQ(_umul(self.numerator, other.numerator),
                          _umul(self.denominator, other.denominator))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        return _RationalQ(_umul(self.numerator, other.denominator),
                          _umul(self.denominator, other.numerator))

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def __pow__(self, power):
        if type(power) is not int or power < 0:
            raise ValueError("rational-function powers must be nonnegative integers")
        out = _RationalQ(1)
        for _ in range(power):
            out *= self
        return out

    def __eq__(self, other):
        other = self.coerce(other)
        return (self.numerator == other.numerator
                and self.denominator == other.denominator)

    def derivative(self):
        return _RationalQ(
            _uadd(_umul(_uderivative(self.numerator), self.denominator),
                  _uscale(_umul(self.numerator,
                                _uderivative(self.denominator)), -1)),
            _umul(self.denominator, self.denominator),
        )

    def series(self, maximum):
        if type(maximum) is not int or maximum < 0:
            raise ValueError("series order must be a nonnegative integer")
        if self.denominator[0] == 0:
            raise ZeroDivisionError("Taylor expansion at a pole q=0")
        out = []
        for n in range(maximum + 1):
            value = self.numerator[n] if n < len(self.numerator) else Fraction(0)
            value -= sum(self.denominator[j] * out[n - j]
                         for j in range(1, min(n, len(self.denominator) - 1) + 1))
            out.append(value / self.denominator[0])
        return tuple(out)

    def json(self):
        return {
            "coefficient_order": "ascending powers of q",
            "numerator": [str(c) for c in self.numerator],
            "denominator": [str(c) for c in self.denominator],
        }


# A sparse Laurent-polynomial ring for the short multivariate formal checks.
# Negative powers are only needed to shift formal series and divide by L.
_VARIABLES = ("u", "e", "x", "L", "t", "d", "S", "T", "lambda", "I0")
_ZERO_MONOMIAL = (0,) * len(_VARIABLES)


class _P:
    def __init__(self, terms=None):
        self.terms = {monomial: Fraction(coefficient)
                      for monomial, coefficient in (terms or {}).items()
                      if coefficient != 0}

    @staticmethod
    def coerce(value):
        return value if isinstance(value, _P) else _P({_ZERO_MONOMIAL: value})

    def __add__(self, other):
        out = self.terms.copy()
        for monomial, coefficient in self.coerce(other).terms.items():
            out[monomial] = out.get(monomial, Fraction(0)) + coefficient
        return _P(out)

    __radd__ = __add__

    def __neg__(self):
        return _P({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        out = {}
        for a, x in self.terms.items():
            for b, y in self.coerce(other).terms.items():
                monomial = tuple(i + j for i, j in zip(a, b))
                out[monomial] = out.get(monomial, Fraction(0)) + x * y
        return _P(out)

    __rmul__ = __mul__

    def __truediv__(self, scalar):
        scalar = Fraction(scalar)
        if scalar == 0:
            raise ZeroDivisionError("zero scalar divisor")
        return self * (1 / scalar)

    def __pow__(self, power):
        if type(power) is not int or power < 0:
            raise ValueError("polynomial powers must be nonnegative integers")
        out = self.coerce(1)
        for _ in range(power):
            out *= self
        return out

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def coefficient(self, variable, power):
        index = _VARIABLES.index(variable)
        out = {}
        for monomial, coefficient in self.terms.items():
            if monomial[index] == power:
                reduced = list(monomial)
                reduced[index] = 0
                out[tuple(reduced)] = coefficient
        return _P(out)

    def truncate(self, variable, low, high):
        index = _VARIABLES.index(variable)
        return _P({m: c for m, c in self.terms.items() if low <= m[index] <= high})

    def derivative(self, variable):
        index = _VARIABLES.index(variable)
        out = {}
        for monomial, coefficient in self.terms.items():
            if monomial[index] != 0:
                reduced = list(monomial)
                reduced[index] -= 1
                out[tuple(reduced)] = coefficient * monomial[index]
        return _P(out)

    def at_zero(self, variable):
        index = _VARIABLES.index(variable)
        if any(m[index] < 0 for m in self.terms):
            raise ValueError("cannot substitute zero in a negative power")
        return self.coefficient(variable, 0)


def _v(variable, power=1):
    monomial = [0] * len(_VARIABLES)
    monomial[_VARIABLES.index(variable)] = power
    return _P({tuple(monomial): Fraction(1)})


def _delta(value, power=1):
    q = _RationalQ((0, 1))
    for _ in range(power):
        value = value - q * value.derivative()
    return value


def _spectral_taylor():
    u, d, S, T, lam = map(_v, ("u", "d", "S", "T", "lambda"))
    y = 1 + d * u + S * u**2 + (T - d * S) * u**3
    z = y - 1
    inverse = sum(((-z)**j for j in range(4)), _P.coerce(0))
    schur_rhs = 1 + d * u + S * u**2 * inverse + T * u**3 * inverse**2
    _require((y - schur_rhs).truncate("u", 0, 3) == 0,
             "Schur expansion of y failed through u^3")
    log_y = sum((((-1)**(j + 1)) * z**j / j for j in range(1, 4)),
                _P.coerce(0))
    shifted_exponent = (lam * log_y * _v("u", -1) - lam * d).truncate("u", 0, 2)
    expansion = (1 + shifted_exponent + shifted_exponent**2 / 2).truncate("u", 0, 2)
    coefficient_1 = expansion.coefficient("u", 1)
    coefficient_2 = expansion.coefficient("u", 2)
    _require(coefficient_1 == lam * (S - d**2 / 2), "supercritical c1 Taylor coefficient")
    _require(coefficient_2 == lam * (T - 2 * d * S + d**3 / 3)
             + lam**2 / 2 * (S - d**2 / 2)**2, "supercritical c2 Taylor coefficient")
    return coefficient_1, coefficient_2


def _weighted_taylor_polynomial(polynomial, moments):
    """Map d^a S^b T^c to (1-q d/dq)^a of its moment generating function."""
    out = {}
    permitted = {"d", "S", "T", "lambda"}
    for monomial, coefficient in polynomial.terms.items():
        powers = dict(zip(_VARIABLES, monomial))
        _require(all(power == 0 or variable in permitted
                     for variable, power in powers.items()), "unexpected Taylor variable")
        key = (powers["S"], powers["T"])
        _require(key in moments, "Taylor moment outside the implemented finite order")
        lam_power = powers["lambda"]
        out[lam_power] = out.get(lam_power, _RationalQ(0)) + coefficient * _delta(
            moments[key], powers["d"])
    return out


@lru_cache(maxsize=None)
def _compositions(total):
    if total == 0:
        return ((),)
    return tuple((first,) + tail for first in range(1, total + 1)
                 for tail in _compositions(total - first))


def _supercritical_checks(maximum):
    q = _RationalQ((0, 1))
    F = (1 - q) / (1 - 2 * q)
    h0 = q / (1 - q)
    h1 = q * h0.derivative()
    h2 = q * h1.derivative()
    _require(h1 == q / (1 - q)**2, "h1 geometric derivative")
    _require(h2 == q * (1 + q) / (1 - q)**3, "h2 geometric derivative")
    W = F**2
    WS = 2 * W * h1
    WSS = 2 * W * h2 + 2 * W * h1**2
    WT = 2 * W * (h2 + h0 * h1)
    c1_numerator = WS - _delta(W, 2) / 2
    c2_linear = WT - 2 * _delta(WS) + _delta(W, 3) / 3
    c2_quadratic = (WSS - _delta(WS, 2) + _delta(W, 4) / 4) / 2
    explicit_c1 = -(4 * q**4 - 40 * q**3 + 45 * q**2 - 12 * q + 1) / (
        2 * (1 - q)**2 * (1 - 2 * q)**2)
    _require(c1_numerator / W == explicit_c1, "c1 explicit rational identity")
    P6 = 8 * q**6 - 380 * q**5 + 690 * q**4 - 401 * q**3 + 69 * q**2 - 5 * q + 1
    P8 = (16 * q**8 - 976 * q**7 + 2920 * q**6 - 2940 * q**5
          + 977 * q**4 + 14 * q**3 + 2 * q**2 - 6 * q + 1)
    _require(c2_linear / W == P6 / (3 * (1 - q)**3 * (1 - 2 * q)**3),
             "c2 explicit P6 split numerator")
    _require(c2_quadratic / W == P8 / (8 * (1 - q)**4 * (1 - 2 * q)**4),
             "c2 explicit P8 split numerator")

    taylor_1, taylor_2 = _spectral_taylor()
    moments = {(0, 0): W, (1, 0): WS, (2, 0): WSS, (0, 1): WT}
    mapped_1 = _weighted_taylor_polynomial(taylor_1, moments)
    mapped_2 = _weighted_taylor_polynomial(taylor_2, moments)
    _require(set(mapped_1) == {1} and mapped_1[1] == c1_numerator,
             "c1 operator versus Taylor-weighted moment identity")
    _require(set(mapped_2) == {1, 2} and mapped_2[1] == c2_linear
             and mapped_2[2] == c2_quadratic,
             "c2 operator versus Taylor-weighted moment identity")

    generating_functions = {"W": W, "W_S": WS, "W_SS": WSS, "W_T": WT,
                            "c1_numerator_per_lambda": c1_numerator,
                            "c2_numerator_per_lambda": c2_linear,
                            "c2_numerator_per_lambda_squared": c2_quadratic}
    exact_series = {name: value.series(maximum)
                    for name, value in generating_functions.items()}
    checked_pairs = 0
    rows = []
    for k in range(maximum + 1):
        totals = {name: Fraction(0) for name in generating_functions}
        d = 1 - k
        for left_length in range(k + 1):
            for left in _compositions(left_length):
                for right in _compositions(k - left_length):
                    first_left = left[0] if left else 0
                    first_right = right[0] if right else 0
                    second_left = left[1] if len(left) > 1 else 0
                    second_right = right[1] if len(right) > 1 else 0
                    S = first_left + first_right
                    T = first_left**2 + second_left + first_right**2 + second_right
                    first_correction = S - Fraction(d**2, 2)
                    totals["W"] += 1
                    totals["W_S"] += S
                    totals["W_SS"] += S**2
                    totals["W_T"] += T
                    totals["c1_numerator_per_lambda"] += first_correction
                    totals["c2_numerator_per_lambda"] += T - 2 * d * S + Fraction(d**3, 3)
                    totals["c2_numerator_per_lambda_squared"] += first_correction**2 / 2
                    checked_pairs += 1
        for name, value in totals.items():
            _require(value == exact_series[name][k], "%s composition coefficient q^%s" % (name, k))
        multiplicity = 2 if k == 0 else (k + 3) * 2**(k - 1)
        _require(2 * totals["W"] == multiplicity, "marked-run multiplicity at defect %s" % k)
        expected_mean = Fraction(0) if k == 0 else Fraction(4 * k, k + 3)
        _require(totals["W_S"] / totals["W"] == expected_mean,
                 "mean first outward run sum at defect %s" % k)
        rows.append({"defect": k, "ordered_boundary_pairs": int(totals["W"]),
                     "mean_S": str(expected_mean)})
    return {
        "status": "pass",
        "exact_identity_checks": [
            "geometric first- and second-run moment rational functions",
            "Schur expansion of y through u^3",
            "logarithm and exponential through u^2 for w=lambda*h",
            "c1 operator equals the displayed explicit rational function",
            "c2 operator equals the Taylor-weighted moment rational function",
            "c2 equals the displayed P6/P8 explicit split rational expression",
        ],
        "c1": "-lambda*(4*q^4-40*q^3+45*q^2-12*q+1)/(2*(1-q)^2*(1-2*q)^2)",
        "c2": {
            "interpretation": "c2 = lambda*linear + lambda^2*quadratic",
            "explicit": "lambda*P6/[3*(1-q)^3*(1-2*q)^3]+lambda^2*P8/[8*(1-q)^4*(1-2*q)^4]",
            "P6": "8*q^6-380*q^5+690*q^4-401*q^3+69*q^2-5*q+1",
            "P8": "16*q^8-976*q^7+2920*q^6-2940*q^5+977*q^4+14*q^3+2*q^2-6*q+1",
            "linear": (c2_linear / W).json(),
            "quadratic": (c2_quadratic / W).json(),
        },
        "composition_check": {
            "scope": "finite coefficient check, not an all-defect proof",
            "maximum_defect_inclusive": maximum,
            "ordered_boundary_pairs_checked": checked_pairs,
            "series_checked": sorted(generating_functions),
            "rows": rows,
        },
    }


def _integrate_moments(polynomial, moments):
    maximum_power = max((m[_VARIABLES.index("x")] for m in polynomial.terms), default=0)
    _require(maximum_power < len(moments), "insufficient Gaussian moments")
    return sum((polynomial.coefficient("x", j) * moments[j]
                for j in range(maximum_power + 1)), _P.coerce(0))


def _critical_checks():
    e, x, L, t, I0 = map(_v, ("e", "x", "L", "t", "I0"))
    log_argument_minus_one = -x * e + e**2
    log_series = sum((((-1)**(j + 1)) * log_argument_minus_one**j / j
                      for j in range(1, 5)), _P.coerce(0))
    exponent = (L * x * _v("e", -1)
                + (L * _v("e", -2) + t * _v("e", -1)) * log_series)
    a = t + L * x - t * x**2 / 2 - L * x**3 / 3
    b = L * (-Fraction(1, 2) + x**2 - x**4 / 4) + t * (x - x**3 / 3)
    expected = L - t * x - L * x**2 / 2 + e * a + e**2 * b
    _require(exponent.truncate("e", -2, 2) == expected,
             "critical logarithm Taylor coefficients a and b")
    shifted = e * a + e**2 * b
    exponential = (1 + shifted + shifted**2 / 2).truncate("e", 0, 2)
    _require(exponential.coefficient("e", 1) == a
             and exponential.coefficient("e", 2) == b + a**2 / 2,
             "critical exponential Taylor coefficient b+a^2/2")

    moments = [I0, (1 - t * I0) * _v("L", -1)]
    for j in range(1, 7):
        moments.append((j * moments[j - 1] - t * moments[j]) * _v("L", -1))
    _require(L * moments[1] + t * moments[0] == 1, "Gaussian moment boundary recurrence")
    for j in range(1, 7):
        _require(L * moments[j + 1] + t * moments[j] == j * moments[j - 1],
                 "Gaussian moment recurrence at j=%s" % j)
    H = _integrate_moments(3 + x * a, moments)
    simple_H = 4 * moments[0] - moments[2] - t * moments[3] / 6
    _require(H == simple_H, "H recurrence simplification")
    _require(H.at_zero("t") == (4 - _v("L", -1)) * I0,
             "H(0) with I0(0)=sqrt(pi/(2L))")

    # z/(exp(z)-1), using four exact formal coefficients, gives B2=1/6.
    bernoulli_generator = _RationalQ(1, (1, Fraction(1, 2), Fraction(1, 6),
                                         Fraction(1, 24), Fraction(1, 120)))
    bernoulli_coefficients = bernoulli_generator.series(4)
    _require(bernoulli_coefficients == (1, Fraction(-1, 2), Fraction(1, 12),
                                       0, Fraction(-1, 720)), "Bernoulli generating coefficients")
    g0_polynomial = x
    g1_polynomial = 3 + x * a
    g0_at_zero = g0_polynomial.at_zero("x")
    # (p*f)'=(p'-(t+L*x)*p)*f, with f(0)=1.
    g0_prime_at_zero = (g0_polynomial.derivative("x")
                        - (t + L * x) * g0_polynomial).at_zero("x")
    g1_at_zero = g1_polynomial.at_zero("x")
    _require(g0_at_zero == 0 and g0_prime_at_zero == 1 and g1_at_zero == 3,
             "Euler-Maclaurin boundary data")
    endpoint = Fraction(2) * 2  # N_0=2 and exp(L)=2; this is exceptional.
    derivative_correction = -bernoulli_coefficients[2]
    half_boundary = Fraction(-3, 2)
    em_constant = endpoint + derivative_correction + half_boundary
    _require(em_constant == Fraction(29, 12), "Euler-Maclaurin constant 29/12")
    extended_endpoint = Fraction(3, 2) * 2
    _require(endpoint - extended_endpoint == 1,
             "exceptional k=0 multiplicity correction")

    g2_polynomial = 3 * a + x * (b + a**2 / 2)
    integrated_g2 = _integrate_moments(g2_polynomial, moments)
    G = moments[1]
    base_J = em_constant + integrated_g2
    schur_J = 4 * L * G
    full_J = base_J + schur_J
    center_base = Fraction(71, 12) - Fraction(8, 3) * _v("L", -1) + Fraction(2, 3) * _v("L", -2)
    center_full = Fraction(119, 12) - Fraction(8, 3) * _v("L", -1) + Fraction(2, 3) * _v("L", -2)
    _require(G.at_zero("t") == _v("L", -1), "G(0)=1/L")
    _require(base_J.at_zero("t") == center_base, "critical base-sum J(0)")
    _require(schur_J.at_zero("t") == 4, "critical Schur contribution at t=0")
    _require(full_J.at_zero("t") == center_full, "full critical J(0)")
    return {
        "status": "pass",
        "exact_identity_checks": [
            "logarithm coefficients a_t(x) and b_t(x) through e^2",
            "exponential coefficient b_t(x)+a_t(x)^2/2",
            "Gaussian moment recurrence through I7 and the two H formulas",
            "Bernoulli coefficients and Euler-Maclaurin endpoint constants",
            "J(0) including the separately identified Schur term",
        ],
        "formal_parameters": "L is a positive formal parameter; exp(L)=2 is used only for the endpoint factor",
        "G_at_zero": "1/L",
        "H_at_zero": "(4-1/L)*sqrt(pi/(2*L))",
        "euler_maclaurin_constant": {
            "exceptional_k0_endpoint": str(endpoint),
            "g0_derivative_term": str(derivative_correction),
            "g1_half_boundary_term": str(half_boundary),
            "sum": str(em_constant),
            "error_if_generic_multiplicity_is_used_at_k0": "-1",
        },
        "base_sum_constant_at_zero": "71/12-8/(3*L)+2/(3*L^2)",
        "schur_correction": "4*L*G(t)",
        "schur_correction_at_zero": "4",
        "full_J_at_zero": "119/12-8/(3*L)+2/(3*L^2)",
        "scope": "exact finite-order algebra and moment recurrence; analytic remainders are not machine-proved",
    }


def _guard_checks():
    """Exercise failure paths explicitly; these remain active with python -O."""
    guarded_operations = (
        ("verification condition", VerificationError, lambda: _require(False, "expected failure")),
        ("zero polynomial divisor", ZeroDivisionError, lambda: _udivmod((1,), (0,))),
        ("zero rational denominator", ZeroDivisionError, lambda: _RationalQ(1, 0)),
        ("division by zero rational function", ZeroDivisionError, lambda: _RationalQ(1) / 0),
        ("Taylor expansion at a pole", ZeroDivisionError, lambda: _RationalQ(1, (0, 1)).series(2)),
        ("negative Taylor order", ValueError, lambda: _RationalQ(1).series(-1)),
        ("negative polynomial power", ValueError, lambda: _v("x")**-1),
        ("zero scalar divisor", ZeroDivisionError, lambda: _v("x") / 0),
        ("zero substituted into negative power", ValueError, lambda: _v("L", -1).at_zero("L")),
    )
    passed = []
    for label, expected_exception, operation in guarded_operations:
        try:
            operation()
        except expected_exception:
            passed.append(label)
        else:
            raise VerificationError("guard did not reject: " + label)
    # A few nontrivial field identities catch normalization/derivative mistakes.
    q = _RationalQ((0, 1))
    _require((1 - q**2) / (1 - q) == 1 + q, "rational cancellation self-check")
    _require((q / (1 - q)).derivative() == 1 / (1 - q)**2,
             "rational derivative self-check")
    return {"status": "pass", "failure_paths_checked": passed,
            "optimization_safe": "all correctness checks use explicit exceptions"}


def run_symbolic_checks(max_defect=12) -> dict:
    """Return exact deterministic verification results, raising on any failure.

    max_defect bounds only the independent finite ordered-composition checks.
    The default covers defects 0,...,12; every rational identity is checked as
    an identity, rather than by substituting a finite set of q values.
    """
    if type(max_defect) is not int or not 0 <= max_defect <= 16:
        raise ValueError("max_defect must be an integer in [0,16]")
    guards = _guard_checks()
    return {
        "report": "Report174",
        "status": "pass",
        "arithmetic": "exact Fraction coefficients; no floating-point arithmetic or CAS",
        "guards": guards,
        "supercritical": _supercritical_checks(max_defect),
        "critical": _critical_checks(),
        "scope": {
            "full_count_A_computed": False,
            "numerical_star_sum_computed": False,
            "analytic_uniform_remainders_verified_by_program": False,
            "finite_composition_checks_are_not_all_order_proofs": True,
            "critical_coefficients_use_actual_t": "t=(w-log(2)*h)/sqrt(h)",
        },
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-defect", type=int, default=12,
                        help="finite composition check cutoff, inclusive (default: 12; maximum: 16)")
    args = parser.parse_args(argv)
    try:
        result = run_symbolic_checks(args.max_defect)
    except (VerificationError, ValueError, ZeroDivisionError) as exc:
        print(json.dumps({"report": "Report174", "status": "fail", "error": str(exc)},
                         sort_keys=True, indent=2))
        return 1
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
