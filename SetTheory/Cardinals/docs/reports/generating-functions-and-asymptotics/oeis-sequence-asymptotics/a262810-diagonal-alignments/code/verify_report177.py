#!/usr/bin/env python3
"""Report177 exact arithmetic verifier; Python standard library only.

Run: python3 verify_report177.py --output checks.json
Use --order J (J >= 3) to construct any requested fixed order.
No floating-point arithmetic or removable assertion statements are used.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json
from math import comb, factorial
from pathlib import Path
import subprocess
import sys


class VerificationError(RuntimeError):
    """A mathematical identity or invariant did not pass verification."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def natural(value, name, minimum=0):
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")


def positive_rational(value, name):
    if not isinstance(value, (int, Q)) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive integer or Fraction")
    return Q(value)


@dataclass(frozen=True)
class Poly:
    """Sparse exact Laurent polynomial, with a fixed number of variables."""
    dimensions: int
    terms: dict

    def __post_init__(self):
        natural(self.dimensions, "dimensions", 1)
        clean = {}
        for powers, coefficient in self.terms.items():
            if not isinstance(powers, tuple) or len(powers) != self.dimensions:
                raise ValueError("wrong exponent tuple dimensions")
            if any(not isinstance(p, int) or isinstance(p, bool) for p in powers):
                raise ValueError("exponents must be integers")
            if not isinstance(coefficient, (int, Q)) or isinstance(coefficient, bool):
                raise ValueError("coefficients must be exact integers or Fractions")
            coefficient = Q(coefficient)
            if coefficient:
                clean[powers] = coefficient
        object.__setattr__(self, "terms", clean)

    @classmethod
    def constant(cls, dimensions, coefficient):
        return cls(dimensions, {(0,) * dimensions: coefficient})

    @classmethod
    def monomial(cls, powers, coefficient=1):
        return cls(len(powers), {tuple(powers): coefficient})

    def compatible(self, other):
        if not isinstance(other, Poly):
            other = Poly.constant(self.dimensions, other)
        if other.dimensions != self.dimensions:
            raise ValueError("polynomial dimension mismatch")
        return other

    def __add__(self, other):
        other = self.compatible(other)
        terms = dict(self.terms)
        for powers, coefficient in other.terms.items():
            terms[powers] = terms.get(powers, Q(0)) + coefficient
        return Poly(self.dimensions, terms)

    __radd__ = __add__

    def __neg__(self):
        return self.scale(-1)

    def __sub__(self, other):
        return self + (-self.compatible(other))

    def __rsub__(self, other):
        return self.compatible(other) - self

    def __mul__(self, other):
        other = self.compatible(other)
        terms = {}
        for a, c in self.terms.items():
            for b, d in other.terms.items():
                powers = tuple(x + y for x, y in zip(a, b))
                terms[powers] = terms.get(powers, Q(0)) + c * d
        return Poly(self.dimensions, terms)

    __rmul__ = __mul__

    def scale(self, coefficient):
        if not isinstance(coefficient, (int, Q)) or isinstance(coefficient, bool):
            raise ValueError("scale must be rational")
        return Poly(self.dimensions, {p: c * coefficient for p, c in self.terms.items()})

    def __truediv__(self, coefficient):
        if not isinstance(coefficient, (int, Q)) or isinstance(coefficient, bool) or not coefficient:
            raise ValueError("divisor must be a nonzero rational")
        return self.scale(1 / Q(coefficient))

    def __pow__(self, exponent):
        natural(exponent, "exponent")
        answer = Poly.constant(self.dimensions, 1)
        base = self
        while exponent:
            if exponent % 2:
                answer = answer * base
            base = base * base
            exponent //= 2
        return answer

    def derivative(self, variable):
        natural(variable, "variable")
        if variable >= self.dimensions:
            raise ValueError("variable index outside polynomial")
        terms = {}
        for powers, coefficient in self.terms.items():
            if powers[variable]:
                new = list(powers)
                new[variable] -= 1
                terms[tuple(new)] = coefficient * powers[variable]
        return Poly(self.dimensions, terms)

    def at_one(self, variable):
        natural(variable, "variable")
        if variable >= self.dimensions or self.dimensions < 2:
            raise ValueError("at_one requires a valid variable in dimension >= 2")
        terms = {}
        for powers, coefficient in self.terms.items():
            new = powers[:variable] + powers[variable + 1:]
            terms[new] = terms.get(new, Q(0)) + coefficient
        return Poly(self.dimensions - 1, terms)

    def evaluate(self, values):
        if len(values) != self.dimensions:
            raise ValueError("evaluation dimension mismatch")
        if any(not isinstance(x, (int, Q)) or isinstance(x, bool) for x in values):
            raise ValueError("evaluation values must be rational")
        total = Q(0)
        for powers, coefficient in self.terms.items():
            term = coefficient
            for value, power in zip(values, powers):
                term *= Q(value) ** power
            total += term
        return total


def zero(dimensions):
    return Poly.constant(dimensions, 0)


def univariate(coefficients):
    return Poly(1, {(k,): c for k, c in coefficients.items()})


@lru_cache(maxsize=None, typed=True)
def bernoulli_numbers(order):
    """B_1=-1/2, from sum_{k=0}^m binom(m+1,k) B_k = 0."""
    natural(order, "Bernoulli order")
    result = [Q(1)]
    for m in range(1, order + 1):
        result.append(-sum(Q(comb(m + 1, k)) * result[k] for k in range(m)) / (m + 1))
    return tuple(result)


def bernoulli_polynomial_at(order, x):
    natural(order, "Bernoulli polynomial order")
    numbers = bernoulli_numbers(order)
    return sum((x ** (order - k)).scale(comb(order, k) * numbers[k])
               for k in range(order + 1))


def centered_B(order):
    """B_r(N), proven polynomial by Bernoulli summation, not fitted data."""
    natural(order, "centered power-sum order", 1)
    n = univariate({1: 1})
    plus, minus = (n + 1) / 2, (1 - n) / 2
    expression = n * (bernoulli_polynomial_at(2 * order + 1, plus)
                      - bernoulli_polynomial_at(2 * order + 1, minus))
    expression = expression / (2 * order * (2 * order + 1))
    require(all(power[0] % 2 == 0 for power in expression.terms),
            "centered Bernoulli sum has an odd power of n")
    return univariate({power[0] // 2: c for power, c in expression.terms.items()})


def central_moment(order):
    """Exact polynomial E[(Y-1)^order], Y ~ Gamma(N+1, rate N)."""
    natural(order, "central moment order")
    e = univariate({1: 1})
    raw = Poly.constant(1, 1)
    answer = zero(1)
    for j in range(order + 1):
        if j:
            raw = raw * (1 + j * e)
        answer += raw.scale((-1) ** (order - j) * comb(order, j))
    if order:
        require(all(k[0] >= (order + 1) // 2 for k in answer.terms),
                "central-moment valuation failed")
    return answer


def exponential_series(coefficients, order):
    """exp(sum_{k>=1} coefficients[k] t^k) through t^order."""
    natural(order, "exponential series order")
    if not coefficients or len(coefficients) <= order:
        raise ValueError("insufficient exponential-series coefficients")
    if coefficients[0].terms:
        raise ValueError("exponential-series constant term must be zero")
    dimensions = coefficients[0].dimensions
    answer = [Poly.constant(dimensions, 1)]
    for k in range(1, order + 1):
        answer.append(sum(j * coefficients[j] * answer[k - j]
                          for j in range(1, k + 1)) / k)
    return answer


def logarithmic_coefficients(R):
    if not R or R[0] != Poly.constant(1, 1):
        raise ValueError("logarithm requires univariate constant term one")
    L = [zero(1)]
    for k in range(1, len(R)):
        L.append(R[k] - sum((j * L[j] * R[k - j] for j in range(1, k)), zero(1)) / k)
    return L


def gamma_coefficients(order):
    """Construct R_j, L_j, C_j for any specified finite nonnegative order."""
    natural(order, "coefficient order")
    Bs = [centered_B(r) for r in range(1, order + 2)]
    g = [zero(2) for _ in range(order + 1)]  # variable order: z, y
    for r, b in enumerate(Bs, 1):
        for (degree,), coefficient in b.terms.items():
            k = 2 * r - degree
            require(k >= 0, "negative epsilon power in centered expansion")
            if k <= order:
                g[k] += Poly.monomial((2 * r, -2 * r), -coefficient)
    require(g[0] == Poly.monomial((2, -2), -Q(1, 24)),
            "wrong leading exp(-z^2/(24y^2)) term")
    g[0] = zero(2)  # this factor is handled by the twisted derivative
    H = exponential_series(g, order)
    moments = [central_moment(r) for r in range(2 * order + 1)]
    R = [zero(1) for _ in range(order + 1)]
    twist = Poly.monomial((2, -3), Q(1, 12))
    for q in range(order + 1):
        derivative = H[q]
        for r in range(2 * (order - q) + 1):
            at_one = derivative.at_one(1)
            for (k,), coefficient in moments[r].terms.items():
                if q + k <= order:
                    R[q + k] += at_one.scale(coefficient / factorial(r))
            derivative = derivative.derivative(1) + twist * derivative
    L = logarithmic_coefficients(R)
    numbers = bernoulli_numbers(2 * order + 2)
    C = [zero(1)]
    for j in range(1, order + 1):
        correction = -numbers[2 * j + 2] / ((2 * j + 2) * (2 * j + 1))
        if j % 2:
            r = (j + 1) // 2
            correction += numbers[2 * r] / (2 * r * (2 * r - 1))
        C.append(L[j] + correction)
    return Bs, R, L, C


def gaussian_average(p):
    """Integrate v-powers against an independent standard normal law."""
    if p.dimensions != 2:
        raise ValueError("Gaussian average requires variables z,v")
    terms = {}
    for (z_power, v_power), coefficient in p.terms.items():
        if v_power < 0:
            raise ValueError("Gaussian average cannot use negative v powers")
        if v_power % 2 == 0:
            moment = factorial(v_power) // (2 ** (v_power // 2) * factorial(v_power // 2))
            terms[(z_power,)] = terms.get((z_power,), Q(0)) + coefficient * moment
    return Poly(1, terms)


def gaussian_coefficients(order):
    """Independent t=N^-1/2 Laplace expansion, divided by gamma normalization."""
    natural(order, "Gaussian coefficient order")
    depth = 2 * order
    base = [zero(2) for _ in range(depth + 1)]  # variables z,v
    perturbation = [zero(2) for _ in range(depth + 1)]
    for k in range(3, depth + 3):
        base[k - 2] += Poly.monomial((0, k), Q((-1) ** (k + 1), k))
    for r in range(1, order + 2):
        for (degree,), coefficient in centered_B(r).terms.items():
            offset = 4 * r - 2 * degree
            require(offset >= 0, "negative t power in Laplace expansion")
            for ell in range(depth - offset + 1):
                perturbation[offset + ell] += Poly.monomial(
                    (2 * r, ell), -coefficient * (-1) ** ell * comb(2 * r + ell - 1, ell))
    perturbation[0] += Poly.monomial((2, 0), Q(1, 24))
    require(not perturbation[0].terms, "Gaussian leading constant failed to cancel")
    numerator = [gaussian_average(p) for p in exponential_series(
        [b + c for b, c in zip(base, perturbation)], depth)]
    denominator = [gaussian_average(p) for p in exponential_series(base, depth)]
    quotient = []
    for k in range(depth + 1):
        quotient.append(numerator[k] - sum(denominator[j] * quotient[k - j]
                                           for j in range(1, k + 1)))
    require(all(not quotient[k].terms for k in range(1, depth + 1, 2)),
            "odd t powers survived Gaussian averaging")
    return quotient[::2]


def forward_difference_values(values):
    if not values:
        raise ValueError("difference table must not be empty")
    row = list(values)
    result = []
    while row:
        result.append(row[0])
        row = [b - a for a, b in zip(row, row[1:])]
    return result


def difference_counts(n, weak=False):
    natural(n, "n", 1)
    if type(weak) is not bool:
        raise ValueError("weak must be a bool")
    return forward_difference_values([
        comb(m + n - 1 if weak else m, n) ** n for m in range(n * n + 1)])


def product_counts(n):
    """Positive binomial-basis multiplication, independent of differences."""
    natural(n, "n", 1)
    counts = {0: 1}
    for _ in range(n):
        new = {}
        for r, coefficient in counts.items():
            for j in range(max(r, n), r + n + 1):
                new[j] = new.get(j, 0) + coefficient * comb(j, r) * comb(r, r + n - j)
        counts = new
    return [counts.get(j, 0) for j in range(n * n + 1)]


def evaluate_counts(counts, u):
    u = positive_rational(u, "u")
    return sum(Q(c) * u ** j for j, c in enumerate(counts))


def exact_column_moments(counts, u):
    u = positive_rational(u, "u")
    weights = [Q(c) * u ** j for j, c in enumerate(counts)]
    total = sum(weights)
    if total <= 0:
        raise ValueError("moment distribution must have positive mass")
    mean = sum(j * weight for j, weight in enumerate(weights)) / total
    second = sum(j * j * weight for j, weight in enumerate(weights)) / total
    return total, mean, second - mean * mean


def exact_auxiliary_moments(n, u):
    """Inserted m and m^2 positive-series moments via separate differences."""
    natural(n, "n", 1)
    u = positive_rational(u, "u")
    inserted = []
    for power in range(3):
        degree = n * n + power
        coefficients = forward_difference_values([
            m ** power * comb(m, n) ** n for m in range(degree + 1)])
        inserted.append(evaluate_counts(coefficients, u))
    mean = inserted[1] / inserted[0]
    variance = inserted[2] / inserted[0] - mean * mean
    return mean, variance


def weak_convolution(counts, n):
    natural(n, "n", 1)
    if len(counts) != n * n + 1:
        raise ValueError("binary count vector has wrong length")
    if any(counts[k] for k in range(n)):
        raise ValueError("binary support below n prevents a polynomial shift")
    result = [0] * len(counts)
    for j, count in enumerate(counts):
        if count:
            for r in range(n):
                result[j - (n - 1) + r] += count * comb(n - 1, r)
    return result


def grid_distribution(n, weak=False):
    """Independent recursion over all allowed nonzero columns, for small n."""
    natural(n, "n", 1)
    if type(weak) is not bool:
        raise ValueError("weak must be a bool")

    @lru_cache(maxsize=None)
    def recurse(state):
        if not any(state):
            return (1,)
        result = [0] * (sum(state) + 1)
        choices = [range(v + 1) if weak else range(min(v, 1) + 1) for v in state]
        for column in product(*choices):
            if not any(column):
                continue
            child = recurse(tuple(v - c for v, c in zip(state, column)))
            for length, count in enumerate(child):
                result[length + 1] += count
        return tuple(result)

    return list(recurse((n,) * n))


def rational_tail_enclosure(n, u, exact, tolerance=Q(1, 10 ** 70)):
    """Geometric enclosure using the decreasing exact consecutive-term ratio."""
    natural(n, "n", 1)
    u = positive_rational(u, "u")
    exact = positive_rational(exact, "exact")
    tolerance = positive_rational(tolerance, "tolerance")
    rho = u / (1 + u)
    m = n
    term = rho ** n / (1 + u)
    partial = Q(0)
    while True:
        partial += term
        ratio = rho * Q(m + 1, m + 1 - n) ** n
        if ratio < 1:
            tail = term * ratio / (1 - ratio)
            if tail <= exact * tolerance:
                break
        term *= ratio
        m += 1
    require(partial <= exact <= partial + tail, "exact value outside rational enclosure")
    require(tail / exact <= tolerance, "relative rational tail exceeds tolerance")
    return {"last_m": m, "lower": str(partial), "upper": str(partial + tail),
            "tail_bound": str(tail), "relative_tail_bound": str(tail / exact),
            "tolerance": str(tolerance), "next_ratio": str(ratio),
            "encloses_exact": True}


def serialize_polynomial(p, names):
    if len(names) != p.dimensions:
        raise ValueError("polynomial serialization dimension mismatch")
    terms = []
    pretty = []
    for powers, coefficient in sorted(p.terms.items(), reverse=True):
        terms.append({"powers": list(powers), "coefficient": str(coefficient)})
        monomial = "*".join(name if power == 1 else f"{name}^{power}"
                            for name, power in zip(names, powers) if power)
        pretty.append(str(coefficient) + ("*" + monomial if monomial else ""))
    return {"variables": list(names), "terms": terms, "expression": " + ".join(pretty) or "0"}


def coefficient_checks(order):
    natural(order, "report order", 3)
    Bs, R, L, C = gamma_coefficients(order)
    expected_B = [
        univariate({2: Q(1, 24), 1: -Q(1, 24)}),
        univariate({3: Q(3, 960), 2: -Q(10, 960), 1: Q(7, 960)}),
        univariate({4: Q(3, 8064), 3: -Q(21, 8064), 2: Q(49, 8064), 1: -Q(31, 8064)}),
        univariate({5: Q(5, 92160), 4: -Q(60, 92160), 3: Q(294, 92160),
                    2: -Q(620, 92160), 1: Q(381, 92160)})]
    expected_L = [
        univariate({4: Q(1, 2880)}),
        univariate({6: -Q(1, 181440), 4: Q(693, 181440)}),
        univariate({8: Q(3, 29030400), 6: Q(3200, 29030400), 4: Q(493920, 29030400)})]
    expected_C = [expected_L[0] + Q(248, 2880), expected_L[1] - Q(144, 181440),
                  expected_L[2] - Q(63360, 29030400)]
    require(Bs[:4] == expected_B, "B1-B4 differ from displayed formulas")
    require(L[1:4] == expected_L, "L1-L3 differ from displayed formulas")
    require(C[1:4] == expected_C, "C1-C3 differ from displayed formulas")
    centered_direct_checks = 0
    for r, b in enumerate(Bs, 1):
        for n in range(1, 11):
            direct = Q(n, 2 * r) * sum((Q(n - 1, 2) - j) ** (2 * r) for j in range(n))
            require(b.evaluate([n * n]) == direct, "Bernoulli polynomial/direct sum mismatch")
            centered_direct_checks += 1
    independent_R = gaussian_coefficients(order)
    require(R == independent_R, "independent Gaussian and gamma coefficients disagree")
    return {"order": order, "B": [serialize_polynomial(p, ["N"]) for p in Bs],
            "R": [serialize_polynomial(p, ["z"]) for p in R],
            "L": [serialize_polynomial(p, ["z"]) for p in L[1:]],
            "C": [serialize_polynomial(p, ["z"]) for p in C[1:]],
            "B1_B4_L1_L3_C1_C3_match": True,
            "centered_direct_sum_checks": centered_direct_checks,
            "independent_Gaussian_R_matches_at_all_requested_orders": True,
            "Gaussian_R": [serialize_polynomial(p, ["z"]) for p in independent_R]}


def finite_checks():
    rows, tails, moments, grids = [], [], [], []
    for n in range(1, 11):
        binary = product_counts(n)
        require(binary == difference_counts(n), "positive product and difference counts disagree")
        require(all(c >= 0 for c in binary), "negative binary count")
        weak = weak_convolution(binary, n)
        require(weak == difference_counts(n, weak=True), "A316677 marked convolution failed")
        require(sum(weak) == 2 ** (n - 1) * sum(binary), "A316677 total count relation failed")
        require(all(c >= 0 for c in weak), "negative nonnegative-entry count")
        rows.append({"n": n, "A262810": str(sum(binary)), "A316677": str(sum(weak)),
                     "binary_column_counts": [str(x) for x in binary],
                     "nonnegative_column_counts": [str(x) for x in weak],
                     "positive_product_matches_differences": True,
                     "marked_A316677_convolution_matches": True})
        if n <= 3:
            require(grid_distribution(n) == binary, "binary grid recursion mismatch")
            require(grid_distribution(n, weak=True) == weak, "nonnegative grid recursion mismatch")
            grids.append({"n": n, "binary_full_distribution_matches": True,
                          "nonnegative_full_distribution_matches": True})
        for u in (Q(1, 2), Q(1), Q(2)):
            exact, mean, variance = exact_column_moments(binary, u)
            weak_exact, weak_mean, weak_variance = exact_column_moments(weak, u)
            require(weak_exact == ((1 + u) / u) ** (n - 1) * exact,
                    "marked nonnegative/binary value identity failed")
            require(weak_mean == mean - Q(n - 1) / (1 + u), "marked mean coupling failed")
            require(weak_variance == variance + Q(n - 1) * u / (1 + u) ** 2,
                    "marked variance coupling failed")
            auxiliary_mean, auxiliary_variance = exact_auxiliary_moments(n, u)
            require(mean == (auxiliary_mean - u) / (1 + u), "auxiliary M mean identity failed")
            require(variance == (auxiliary_variance - u * auxiliary_mean - u) / (1 + u) ** 2,
                    "auxiliary M variance identity failed")
            moments.append({"n": n, "u": str(u), "exact_A": str(exact), "mean": str(mean),
                            "variance": str(variance), "exact_Atilde": str(weak_exact),
                            "nonnegative_mean": str(weak_mean), "nonnegative_variance": str(weak_variance),
                            "auxiliary_M_mean": str(auxiliary_mean),
                            "auxiliary_M_variance": str(auxiliary_variance),
                            "marked_coupling_and_inserted_moment_identities_match": True})
            enclosure = rational_tail_enclosure(n, u, exact)
            enclosure.update({"n": n, "u": str(u), "exact_A": str(exact)})
            tails.append(enclosure)
    return {"counts": rows, "grid_recursions": grids, "exact_moments": moments,
            "rational_tail_enclosures": tails,
            "summary": {"count_pairs": len(rows), "full_grid_distribution_pairs": len(grids),
                        "marked_exact_moment_checks": len(moments), "rational_tail_enclosures": len(tails),
                        "every_relative_tail_at_most_1e_minus_70": True}}


def negative_guard_tests():
    """These deliberately invalid requests must fail in normal and -O Python."""
    # Populate both bool-equivalent integer keys before testing cache aliases.
    bernoulli_numbers(0)
    bernoulli_numbers(1)
    tests = [
        ("warm_cache_bool_false", ValueError, lambda: bernoulli_numbers(False)),
        ("warm_cache_bool_true", ValueError, lambda: bernoulli_numbers(True)),
        ("warm_cache_float_zero", ValueError, lambda: bernoulli_numbers(0.0)),
        ("warm_cache_float_one", ValueError, lambda: bernoulli_numbers(1.0)),
        ("warm_cache_fraction_zero", ValueError, lambda: bernoulli_numbers(Q(0))),
        ("warm_cache_fraction_one", ValueError, lambda: bernoulli_numbers(Q(1))),
        ("difference_weak_integer_zero", ValueError, lambda: difference_counts(1, weak=0)),
        ("difference_weak_integer_one", ValueError, lambda: difference_counts(1, weak=1)),
        ("difference_weak_float", ValueError, lambda: difference_counts(1, weak=1.0)),
        ("difference_weak_fraction", ValueError, lambda: difference_counts(1, weak=Q(1))),
        ("grid_weak_integer_zero", ValueError, lambda: grid_distribution(1, weak=0)),
        ("grid_weak_integer_one", ValueError, lambda: grid_distribution(1, weak=1)),
        ("grid_weak_float", ValueError, lambda: grid_distribution(1, weak=1.0)),
        ("grid_weak_fraction", ValueError, lambda: grid_distribution(1, weak=Q(1))),
        ("failure_guard", VerificationError, lambda: require(False, "deliberate guard test")),
        ("negative_n", ValueError, lambda: product_counts(-1)),
        ("zero_n", ValueError, lambda: difference_counts(0)),
        ("boolean_n", ValueError, lambda: product_counts(True)),
        ("noninteger_n", ValueError, lambda: difference_counts(Q(3, 2))),
        ("zero_u", ValueError, lambda: evaluate_counts([1], Q(0))),
        ("negative_u", ValueError, lambda: rational_tail_enclosure(1, Q(-1), Q(1))),
        ("float_u", ValueError, lambda: evaluate_counts([1], 0.5)),
        ("zero_tolerance", ValueError, lambda: rational_tail_enclosure(1, Q(1), Q(1), Q(0))),
        ("negative_exact", ValueError, lambda: rational_tail_enclosure(1, Q(1), Q(-1))),
        ("negative_coefficient_order", ValueError, lambda: gamma_coefficients(-1)),
        ("insufficient_report_order", ValueError, lambda: coefficient_checks(2)),
        ("negative_B_order", ValueError, lambda: centered_B(-1)),
        ("zero_B_order", ValueError, lambda: centered_B(0)),
        ("bad_poly_dimensions", ValueError, lambda: Poly(0, {})),
        ("bad_exponent_tuple", ValueError, lambda: Poly(2, {(1,): 1})),
        ("noninteger_exponent", ValueError, lambda: Poly(1, {(Q(1, 2),): 1})),
        ("float_coefficient", ValueError, lambda: Poly(1, {(0,): 0.1})),
        ("dimension_mismatch", ValueError, lambda: zero(1) + zero(2)),
        ("negative_poly_power", ValueError, lambda: zero(1) ** -1),
        ("zero_poly_divisor", ValueError, lambda: zero(1) / 0),
        ("invalid_derivative_variable", ValueError, lambda: zero(1).derivative(1)),
        ("bad_evaluation_dimension", ValueError, lambda: zero(1).evaluate([1, 2])),
        ("bad_exponential_constant", ValueError, lambda: exponential_series([Poly.constant(1, 1)], 0)),
        ("insufficient_exponential_series", ValueError, lambda: exponential_series([zero(1)], 1)),
        ("invalid_log_constant", ValueError, lambda: logarithmic_coefficients([zero(1)])),
        ("negative_gaussian_monomial", ValueError, lambda: gaussian_average(Poly.monomial((0, -2)))),
        ("empty_difference_table", ValueError, lambda: forward_difference_values([])),
        ("zero_moment_mass", ValueError, lambda: exact_column_moments([0], 1)),
        ("bad_convolution_length", ValueError, lambda: weak_convolution([0], 2)),
        ("bad_convolution_support", ValueError, lambda: weak_convolution([1, 0, 0, 0, 0], 2)),
    ]
    results = []
    for name, expected, call in tests:
        try:
            call()
        except expected:
            results.append({"test": name, "rejected": True, "exception": expected.__name__})
        else:
            raise VerificationError(f"negative guard test accepted invalid input: {name}")
    return {"status": "passed", "optimization_level": sys.flags.optimize,
            "count": len(results), "tests": results}


def verify_guard_modes():
    script = str(Path(__file__).resolve())
    modes = {}
    for name, switches in (("normal", ["-E"]), ("optimized", ["-E", "-O"])):
        process = subprocess.run([sys.executable] + switches + [script, "--guard-tests"],
                                 text=True, capture_output=True, check=False)
        require(process.returncode == 0, f"{name} guard subprocess failed: {process.stderr}")
        result = json.loads(process.stdout)
        require(result.get("status") == "passed", f"{name} guard tests did not pass")
        modes[name] = result
    require(modes["normal"]["optimization_level"] == 0, "normal subprocess was optimized")
    require(modes["optimized"]["optimization_level"] == 1, "-O subprocess was not optimized")
    require(modes["normal"]["tests"] == modes["optimized"]["tests"],
            "normal/-O negative guard results differ")
    return modes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write deterministic JSON here; default stdout")
    parser.add_argument("--order", type=int, default=3, help="fixed coefficient order, at least 3 (default 3)")
    parser.add_argument("--guard-tests", action="store_true", help="run negative guard tests only")
    args = parser.parse_args()
    try:
        if args.guard_tests:
            result = negative_guard_tests()
        else:
            natural(args.order, "--order", 3)
            coefficients = coefficient_checks(args.order)
            result = {"schema_version": 1, "report": "Report177", "status": "passed",
                      "arithmetic": "Python integers and fractions.Fraction only; no floating point",
                      "scope": "Exact finite identities and coefficients; analytic remainder proofs are in the report",
                      "coefficients": coefficients, "finite_checks": finite_checks(),
                      "negative_guard_tests": verify_guard_modes()}
        output = json.dumps(result, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            sys.stdout.write(output)
        else:
            args.output.write_text(output, encoding="utf-8")
    except (ValueError, VerificationError, OSError, json.JSONDecodeError) as error:
        sys.stderr.write(f"verification failed: {error}\n")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
