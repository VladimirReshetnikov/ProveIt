#!/usr/bin/env python3
"""Fresh exact companion for Report151 (Python 3.10+).

x marks half-length; q marks pairs of fixed points.  All combinatorial and
profile-table arithmetic is exact.  mpmath is imported only for explicitly
labelled numerical diagnostics, which do not certify uniform remainder bounds.
This file neither imports nor executes any predecessor/research companion.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, factorial


def _natural(n: int, name: str = "n") -> int:
    if isinstance(n, bool) or not isinstance(n, int) or n < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return n


def _class(s: str) -> str:
    if s not in ("E", "R"):
        raise ValueError("class must be 'E' or 'R'")
    return s


def _parity(epsilon: int) -> int:
    if epsilon not in (-1, 1):
        raise ValueError("epsilon must be -1 or 1")
    return epsilon


@lru_cache(None)
def catalan(n: int) -> int:
    _natural(n)
    return comb(2 * n, n) // (n + 1)


def _trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p or [0])


def polynomial_add(a, b):
    out = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return _trim(out)


def polynomial_multiply(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] += u * v
    return _trim(out)


def polynomial_value(p, x):
    value = 0
    for coefficient in reversed(p):
        value = value * x + coefficient
    return value


def recurrence_polynomials(max_m: int):
    """Return integer coefficient tuples (E[0..m], R[0..m]).

    Direct triangular extraction from E=C(x^2)(1+xqR), R=1+xER.
    This routine does not call a fixed-r formula.
    """
    _natural(max_m, "max_m")
    e, r = [(1,)], [(1,)]
    for m in range(1, max_m + 1):
        em = (catalan(m // 2),) if m % 2 == 0 else (0,)
        for j in range((m - 1) // 2 + 1):
            term = (0,) + tuple(catalan(j) * v for v in r[m - 1 - 2 * j])
            em = polynomial_add(em, term)
        e.append(em)
        rm = (0,)
        for j in range(m):
            rm = polynomial_add(rm, polynomial_multiply(e[j], r[m - 1 - j]))
        r.append(rm)
    return tuple(e), tuple(r)


@lru_cache(None)
def h_coefficient(n: int) -> F:
    _natural(n)
    j = n // 2
    return F(comb(2 * j, j), 4**j)


def negative_power_coefficient(r: int, n: int) -> int:
    """[y^n](1-y)^(-r), with an explicit r=0 convention."""
    _natural(r, "r")
    if n < 0:
        return 0
    _natural(n)
    return int(n == 0) if r == 0 else comb(n + r - 1, r - 1)


def h_convolution_coefficient(r: int, n: int) -> F:
    """[y^n] H(y)(1-y)^(-r), by direct coefficient convolution."""
    _natural(r, "r")
    if n < 0:
        return F(0)
    return sum((h_coefficient(j) * negative_power_coefficient(r, n - j)
                for j in range(n + 1)), F(0))


def _rising(a: F, k: int) -> F:
    out = F(1)
    for i in range(k):
        out *= a + i
    return out


def h_parity_coefficient(r: int, n: int) -> F:
    """Independent extraction from (1+y)^(r+1)(1-y^2)^(-r-1/2).

    The finite-support condition j<=n is retained, even at the upper edge.
    """
    _natural(r, "r")
    if n < 0:
        return F(0)
    out = F(0)
    for j in range(min(r + 1, n) + 1):
        if (n - j) % 2 == 0:
            k = (n - j) // 2
            out += comb(r + 1, j) * _rising(F(2 * r + 1, 2), k) / factorial(k)
    return out


def closed_coefficient(s: str, m: int, k: int) -> int:
    """Exact [x^m q^k]E or R from the fixed-k closed formula.

    This does not call the recurrence, and uses only h_j and binomial sums.
    """
    _class(s)
    _natural(m, "m")
    _natural(k, "k")
    if s == "E" and k == 0:
        return catalan(m // 2) if m % 2 == 0 else 0
    r = k if s == "R" else k - 1
    n = m - 2 * r
    if n < 0:
        return 0
    sign = 1 if s == "R" else -1
    coefficient = (F(2**m * catalan(r), 2 * 4**r)
                   * (h_convolution_coefficient(r, n)
                      + sign * negative_power_coefficient(r, n)))
    if coefficient.denominator != 1:
        raise ArithmeticError("closed coefficient unexpectedly nonintegral")
    return coefficient.numerator


@lru_cache(None)
def closed_polynomial(s: str, m: int):
    _class(s)
    _natural(m, "m")
    degree_bound = (m + 1) // 2 if s == "E" else m // 2
    return _trim([closed_coefficient(s, m, k) for k in range(degree_bound + 1)])


@lru_cache(None)
def bernoulli_number(n: int) -> F:
    """Bernoulli convention B_1=-1/2."""
    _natural(n)
    if n == 0:
        return F(1)
    return -sum((F(comb(n + 1, k)) * bernoulli_number(k)
                 for k in range(n)), F(0)) / (n + 1)


def bernoulli_polynomial(n: int, x) -> F:
    _natural(n)
    x = F(x)
    return sum((comb(n, k) * bernoulli_number(k) * x**(n - k)
                for k in range(n + 1)), F(0))


@lru_cache(None)
def gamma_ratio_coefficients(order: int, a: F, b: F):
    """G_0,...,G_order for Gamma(z+a)/Gamma(z+b), exactly."""
    _natural(order, "order")
    a, b = F(a), F(b)
    logarithmic = [F(0)]
    for h in range(1, order + 1):
        logarithmic.append(F((-1)**(h + 1), h * (h + 1))
                           * (bernoulli_polynomial(h + 1, a)
                              - bernoulli_polynomial(h + 1, b)))
    out = [F(1)]
    for ell in range(1, order + 1):
        out.append(sum((h * logarithmic[h] * out[ell - h]
                        for h in range(1, ell + 1)), F(0)) / ell)
    return tuple(out)


@lru_cache(None)
def p_value(ell: int, r: int) -> F:
    _natural(ell, "ell")
    _natural(r, "r")
    out = F(0)
    for j in range(r + 2):
        out += (comb(r + 1, j) * 2**ell
                * gamma_ratio_coefficients(ell, F(1 - j, 2), F(2 - 2 * r - j, 2))[ell])
    return out / 2**(r + 1)


@lru_cache(None)
def alternating_p_value(ell: int, r: int) -> F:
    """Compute the complete alternating expectation, without assuming cancellation."""
    _natural(ell, "ell")
    _natural(r, "r")
    out = F(0)
    for j in range(r + 2):
        out += ((-1)**j * comb(r + 1, j) * 2**ell
                * gamma_ratio_coefficients(ell, F(1 - j, 2), F(2 - 2 * r - j, 2))[ell])
    return out / 2**(r + 1)


def _interpolate_consecutive(values):
    """Convert exact forward differences at 0,1,... into monomial coefficients."""
    differences = [F(v) for v in values]
    result, basis = (F(0),), (F(1),)
    for j in range(len(values)):
        result = polynomial_add(result, tuple(differences[0] * v for v in basis))
        differences = [b - a for a, b in zip(differences, differences[1:])]
        basis = tuple(v / (j + 1) for v in polynomial_multiply(basis, (-j, 1)))
    return _trim(result)


@lru_cache(None)
def p_polynomial(ell: int):
    """P_ell(r); uses the proved degree bound <=2ell, not a numerical fit."""
    _natural(ell, "ell")
    return _interpolate_consecutive([p_value(ell, r) for r in range(2 * ell + 1)])


@lru_cache(None)
def q_polynomial(ell: int):
    _natural(ell, "ell")
    return _trim([alternating_p_value(ell, r) / factorial(r + 1)
                  for r in range(ell)])


def elementary_symmetric(values, ell: int):
    _natural(ell, "ell")
    out = [1] + [0] * ell
    for value in values:
        for j in range(ell, 0, -1):
            out[j] += value * out[j - 1]
    return out[ell]


@lru_cache(None)
def b_operator_value(ell: int, r: int) -> int:
    _natural(ell, "ell")
    _natural(r, "r")
    return (-1)**ell * elementary_symmetric(range(r + 1, 2 * r), ell)


@lru_cache(None)
def b_operator_polynomial(ell: int):
    """Polynomial in D for B_R,ell. Interpolate at r=1,...,2ell+1.

    r=0 is outside the defining B series and is not used as an interpolation
    datum: the empty-list convention there need not give the polynomial value.
    """
    _natural(ell, "ell")
    shifted = _interpolate_consecutive([b_operator_value(ell, r)
                                       for r in range(1, 2 * ell + 2)])
    out, basis = (F(0),), (F(1),)
    for coefficient in shifted:
        out = polynomial_add(out, tuple(coefficient * v for v in basis))
        basis = polynomial_multiply(basis, (-1, 1))
    return _trim(out)


def catalan_profile_coefficient(ell: int) -> F:
    _natural(ell, "ell")
    return 2**ell * gamma_ratio_coefficients(ell, F(1, 2), F(2))[ell]


def exact_profile_coefficient(kind: str, s: str, ell: int, epsilon: int, k: int) -> F:
    """Exact [w^k](sqrt(2pi) A) or [w^k]B.

    Removing the common sqrt(2pi) from A makes every returned value rational.
    This also supports exact formal checks of the boundary inverses.
    """
    if kind not in ("A", "B"):
        raise ValueError("profile kind must be 'A' or 'B'")
    _class(s)
    _natural(ell, "ell")
    _parity(epsilon)
    _natural(k, "k")
    if s == "E":
        if k == 0:
            return (2 * (1 + epsilon) * catalan_profile_coefficient(ell)
                    if kind == "A" else F(0))
        result = exact_profile_coefficient(kind, "R", ell, epsilon, k - 1)
        return result if kind == "A" else -result
    if kind == "A":
        return (p_value(ell, k) + epsilon * alternating_p_value(ell, k)) / factorial(k + 1)
    if k == 0:
        return F(0)
    return F(catalan(k), 2 * 4**k * factorial(k - 1)) * b_operator_value(ell, k)


@dataclass(frozen=True)
class ExactThreshold:
    """A rational factor times sqrt(radicand), with exact comparison in that basis."""
    factor: F
    radicand: int

    def compare_factor(self, target_factor) -> int:
        """Sign of Y-threshold when Y=target_factor*sqrt(radicand)."""
        difference = F(target_factor) - self.factor
        return (difference > 0) - (difference < 0)


def exact_threshold(s: str, m: int) -> ExactThreshold:
    _class(s)
    _natural(m, "m")
    if m < (1 if s == "E" else 2):
        raise ValueError("positive-root theorem excludes E m=0 and R m=0,1")
    factor = F(closed_coefficient(s, m, 0), 2**m)
    if s == "E":
        factor *= m
    return ExactThreshold(factor, m)


def _mp():
    try:
        import mpmath as mp
    except ImportError as exc:
        raise RuntimeError("numerical diagnostics require mpmath==1.3.0") from exc
    return mp


def _mp_fraction(q, mp):
    q = F(q)
    return mp.mpf(q.numerator) / q.denominator


def _finite_real(value, name, mp):
    value = mp.mpf(value)
    if not mp.isfinite(value):
        raise ValueError(f"{name} must be finite")
    return value


def _profile_r(kind: str, ell: int, epsilon: int, w, derivative: int):
    mp = _mp()
    w = mp.mpmathify(w)
    if not mp.isfinite(w):
        raise ValueError("profile argument must be finite")
    terms, small = [], 0
    polynomial = p_polynomial(ell) if kind == "A" else b_operator_polynomial(ell)
    start = derivative if kind == "A" else max(1, derivative)
    for r in range(start, 10000):
        if kind == "A":
            value = polynomial_value(polynomial, r)
            if r < ell:
                value += epsilon * alternating_p_value(ell, r)
            coefficient = value / ((r + 1) * factorial(r - derivative))
        else:
            coefficient = (F(catalan(r), 2 * 4**r) * r
                           * polynomial_value(polynomial, r) / factorial(r - derivative))
        term = _mp_fraction(coefficient, mp) * w**(r - derivative)
        terms.append(term)
        if r > abs(w) + 2 * ell + derivative + 12 and abs(term) < mp.eps:
            small += 1
            if small >= 8:
                answer = mp.fsum(terms)
                return answer / mp.sqrt(2 * mp.pi) if kind == "A" else answer
        else:
            small = 0
    raise ArithmeticError("diagnostic profile series did not converge within 10000 terms")


def profile(kind: str, s: str, ell: int, epsilon: int, w, derivative: int = 0):
    """Numerical entire profile/derivative, evaluated from exact coefficients.

    Series termination is a high-precision diagnostic, not interval certification.
    """
    if kind not in ("A", "B"):
        raise ValueError("profile kind must be 'A' or 'B'")
    _class(s)
    _natural(ell, "ell")
    _parity(epsilon)
    _natural(derivative, "derivative")
    mp = _mp()
    w = mp.mpmathify(w)
    result = _profile_r(kind, ell, epsilon, w, derivative)
    if s == "R":
        return result
    result *= w
    if derivative:
        result += derivative * _profile_r(kind, ell, epsilon, w, derivative - 1)
    if kind == "B":
        return -result
    if derivative == 0:
        result += (2 * (1 + epsilon) * _mp_fraction(catalan_profile_coefficient(ell), mp)
                   / mp.sqrt(2 * mp.pi))
    return result


def normalized_value(s: str, m: int, w):
    _class(s)
    _natural(m, "m")
    if m == 0:
        raise ValueError("normalization requires m>=1")
    mp = _mp()
    w = mp.mpmathify(w)
    if not mp.isfinite(w):
        raise ValueError("weight argument must be finite")
    scale = mp.sqrt(m) * (m if s == "E" else 1) / 2**m
    return scale * polynomial_value(closed_polynomial(s, m), w / m)


def asymptotic_value(s: str, m: int, w, order: int = 1):
    _natural(order, "order")
    _natural(m, "m")
    if m == 0:
        raise ValueError("normalization requires m>=1")
    mp = _mp()
    epsilon = (-1)**m
    return mp.fsum(profile("A", s, ell, epsilon, w) / m**ell
                   + profile("B", s, ell, epsilon, w) / (m**ell * mp.sqrt(m))
                   for ell in range(order + 1))


def model_root(s: str, epsilon: int, target):
    _class(s)
    _parity(epsilon)
    mp = _mp()
    target = _finite_real(target, "target", mp)
    threshold = (1 if s == "R" else 2 + 2 * epsilon) / mp.sqrt(2 * mp.pi)
    if target < threshold:
        raise ValueError("target is below the limiting model threshold")
    if target == threshold:
        return mp.mpf(0)
    if s == "E":
        return mp.log(mp.sqrt(2 * mp.pi) * target - 1 - 2 * epsilon)
    h = mp.sqrt(2 * mp.pi) * target
    return mp.re(-mp.lambertw(-mp.exp(-1 / h) / h, -1) - 1 / h)


def numerical_exact_root(s: str, m: int, target):
    """Bisection of the exact finite polynomial, in high-precision arithmetic.

    'Exact' describes the polynomial, not a certified numerical root enclosure.
    Endpoint eligibility uses the finite-m threshold, never the limiting one.
    """
    exact_threshold(s, m)  # Validate the exceptional cases before bisection.
    mp = _mp()
    target = _finite_real(target, "target", mp)
    low, high = mp.mpf(0), mp.mpf(1)
    threshold = normalized_value(s, m, low)
    if target < threshold:
        raise ValueError("target is below the exact finite-m threshold; no nonnegative root")
    if target == threshold:
        return low
    slope_at_zero = (mp.sqrt(m) * (m if s == "E" else 1)
                     * closed_polynomial(s, m)[1] / (2**m * m))
    high = max(high, 2 * (target - threshold) / slope_at_zero)
    for _ in range(16):
        if normalized_value(s, m, high) >= target:
            break
        high *= 2
    else:
        raise ArithmeticError("diagnostic root bracket could not be verified")
    for _ in range(8 * mp.mp.dps + 100):
        middle = (low + high) / 2
        if normalized_value(s, m, middle) < target:
            low = middle
        else:
            high = middle
        if high - low <= 8 * mp.eps * max(1, abs(high)):
            return (low + high) / 2
    raise ArithmeticError("diagnostic bisection did not converge")


def inverse_series(s: str, epsilon: int, w0, order: int = 2):
    """u_1,...,u_order by arbitrary-fixed-order formal series reversion.

    The expansion parameter is t=m^(-1/2), and the target is A_s,0(w0).
    This numerical implementation is intended for interior-root diagnostics.
    """
    _class(s)
    _parity(epsilon)
    _natural(order, "order")
    mp = _mp()
    w0 = _finite_real(w0, "model root", mp)
    if w0 <= 0:
        raise ValueError("inverse expansion requires an interior model root w0>0")
    slope = profile("A", s, 0, epsilon, w0, 1)
    jets = {}

    def jet(k, d):
        key = (k, d)
        if key not in jets:
            jets[key] = profile("A" if k % 2 == 0 else "B", s, k // 2,
                                epsilon, w0, d) / factorial(d)
        return jets[key]

    delta = [mp.mpf(0)]
    for n in range(1, order + 1):
        coefficient = mp.mpf(0)
        for k in range(n + 1):
            power = (mp.mpf(1),)
            for d in range(n - k + 1):
                if n - k < len(power):
                    coefficient += jet(k, d) * power[n - k]
                power = polynomial_multiply(power, delta)[:n + 1]
        delta.append(-coefficient / slope)
    return tuple(delta[1:])


def boundary_root_approximation(s: str, m: int):
    """Even-m limiting-threshold approximation; distinct from interior inversion."""
    _class(s)
    _natural(m, "m")
    if m == 0 or m % 2:
        raise ValueError("boundary expansion applies to positive even m only")
    mp = _mp()
    S = mp.sqrt(2 * mp.pi)
    if s == "E":
        return mp.mpf(9) / m - mp.mpf(451) / (8 * m**2) + 81 * S / (8 * m**2 * mp.sqrt(m))
    return (mp.mpf(1) / (2 * m) - S / (8 * m * mp.sqrt(m))
            + (mp.pi / 16 + mp.mpf(11) / 48) / m**2)


def diagnostics(dps: int = 80):
    """Return reproducible finite-sample diagnostics; no analytic certification."""
    if not isinstance(dps, int) or dps < 30:
        raise ValueError("diagnostics require at least 30 decimal digits")
    mp = _mp()
    with mp.workdps(dps):
        out = {"status": "finite high-precision diagnostics, not proofs of uniform bounds",
               "decimal_digits": dps, "crossover": [], "inverse": [], "endpoints": [],
               "boundary": []}
        fmt = lambda z: mp.nstr(z, 24)
        for m in (40, 41, 80, 81, 160, 161):
            for s in ("E", "R"):
                for w in (mp.mpf(0), mp.mpf("0.5"), mp.mpf(2), mp.mpc(1, "0.75")):
                    residual = normalized_value(s, m, w) - asymptotic_value(s, m, w, 1)
                    out["crossover"].append({"class": s, "m": m, "w": fmt(w),
                                             "m_squared_residual": fmt(m * m * residual)})
                w0 = mp.mpf("0.75")
                target = profile("A", s, 0, (-1)**m, w0)
                u1, u2 = inverse_series(s, (-1)**m, w0, 2)
                approximate = w0 + u1 / mp.sqrt(m) + u2 / m
                root = numerical_exact_root(s, m, target)
                out["inverse"].append({"class": s, "m": m, "model_root": fmt(w0),
                                       "exact_polynomial_root": fmt(root),
                                       "m_three_halves_root_error": fmt(m * mp.sqrt(m) * (approximate - root)),
                                       "m_three_halves_residual": fmt(m * mp.sqrt(m) *
                                           (normalized_value(s, m, approximate) - target))})
            threshold = normalized_value("R", m, 0)
            limit = 1 / mp.sqrt(2 * mp.pi)
            status = "positive root" if threshold < limit else "no nonnegative root"
            out["endpoints"].append({"class": "R", "m": m,
                                      "finite_threshold": fmt(threshold), "limiting_threshold": fmt(limit),
                                      "at_limiting_target": status})
            if m % 2 == 0:
                for s in ("E", "R"):
                    target = (4 if s == "E" else 1) / mp.sqrt(2 * mp.pi)
                    approximate = boundary_root_approximation(s, m)
                    root = numerical_exact_root(s, m, target)
                    scale = m**3 if s == "E" else m**2 * mp.sqrt(m)
                    out["boundary"].append({"class": s, "m": m,
                                            "exact_polynomial_root": fmt(root),
                                            "scaled_root_error": fmt(scale * (approximate - root)),
                                            "scaled_residual": fmt(scale *
                                                (normalized_value(s, m, approximate) - target)),
                                            "scale": "m^3" if s == "E" else "m^(5/2)"})
        return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("exact", "profiles", "diagnostics"))
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--order", type=int, default=4)
    parser.add_argument("--dps", type=int, default=80)
    args = parser.parse_args(argv)
    if args.command == "exact":
        e, r = recurrence_polynomials(args.m)
        print(json.dumps({"coefficient_order": "q^0,q^1,...", "E": e, "R": r}, indent=2))
    elif args.command == "profiles":
        _natural(args.order, "order")
        rows = [{"ell": ell, "P": list(map(str, p_polynomial(ell))),
                 "Q": list(map(str, q_polynomial(ell))),
                 "B_operator": list(map(str, b_operator_polynomial(ell))),
                 "c": str(catalan_profile_coefficient(ell))} for ell in range(args.order + 1)]
        print(json.dumps({"coefficient_order": "constant,linear,...", "profiles": rows}, indent=2))
    else:
        print(json.dumps(diagnostics(args.dps), indent=2))


if __name__ == "__main__":
    main()
