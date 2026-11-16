#!/usr/bin/env python3
"""Exact-rational certificate generator for the Gaussian iPRA packet.

The universal mathematics is proved in the accompanying manuscript.  This file
checks representative finite certificate instances using only integers and
fractions.Fraction for all proof-relevant calculations.  mpmath, when present,
is used only for non-authoritative diagnostics.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

sys.set_int_max_str_digits(0)


@dataclass(frozen=True)
class Ivl:
    lo: Fraction
    hi: Fraction

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError(f"invalid interval [{self.lo}, {self.hi}]")

    @staticmethod
    def point(x: Fraction | int) -> "Ivl":
        return Ivl(Fraction(x), Fraction(x))

    def __add__(self, other: "Ivl") -> "Ivl":
        return Ivl(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other: "Ivl") -> "Ivl":
        return Ivl(self.lo - other.hi, self.hi - other.lo)

    def __neg__(self) -> "Ivl":
        return Ivl(-self.hi, -self.lo)

    def __mul__(self, other: "Ivl") -> "Ivl":
        candidates = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Ivl(min(candidates), max(candidates))

    def scale(self, q: Fraction | int) -> "Ivl":
        return self * Ivl.point(Fraction(q))

    def recip(self) -> "Ivl":
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError("interval crosses zero")
        return Ivl(Fraction(1, 1) / self.hi, Fraction(1, 1) / self.lo)

    def pow_nat(self, n: int) -> "Ivl":
        if n < 0:
            raise ValueError("negative exponent")
        result = Ivl.point(1)
        base = self
        k = n
        while k:
            if k & 1:
                result = result * base
            base = base * base
            k >>= 1
        return result

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo

    def contains(self, q: Fraction) -> bool:
        return self.lo <= q <= self.hi

    def to_decimal_strings(self, digits: int = 18) -> dict[str, str]:
        # Decimal conversion here is display only; interval endpoints remain exact.
        from decimal import Decimal, localcontext
        with localcontext() as ctx:
            ctx.prec = digits + 20
            lo = Decimal(self.lo.numerator) / Decimal(self.lo.denominator)
            hi = Decimal(self.hi.numerator) / Decimal(self.hi.denominator)
            width = Decimal(self.width.numerator) / Decimal(self.width.denominator)
            return {
                "lo": format(lo, f".{digits}f"),
                "hi": format(hi, f".{digits}f"),
                "width": format(width, f".{digits}E"),
            }



def floor_fraction_scaled(q: Fraction, bits: int) -> Fraction:
    scale = 1 << bits
    z = q.numerator * scale // q.denominator
    return Fraction(z, scale)


def ceil_fraction_scaled(q: Fraction, bits: int) -> Fraction:
    scale = 1 << bits
    z = -((-q.numerator * scale) // q.denominator)
    return Fraction(z, scale)


def dyadic_hull(i: Ivl, bits: int = 220) -> Ivl:
    return Ivl(floor_fraction_scaled(i.lo, bits), ceil_fraction_scaled(i.hi, bits))


def floor_sqrt_fraction(q: Fraction, bits: int) -> Fraction:
    if q < 0:
        raise ValueError("sqrt of negative")
    scale = 1 << bits
    # floor(sqrt(q) * scale)
    z = math.isqrt((q.numerator * scale * scale) // q.denominator)
    # Correct defensively if integer division happened close to a square.
    while Fraction((z + 1) * (z + 1), scale * scale) <= q:
        z += 1
    while Fraction(z * z, scale * scale) > q:
        z -= 1
    return Fraction(z, scale)


def sqrt_interval(q: Fraction, bits: int = 220) -> Ivl:
    lo = floor_sqrt_fraction(q, bits)
    step = Fraction(1, 1 << bits)
    if lo * lo == q:
        return Ivl.point(lo)
    return Ivl(lo, lo + step)


def sqrt_interval_ivl(q: Ivl, bits: int = 220) -> Ivl:
    return Ivl(sqrt_interval(q.lo, bits).lo, sqrt_interval(q.hi, bits).hi)


def atan_unit_interval(x: Fraction, terms: int) -> Ivl:
    """Alternating arctangent interval for 0 <= x <= 1."""
    if not (0 <= x <= 1):
        raise ValueError("atan series requires 0 <= x <= 1")
    if terms <= 0:
        raise ValueError("terms must be positive")
    s = Fraction(0)
    x2 = x * x
    power = x
    for k in range(terms):
        term = power / (2 * k + 1)
        s += term if k % 2 == 0 else -term
        power *= x2
    nxt = power / (2 * terms + 1)
    signed = nxt if terms % 2 == 0 else -nxt
    return Ivl(min(s, s + signed), max(s, s + signed))


def pi_machin_interval(terms_5: int = 170, terms_239: int = 55) -> Ivl:
    a = atan_unit_interval(Fraction(1, 5), terms_5)
    b = atan_unit_interval(Fraction(1, 239), terms_239)
    return dyadic_hull(a.scale(16) - b.scale(4), 240)


def exp_neg_unit_interval(y: Fraction, terms: int = 240) -> Ivl:
    """Certified e^{-y} for 0 <= y <= 1 by alternating Taylor series."""
    if not (0 <= y <= 1):
        raise ValueError("requires y in [0,1]")
    s = Fraction(0)
    term = Fraction(1)
    for k in range(terms):
        if k:
            term *= y
            term /= k
        s += term if k % 2 == 0 else -term
    # Next term has exponent terms and factorial terms! because loop ended at k=terms-1.
    next_term = term * y / terms
    signed = next_term if terms % 2 == 0 else -next_term
    return Ivl(min(s, s + signed), max(s, s + signed))


def exp_neg_interval(r: Fraction, terms: int = 240) -> Ivl:
    if r < 0:
        raise ValueError("requires nonnegative r")
    if r == 0:
        return Ivl.point(1)
    m = 1
    while r > m:
        m <<= 1
    base = exp_neg_unit_interval(r / m, terms)
    return base.pow_nat(m)


def normalizing_constant_interval(bits: int = 220) -> tuple[Ivl, Ivl]:
    pi_i = pi_machin_interval()
    two_pi = pi_i.scale(2)
    sqrt_two_pi = sqrt_interval_ivl(two_pi, bits)
    return sqrt_two_pi.recip(), pi_i


def normal_cdf_series_interval(x: Fraction, terms: int, c: Ivl) -> Ivl:
    """Phi(x) from its integrated exponential series, for x >= 0.

    Phi(x) = 1/2 + c * sum_{k>=0} (-1)^k x^{2k+1}/(2^k k! (2k+1)).
    When terms > x^2/2, the term magnitudes decrease.  We use a symmetric
    one-next-term enclosure after checking the ratio condition.
    """
    if x < 0:
        pos = normal_cdf_series_interval(-x, terms, c)
        return Ivl.point(1) - pos
    if terms <= Fraction(x * x, 2):
        raise ValueError("terms too small for certified alternating tail")
    s = Fraction(0)
    # a_k = x^(2k+1)/(2^k k! (2k+1))
    a = x
    for k in range(terms):
        if k > 0:
            # a_k / a_{k-1} = x^2(2k-1)/(2k(2k+1))
            a *= x * x * (2 * k - 1)
            a /= 2 * k * (2 * k + 1)
        s += a if k % 2 == 0 else -a
    k = terms
    nxt = a * x * x * (2 * k - 1) / (2 * k * (2 * k + 1))
    series_i = Ivl(s - nxt, s + nxt)
    return dyadic_hull(Ivl.point(Fraction(1, 2)) + c * series_i, 210)


def phi_interval(x: Fraction, c: Ivl) -> Ivl:
    return dyadic_hull(c * exp_neg_interval(x * x / 2), 210)


def double_factorial_odd(m: int) -> int:
    """Return (2m-1)!!, with (-1)!!=1 at m=0."""
    out = 1
    for j in range(1, m + 1):
        out *= 2 * j - 1
    return out


def hermite_coeffs(n: int) -> list[int]:
    """Probabilists' Hermite polynomial coefficients, low degree first."""
    if n == 0:
        return [1]
    if n == 1:
        return [0, 1]
    hm1 = [1]
    h = [0, 1]
    for k in range(1, n):
        xh = [0] + h
        khm1 = [k * a for a in hm1] + [0] * (len(xh) - len(hm1))
        hn = [xh[i] - khm1[i] for i in range(len(xh))]
        while len(hn) > 1 and hn[-1] == 0:
            hn.pop()
        hm1, h = h, hn
    return h


def poly_derivative(p: Sequence[int]) -> list[int]:
    return [i * p[i] for i in range(1, len(p))] or [0]


def poly_add(a: Sequence[int], b: Sequence[int]) -> list[int]:
    n = max(len(a), len(b))
    out = [0] * n
    for i in range(n):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_neg_x_mul(a: Sequence[int]) -> list[int]:
    return [0] + [-v for v in a]


def derivative_gaussian_polynomials(n: int) -> list[list[int]]:
    """P_n with d^n exp(-x^2/2) = P_n exp(-x^2/2)."""
    ps = [[1]]
    for _ in range(n):
        ps.append(poly_add(poly_derivative(ps[-1]), poly_neg_x_mul(ps[-1])))
    return ps


def raw_normal_moment(mu: Fraction, var: Fraction, n: int) -> Fraction:
    total = Fraction(0)
    for j in range(n // 2 + 1):
        twoj = 2 * j
        total += Fraction(math.comb(n, twoj) * double_factorial_odd(j), 1) * (var**j) * (mu ** (n - twoj))
    return total


def finite_weighted_moments(values: Sequence[Fraction], weights: Sequence[Fraction]) -> tuple[Fraction, Fraction]:
    if len(values) != len(weights):
        raise ValueError("length mismatch")
    if sum(weights, Fraction(0)) != 1:
        raise ValueError("weights do not sum to one")
    mean = sum((w * x for x, w in zip(values, weights)), Fraction(0))
    var = sum((w * (x - mean) ** 2 for x, w in zip(values, weights)), Fraction(0))
    return mean, var


def mle_variance_identity(xs: Sequence[Fraction]) -> tuple[Fraction, Fraction]:
    n = len(xs)
    mean = sum(xs, Fraction(0)) / n
    lhs = sum((x - mean) ** 2 for x in xs)
    # Test at a deliberately different center.
    a = mean + Fraction(7, 13)
    rhs = sum((x - a) ** 2 for x in xs) - n * (a - mean) ** 2
    return lhs, rhs


def frac_json(q: Fraction) -> dict[str, int]:
    return {"numerator": q.numerator, "denominator": q.denominator}


def ivl_json(i: Ivl, digits: int = 18) -> dict[str, object]:
    return {
        "lo": frac_json(i.lo),
        "hi": frac_json(i.hi),
        "decimal": i.to_decimal_strings(digits),
    }


def run_certificates() -> dict[str, object]:
    checks: list[dict[str, object]] = []

    def record(name: str, ok: bool, detail: object = None) -> None:
        checks.append({"name": name, "ok": bool(ok), "detail": detail})
        if not ok:
            raise AssertionError(name)

    c, pi_i = normalizing_constant_interval()
    record("pi_interval_contains_333_106_and_355_113_bracket", pi_i.lo > Fraction(333, 106) and pi_i.hi < Fraction(355, 113), ivl_json(pi_i))
    record("normalizing_constant_positive", c.lo > 0, ivl_json(c))
    record("normalizing_constant_width_lt_2^-180", c.width < Fraction(1, 1 << 180), frac_json(c.width))

    coverage: dict[str, object] = {}
    published = {
        1: (Fraction(682689492, 10**9), Fraction(682689493, 10**9)),
        2: (Fraction(954499735, 10**9), Fraction(954499737, 10**9)),
        3: (Fraction(997300203, 10**9), Fraction(997300205, 10**9)),
        4: (Fraction(999936656, 10**9), Fraction(999936659, 10**9)),
        5: (Fraction(999999426, 10**9), Fraction(999999428, 10**9)),
        6: (Fraction(999999998, 10**9), Fraction(1, 1)),
    }
    for n in range(1, 7):
        phi_cdf = normal_cdf_series_interval(Fraction(n), 220, c)
        cov = (phi_cdf - Ivl.point(Fraction(1, 2))).scale(2)
        low_ref, high_ref = published[n]
        record(f"coverage_{n}_intersects_reference_window", not (cov.hi < low_ref or cov.lo > high_ref), ivl_json(cov, 20))
        coverage[str(n)] = ivl_json(cov, 20)

        q = Ivl.point(1) - phi_cdf
        ph = phi_interval(Fraction(n), c)
        lower = ph.scale(Fraction(n, n * n + 1))
        upper = ph.scale(Fraction(1, n))
        record(f"mills_lower_x_{n}", lower.hi < q.lo, {"lower": ivl_json(lower), "tail": ivl_json(q)})
        record(f"mills_upper_x_{n}", q.hi < upper.lo, {"tail": ivl_json(q), "upper": ivl_json(upper)})

    # Moment recurrence and exact values.
    moments = [Fraction(0)] * 21
    moments[0] = Fraction(1)
    moments[1] = Fraction(0)
    for n in range(19):
        moments[n + 2] = (n + 1) * moments[n]
    for n, m in enumerate(moments):
        expected = Fraction(0) if n % 2 else Fraction(double_factorial_odd(n // 2))
        record(f"standard_moment_{n}", m == expected, frac_json(m))

    # Raw moment formula obeys affine checks for selected exact parameters.
    mu = Fraction(7, 5)
    var = Fraction(11, 9)
    raw = [raw_normal_moment(mu, var, n) for n in range(13)]
    record("raw_moment_0", raw[0] == 1, frac_json(raw[0]))
    record("raw_moment_1", raw[1] == mu, frac_json(raw[1]))
    record("raw_moment_2", raw[2] == mu * mu + var, frac_json(raw[2]))
    record("raw_moment_3", raw[3] == mu**3 + 3 * mu * var, frac_json(raw[3]))
    record("raw_moment_recurrence", all(raw[n + 1] == mu * raw[n] + n * var * raw[n - 1] for n in range(1, 12)), [frac_json(x) for x in raw])

    # Hermite derivative polynomial identity.
    ps = derivative_gaussian_polynomials(14)
    herm = [hermite_coeffs(n) for n in range(15)]
    for n in range(15):
        target = [((-1) ** n) * a for a in herm[n]]
        record(f"hermite_derivative_identity_{n}", ps[n] == target, {"P": ps[n], "signed_He": target})

    # Hermite recurrence and derivative formula He_n' = n He_{n-1}.
    for n in range(1, 14):
        lhs = hermite_coeffs(n + 1)
        rhs = poly_add([0] + hermite_coeffs(n), [-n * a for a in hermite_coeffs(n - 1)])
        record(f"hermite_three_term_{n}", lhs == rhs, {"lhs": lhs, "rhs": rhs})
        record(f"hermite_derivative_{n}", poly_derivative(hermite_coeffs(n)) == [n * a for a in hermite_coeffs(n - 1)], hermite_coeffs(n))

    # Finite exact probability moments.
    vals = [Fraction(-2), Fraction(1), Fraction(5)]
    ws = [Fraction(1, 4), Fraction(1, 2), Fraction(1, 4)]
    mean, fvar = finite_weighted_moments(vals, ws)
    record("finite_law_mean", mean == Fraction(5, 4), frac_json(mean))
    record("finite_law_variance", fvar == Fraction(99, 16), frac_json(fvar))

    # Sum-of-squares / MLE identity.
    xs = [Fraction(-7, 3), Fraction(2, 5), Fraction(11, 7), Fraction(9, 2), Fraction(5, 6)]
    lhs, rhs = mle_variance_identity(xs)
    record("least_squares_center_identity", lhs == rhs, {"lhs": frac_json(lhs), "rhs": frac_json(rhs)})

    # Symbolic algebra checks when SymPy is available. These are exact and proof-relevant
    # only as regression checks; the paper gives the finite algebraic derivations.
    symbolic: dict[str, object] = {}
    try:
        import sympy as sp
        x, mu_s, sig, t, m1, m2, s1, s2 = sp.symbols("x mu sig t m1 m2 s1 s2", positive=True, real=True)
        logf = -sp.log(sig) - sp.Rational(1, 2) * sp.log(2 * sp.pi) - (x - mu_s) ** 2 / (2 * sig**2)
        score_mu = sp.diff(logf, mu_s)
        score_sig = sp.diff(logf, sig)
        record("symbolic_score_mu", sp.simplify(score_mu - (x - mu_s) / sig**2) == 0, str(score_mu))
        record("symbolic_score_sigma", sp.simplify(score_sig - ((x - mu_s) ** 2 / sig**3 - 1 / sig)) == 0, str(score_sig))
        kl = sp.log(s2 / s1) + (s1**2 + (m1 - m2) ** 2) / (2 * s2**2) - sp.Rational(1, 2)
        record("symbolic_kl_self_zero", sp.simplify(kl.subs({m2: m1, s2: s1})) == 0, str(kl))
        hell_aff = sp.sqrt(2 * s1 * s2 / (s1**2 + s2**2)) * sp.exp(-(m1 - m2) ** 2 / (4 * (s1**2 + s2**2)))
        record("symbolic_hellinger_self_one", sp.simplify(hell_aff.subs({m2: m1, s2: s1})) == 1, str(hell_aff))
        r, theta = sp.symbols("r theta", positive=True, real=True)
        u = r * sp.cos(theta)
        v = r * sp.sin(theta)
        jac = sp.simplify(sp.det(sp.Matrix([[sp.diff(u, r), sp.diff(u, theta)], [sp.diff(v, r), sp.diff(v, theta)]])))
        record("box_muller_polar_jacobian", sp.simplify(jac - r) == 0, str(jac))
        symbolic = {"sympy_version": sp.__version__, "kl": str(kl), "hellinger_affinity": str(hell_aff)}
    except Exception as exc:  # pragma: no cover - diagnostics only
        symbolic = {"unavailable": repr(exc)}

    # Non-authoritative high-precision diagnostics.
    diagnostics: dict[str, object] = {}
    try:
        import mpmath as mp
        mp.mp.dps = 60
        diag_cov = {}
        for n in range(1, 7):
            val = mp.erf(mp.mpf(n) / mp.sqrt(2))
            cov_i = Ivl(
                Fraction(coverage[str(n)]["lo"]["numerator"], coverage[str(n)]["lo"]["denominator"]),
                Fraction(coverage[str(n)]["hi"]["numerator"], coverage[str(n)]["hi"]["denominator"]),
            )
            scaled = Fraction(str(val))
            diag_cov[str(n)] = {"mpmath": mp.nstr(val, 50), "inside_exact_interval": cov_i.contains(scaled)}
        diagnostics = {"mpmath_version": mp.__version__, "coverage": diag_cov}
    except Exception as exc:  # pragma: no cover
        diagnostics = {"unavailable": repr(exc)}

    passed = sum(1 for c0 in checks if c0["ok"])
    return {
        "schema_version": 1,
        "proof_relevant_arithmetic": "integer and fractions.Fraction only",
        "checks_passed": passed,
        "checks_total": len(checks),
        "all_passed": passed == len(checks),
        "normalizing_constant": ivl_json(c, 24),
        "pi": ivl_json(pi_i, 24),
        "coverage_probabilities_P_abs_Z_le_n": coverage,
        "symbolic_regression": symbolic,
        "floating_diagnostics_not_proof": diagnostics,
        "checks": checks,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("evidence/validation.json"))
    parser.add_argument("--summary", type=Path, default=Path("evidence/validation.txt"))
    args = parser.parse_args()

    result = run_certificates()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines = [
        "Gaussian iPRA finite certificate validation",
        "===========================================",
        f"All checks passed: {result['all_passed']}",
        f"Checks: {result['checks_passed']} / {result['checks_total']}",
        "",
        "Certified central coverage intervals P(|Z| <= n):",
    ]
    for n, entry in result["coverage_probabilities_P_abs_Z_le_n"].items():
        dec = entry["decimal"]
        lines.append(f"  n={n}: [{dec['lo']}, {dec['hi']}]  width={dec['width']}")
    lines.extend([
        "",
        "All certificate endpoints are exact rational numbers in validation.json.",
        "Any mpmath values in that file are diagnostics only and are not proof oracles.",
    ])
    args.summary.write_text("\n".join(lines) + "\n", encoding="utf-8")

    digest = hashlib.sha256(args.output.read_bytes()).hexdigest()
    print(f"{result['checks_passed']}/{result['checks_total']} checks passed")
    print(f"validation sha256: {digest}")


if __name__ == "__main__":
    main()
