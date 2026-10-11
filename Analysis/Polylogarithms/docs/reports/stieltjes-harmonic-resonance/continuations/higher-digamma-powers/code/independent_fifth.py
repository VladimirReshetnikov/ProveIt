"""Independent fifth-power algebra and two numerical evaluations.

This script deliberately does not import the root derivation or source scripts.
Numerical results are diagnostics, not interval certificates.
"""

from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path

import mpmath as mp
import sympy as s


g = s.Symbol("gamma")
H = s.symbols("H1:6")
v = s.Symbol("v")
Z = {i: s.Symbol(f"zeta{i}") for i in range(2, 7)}


@lru_cache(None)
def stuffle(a, b):
    if not a:
        return {b: 1}
    if not b:
        return {a: 1}
    out = defaultdict(int)
    for w, c in stuffle(a[1:], b).items():
        out[(a[0],) + w] += c
    for w, c in stuffle(a, b[1:]).items():
        out[(b[0],) + w] += c
    for w, c in stuffle(a[1:], b[1:]).items():
        out[(a[0] + b[0],) + w] += c
    return dict(out)


def word_product(a, b):
    out = defaultdict(lambda: s.S.Zero)
    for wa, ca in a.items():
        for wb, cb in b.items():
            for w, c in stuffle(wa, wb).items():
                out[w] += ca * cb * c
    return dict(out)


def harmonic_expand(expr):
    """Polynomial in H1,...,H5 to linear strict harmonic words."""
    out = defaultdict(lambda: s.S.Zero)
    for degrees, coeff in s.Poly(s.expand(expr), *H).terms():
        words = {(): s.S.One}
        for r, exponent in enumerate(degrees, start=1):
            for _ in range(exponent):
                words = word_product(words, {(r,): s.S.One})
        for w, c in words.items():
            out[w] += coeff * c
    return {w: s.expand(c) for w, c in out.items() if c != 0}


@lru_cache(None)
def mzv(w):
    if not w:
        return s.S.One
    if len(w) == 1:
        if w[0] == 1:
            return g
        return Z[w[0]]
    return s.Symbol("Z_" + "_".join(map(str, w)))


@lru_cache(None)
def ct_harmonic(w):
    if not w or w[0] >= 2:
        return mzv(w)
    terms = dict(stuffle((1,), w[1:]))
    multiplicity = terms.pop(w)
    return s.expand(
        (g * ct_harmonic(w[1:])
         - sum(c * ct_harmonic(q) for q, c in terms.items())) / multiplicity
    )


def reduce_small_mzvs(expr):
    """Only exact classical identities of weights <=5 are used here."""
    z2, z3, z4, z5 = Z[2], Z[3], Z[4], Z[5]
    replacements = {
        mzv((2, 1)): z3,
        mzv((3, 1)): z4 / 4,
        mzv((2, 2)): 3 * z4 / 4,
        mzv((2, 1, 1)): z4,
        mzv((4, 1)): 2 * z5 - z2 * z3,
        mzv((3, 2)): 3 * z2 * z3 - s.Rational(11, 2) * z5,
        mzv((2, 3)): -2 * z2 * z3 + s.Rational(9, 2) * z5,
        mzv((3, 1, 1)): 2 * z5 - z2 * z3,
        mzv((2, 2, 1)): 3 * z2 * z3 - s.Rational(11, 2) * z5,
        mzv((2, 1, 2)): -2 * z2 * z3 + s.Rational(9, 2) * z5,
        mzv((2, 1, 1, 1)): z5,
    }
    return s.expand(s.expand(expr.subs(replacements)).subs(z2 ** 2, s.Rational(5, 2) * z4))


def sum_strict(expr, denominator):
    """Sum a polynomial in H_(n-1) divided by n^denominator."""
    return s.expand(sum(c * mzv((denominator,) + w)
                        for w, c in harmonic_expand(expr).items()))


def symbolic_checks():
    b, c, e, f = H[0] - g, H[1] + Z[2], H[2] - Z[3], H[3] + Z[4]
    old = {
        5: s.S.NegativeOne,
        4: 5 * b,
        3: 5 * c - 10 * b ** 2,
        2: 10 * b ** 3 - 20 * b * c + 5 * e,
        1: -5 * b ** 4 + 30 * b ** 2 * c - 10 * c ** 2 - 20 * b * e + 5 * f,
    }
    increment = {H[r - 1]: H[r - 1] + v ** r for r in range(1, 6)}
    new = {j: s.expand(p.subs(increment, simultaneous=True)) for j, p in old.items()}
    differences = {j: s.expand(new[j] - old[j]) for j in old}
    expected_diff = (-20 * b ** 3 + 60 * b * c - 20 * e) * v + 10 * c * v ** 2 + 20 * b * v ** 3
    assert s.expand(differences[1] - expected_diff) == 0

    # E from the independent all-k finite-part integration formula.
    e_integrand = s.expand(sum(differences[j] * v ** (j - 1) / (j - 1)
                              - new[j] * v ** j for j in range(2, 6)))
    E = s.S.Zero
    for (power,), coefficient in s.Poly(e_integrand, v).terms():
        assert power >= 2
        E += sum_strict(coefficient, power)

    # Finite cutoff constant of sum r_5(n)/n, with inclusive H_n.
    Fct = s.S.Zero
    for w, coeff in harmonic_expand(old[1]).items():
        if not w:
            contribution = g
        else:
            contribution = ct_harmonic((1,) + w) + ct_harmonic((1 + w[0],) + w[1:])
        Fct += coeff * contribution

    C = -g ** 5 + 20 * g ** 3 * Z[2] - 55 * g * Z[4] - 30 * g ** 2 * Z[3] + 20 * Z[2] * Z[3] - 5 * Z[5]
    combined = reduce_small_mzvs(C + E - Fct)
    claimed = 30 * g ** 2 * Z[2] - 60 * g * Z[3] + s.Rational(35, 3) * Z[4]
    residual = s.expand(combined - claimed)
    assert residual == 0, residual
    return {"residue_difference_exact": True,
            "scalar_polynomial_exact": True,
            "scalar_polynomial": str(combined),
            "E_unreduced": str(s.expand(E)),
            "Fct_unreduced": str(s.expand(Fct))}


def truncated_product(a, b, cutoff):
    out = [mp.mpf(0)] * (cutoff + 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b[:cutoff + 1 - i]):
            out[i + j] += ai * bj
    return out


def local_subtracted_quadrature(dps=90, cutoff=110, delta="0.1"):
    mp.mp.dps = dps
    base = [mp.mpf(0)] * (cutoff + 1)
    base[0], base[1] = -mp.mpf(1), -mp.euler
    for r in range(1, cutoff):
        base[r + 1] = (-1) ** (r + 1) * mp.zeta(r + 1)
    power = [mp.mpf(1)]
    for _ in range(5):
        power = truncated_product(power, base, cutoff)
    d = mp.mpf(delta)
    local = sum(power[j] * d ** (j - 4) / (j - 4) for j in range(5, cutoff + 1))
    singular_fp = sum(power[j] / (j - 4) for j in range(4))
    def remainder(x):
        return mp.digamma(x) ** 5 - sum(power[j] * x ** (j - 5) for j in range(5))
    ordinary = mp.quad(remainder, [d, mp.mpf("0.3"), mp.mpf("0.6"), 1])
    return singular_fp + local + ordinary


def spectral_arithmetic(dps=90, ncut=96, order=18):
    mp.mp.dps = dps
    z2 = mp.zeta(2)
    def delta_residue(n):
        b = mp.digamma(n)
        c = 2 * z2 - mp.polygamma(1, n)
        e = mp.polygamma(2, n) / 2
        return (-20 * b ** 3 + 60 * b * c - 20 * e) / n + 10 * c / n ** 2 + 20 * b / n ** 3
    direct = mp.fsum((delta_residue(n) - (-20 * mp.log(n) ** 3 + 120 * z2 * mp.log(n)) / n) * mp.log(n)
                     for n in range(1, ncut + 1))

    # Independently generated Bernoulli tail, retaining order 2*order.
    t, L, zz = s.symbols("t L z2")
    psi = L - t / 2 - sum(s.bernoulli(2 * k) * t ** (2 * k) / (2 * k) for k in range(1, order + 1))
    tri = t + t ** 2 / 2 + sum(s.bernoulli(2 * k) * t ** (2 * k + 1) for k in range(1, order + 1))
    second = -t ** 2 - t ** 3 - sum((2 * k + 1) * s.bernoulli(2 * k) * t ** (2 * k + 2) for k in range(1, order + 1))
    expression = s.expand(((-20 * psi ** 3 + 120 * zz * psi - 60 * psi * tri - 10 * second) * t
                            + (20 * zz - 10 * tri) * t ** 2 + 20 * psi * t ** 3
                            - (-20 * L ** 3 + 120 * zz * L) * t) * L)
    tail = mp.mpf(0)
    terms_used = 0
    for (p, log_power, z_power), rational in s.Poly(expression, t, L, zz).terms():
        if p > 2 * order or p < 2:
            continue
        c = mp.mpf(str(rational.p)) / int(rational.q) * z2 ** z_power
        derivative = mp.diff(lambda u: mp.zeta(u, ncut + 1), p, log_power)
        tail += c * (-1) ** log_power * derivative
        terms_used += 1
    Dlinear = 20 * mp.stieltjes(4) - 120 * z2 * mp.stieltjes(2) - direct - tail
    scalar = 30 * mp.euler ** 2 * z2 - 60 * mp.euler * mp.zeta(3) + mp.mpf(35) * mp.zeta(4) / 3
    return scalar + Dlinear, terms_used


if __name__ == "__main__":
    result = symbolic_checks()
    q = local_subtracted_quadrature()
    a, used = spectral_arithmetic()
    residual = abs(q - a)
    if not residual < mp.mpf("1e-50"):
        raise AssertionError("Independent fifth-power routes disagree")
    result.update({"status": "pass",
                   "working_digits": mp.mp.dps,
                   "mpmath_version": mp.__version__,
                   "sympy_version": s.__version__,
                   "arithmetic_cutoff": 96,
                   "maximum_tail_denominator_power": 36,
                   "local_taylor_degree": 110,
                   "diagnostic_tolerance": "1e-50",
                   "quadrature": mp.nstr(q, 85),
                   "arithmetic": mp.nstr(a, 85),
                   "absolute_residual": mp.nstr(residual, 8),
                   "tail_terms": used,
                   "meaning": "floating-point diagnostics, not a certified enclosure"})
    target = Path(__file__).resolve().parents[1] / "data" / "independent_fifth.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
