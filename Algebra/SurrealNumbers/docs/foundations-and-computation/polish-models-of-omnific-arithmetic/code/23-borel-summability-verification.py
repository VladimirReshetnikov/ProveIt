#!/usr/bin/env python3
"""Exact finite checks for 'Borel Regularity Forces Summability'.

Requires Python 3.10+ and only its standard library. These checks verify finite
algebra and cutoff formulas, not the Baire-category or novelty claims.
Run: python verification.py > verification_results.json
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as Q
import json
import math
import random
from typing import TypeAlias

Series: TypeAlias = dict[Q, Q]
COUNTS: Counter[str] = Counter()


def clean(f: Series) -> Series:
    """Remove zero coefficients and normalize to exact rational data."""
    return {Q(e): Q(c) for e, c in f.items() if c}


def add(*terms: Series) -> Series:
    out: Series = {}
    for term in terms:
        for e, c in term.items():
            out[e] = out.get(e, Q(0)) + c
    return clean(out)


def scale(c: Q, f: Series) -> Series:
    return clean({e: Q(c) * a for e, a in f.items()})


def mul(f: Series, g: Series) -> Series:
    out: Series = {}
    for e, c in f.items():
        for d, b in g.items():
            out[e + d] = out.get(e + d, Q(0)) + c * b
    return clean(out)


def val(f: Series) -> Q:
    if not f:
        raise ValueError("The finite valuation of zero is not defined here.")
    return min(f)


def cut(f: Series, bound: Q) -> Series:
    return {e: c for e, c in f.items() if e <= bound}


def monomial(e: Q, c: Q = Q(1)) -> Series:
    return clean({Q(e): Q(c)})


def euler(f: Series) -> Series:
    return clean({e: e * c for e, c in f.items()})


def deriv(a: Series, f: Series) -> Series:
    """The derivation D_a = a E, E(t^q) = q t^q."""
    return mul(a, euler(f))


def primitive_euler(h: Series) -> Series:
    """Return the primitive with zero constant, or reject the obstruction."""
    if h.get(Q(0), Q(0)):
        raise ValueError("Euler integration requires zero constant coefficient.")
    return {e: c / e for e, c in h.items() if e}


def random_series(rng: random.Random, terms: int = 7) -> Series:
    out: Series = {}
    for _ in range(terms):
        e = Q(rng.randint(-12, 16), 4)
        c = Q(rng.randint(-6, 6), rng.randint(1, 6))
        out[e] = out.get(e, Q(0)) + c
    return clean(out)


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Exact check failed: {name}")
    COUNTS[name] += 1


def flow_binomial(f: Series, s: Q, bound: Q) -> Series:
    """Truncate exp(s*t*E)(f), using t^q(1-s*t)^(-q).

    All shifts are nonnegative integers, so terms above bound never return.
    """
    out: Series = {}
    for q, c in f.items():
        if q > bound:
            continue
        max_n = math.floor(bound - q)
        factor = Q(1)
        for n in range(max_n + 1):
            if n:
                factor *= (q + n - 1) * s / n
            exponent = q + n
            out[exponent] = out.get(exponent, Q(0)) + c * factor
    return clean(out)


def flow_iterated(f: Series, s: Q, bound: Q) -> Series:
    """Independent exponential evaluation by iterating D = t E."""
    if not f or val(f) > bound:
        return {}
    n_max = math.floor(bound - val(f))
    current = dict(f)
    weight = Q(1)
    result: Series = {}
    t = monomial(Q(1))
    for n in range(n_max + 1):
        if n:
            current = deriv(t, current)
            weight *= s / n
        result = add(result, cut(scale(weight, current), bound))
    return result


def run_checks() -> dict[str, object]:
    rng = random.Random(20261004)
    for _ in range(160):
        f, g, a, b = [random_series(rng) for _ in range(4)]
        if not a:
            a = monomial(Q(0))
        check("Leibniz", deriv(a, mul(f, g)) ==
              add(mul(f, deriv(a, g)), mul(g, deriv(a, f))))
        lhs = add(deriv(a, deriv(b, f)), scale(Q(-1), deriv(b, deriv(a, f))))
        bracket_parameter = add(mul(a, euler(b)), scale(Q(-1), mul(b, euler(a))))
        check("commutator", lhs == deriv(bracket_parameter, f))
        bound = Q(rng.randint(-8, 14), 2)
        check("derivation_cutoff", cut(deriv(a, f), bound) ==
              cut(deriv(a, cut(f, bound - val(a))), bound))
        df = deriv(a, f)
        check("gain_bound", not df or val(df) >= val(a) + val(f))
        h = euler(f)
        primitive = primitive_euler(h)
        check("Euler_primitive", euler(primitive) == h)
        check("primitive_unique_mod_constants", primitive ==
              {e: c for e, c in f.items() if e})
        check("weighted_primitive", deriv(a, primitive) == deriv(a, f))
        try:
            primitive_euler(add(h, monomial(Q(0))))
        except ValueError:
            check("constant_obstruction", True)
        else:
            check("constant_obstruction", False)

    exponents = [Q(-7, 3), Q(-2), Q(-1), Q(0), Q(1, 2), Q(2), Q(9, 4)]
    parameters = [Q(-2), Q(-1, 3), Q(0), Q(2, 5), Q(3)]
    for q in exponents:
        for s in parameters:
            for bound in [Q(-1), Q(0), Q(2), Q(5)]:
                f = monomial(q)
                check("binomial_vs_iterated_flow",
                      flow_binomial(f, s, bound) == flow_iterated(f, s, bound))

    for _ in range(60):
        f, g = random_series(rng, 4), random_series(rng, 4)
        if not f:
            f = monomial(Q(0))
        if not g:
            g = monomial(Q(0))
        s = Q(rng.randint(-4, 4), 3)
        r = Q(rng.randint(-4, 4), 5)
        bound = Q(rng.randint(0, 6), 2)
        check("flow_composition", flow_binomial(flow_binomial(f, r, bound), s, bound)
              == flow_binomial(f, r + s, bound))
        check("flow_inverse", flow_binomial(flow_binomial(f, s, bound), -s, bound)
              == cut(f, bound))
        # Negative input exponents require unequal safe factor cutoffs.
        right = cut(mul(flow_binomial(f, s, bound - val(g)),
                        flow_binomial(g, s, bound - val(f))), bound)
        check("flow_multiplicativity", flow_binomial(mul(f, g), s, bound) == right)

    # Finite witnesses to the coefficient-discontinuity sequence:
    # D=(1-t)^(-1) E and f_n=-t^(-n)/n imply [t^0]D(f_n)=1.
    for n in range(1, 41):
        a = {Q(k): Q(1) for k in range(n + 1)}
        f = monomial(Q(-n), Q(-1, n))
        check("discontinuous_coefficient_witness", deriv(a, f).get(Q(0)) == 1)

    return {
        "status": "PASS",
        "seed": 20261004,
        "arithmetic": "exact fractions; no floating-point algebra",
        "checks": dict(sorted(COUNTS.items())),
        "total_checks": sum(COUNTS.values()),
        "scope": "Finite identities and certified cutoff examples only.",
        "not_verified_by_this_script": [
            "Baire-category and generic-support arguments",
            "infinite-dimensional automatic continuity theorem",
            "literature novelty or priority",
            "Lean or another proof-assistant formalization"
        ]
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2, sort_keys=True))
