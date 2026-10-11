#!/usr/bin/env python3
"""Exact pole and strict-harmonic coordinates for FP integral psi^2 psi'^2."""
from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import sympy as s
from differential_normal_form import GAMMA, Z, constant_at_zero

H = s.symbols('h1:8')
V = s.Symbol('v')


@lru_cache(maxsize=None)
def stuffle(a, b):
    if not a:
        return {b: 1}
    if not b:
        return {a: 1}
    out = {}
    for prefix, left, right in ((a[0], a[1:], b),
                                (b[0], a, b[1:]),
                                (a[0] + b[0], a[1:], b[1:])):
        for word, c in stuffle(left, right).items():
            key = (prefix,) + word
            out[key] = out.get(key, 0) + c
    return out


def harmonic_product(exponents):
    out = {(): 1}
    for r, count in enumerate(exponents, 1):
        for _ in range(count):
            new = {}
            for word, coeff in out.items():
                for target, multiplicity in stuffle(word, (r,)).items():
                    new[target] = new.get(target, 0) + coeff * multiplicity
            out = new
    return out


def harmonic_words(poly):
    out = {}
    for powers, coeff in s.Poly(s.expand(poly), *H, V).terms():
        lead = powers[-1]
        for word, multiplicity in harmonic_product(powers[:-1]).items():
            key = (lead,) + word
            out[key] = out.get(key, 0) + coeff * multiplicity
    return {key: s.factor(coeff) for key, coeff in out.items()
            if s.expand(coeff) != 0}


def pole_data():
    b, c, d, e, f = s.symbols('b c d e f')
    generic = {
        6: s.Integer(1), 5: -2 * b, 4: b ** 2,
        3: -2 * b * c + 2 * d,
        2: 2 * b ** 2 * c - 2 * c ** 2 - 6 * b * d + 4 * e,
        1: 4 * b ** 2 * d + 2 * b * c ** 2 - 6 * c * d - 10 * b * e + 6 * f,
    }
    subst = {b: H[0] - GAMMA, c: H[1] + Z[2], d: H[2] - Z[3],
             e: H[3] + Z[4], f: H[4] - Z[5]}
    poles = {j: s.expand(v.subs(subst)) for j, v in generic.items()}
    shift = {h: h + V ** (r + 1) for r, h in enumerate(H)}
    delta = {j: s.expand(p.subs(shift, simultaneous=True) - p)
             for j, p in poles.items()}
    return generic, poles, delta


def reduce_weight_five(words):
    """Only standard admissible double-zeta evaluations used in J."""
    explicit = {
        (2, 1): Z[3], (3, 1): Z[4] / 4, (2, 2): 3 * Z[4] / 4,
        (4, 1): 2 * Z[5] - Z[2] * Z[3],
        (3, 2): 3 * Z[2] * Z[3] - s.Rational(11, 2) * Z[5],
        (2, 3): s.Rational(9, 2) * Z[5] - 2 * Z[2] * Z[3],
        (2, 1, 1): Z[4], (3, 1, 1): 2 * Z[5] - Z[2] * Z[3],
        (2, 2, 1): 3 * Z[2] * Z[3] - s.Rational(11, 2) * Z[5],
        (2, 1, 2): s.Rational(9, 2) * Z[5] - 2 * Z[2] * Z[3],
    }
    out = 0
    for word, coeff in words.items():
        value = Z[word[0]] if len(word) == 1 else explicit[word]
        out += coeff * value
    return s.expand(out).subs(Z[2] ** 2, s.Rational(5, 2) * Z[4]).expand()


def convergent_spectral_words(original):
    """Use one upper tail to move each singular first-order coordinate.

    A pair (word, slot) means zeta(word[0], ..., word[slot]+s, ...).
    The exact upper-tail conversion is proved in Appendix A of the article.
    Every resulting germ converges on Re(s)>-1; no pole extraction is used.
    """
    out = {(word, 0): coeff for word, coeff in original.items() if word[0] >= 2}
    replacements = [
        ((3, 1, 1), 1, -8), ((4, 1), 0, -8),
        ((3, 1), 1, 8*GAMMA), ((4,), 0, 8*GAMMA),
        ((2, 1, 2), 1, -2), ((3, 2), 0, -2),
        ((2, 1), 1, -6*Z[2]), ((3,), 0, -6*Z[2]),
        ((4, 1), 1, 10), ((5,), 0, 10),
    ]
    for word, slot, coeff in replacements:
        key = (word, slot)
        out[key] = out.get(key, 0) + coeff
    return {key: s.expand(c) for key, c in out.items() if s.expand(c) != 0}


def main():
    generic, poles, delta = pole_data()
    jpoly = s.expand(sum(delta[j] * V ** (j - 1) / (j - 1) for j in range(2, 7)))
    dpoly = delta[1]
    jw = harmonic_words(jpoly)
    dw = harmonic_words(dpoly)
    jvalue = reduce_weight_five(jw)
    print('J =', jvalue)
    print('Delta residue =', s.factor(dpoly))
    print('D(s) words:')
    for word, coeff in sorted(dw.items()):
        print(word, ':', coeff)
    data = {
        'pole_coefficients': {str(j): str(v) for j, v in generic.items()},
        'local_constant_at_zero': str(constant_at_zero((0, 0, 1, 1))),
        'higher_pole_sum': str(jvalue),
        'higher_pole_words': [{'word': list(w), 'coefficient': str(c)} for w, c in sorted(jw.items())],
        'spectral_words': [{'word': list(w), 'coefficient': str(c)} for w, c in sorted(dw.items())],
        'convergent_spectral_words': [
            {'word': list(w), 'spectral_parameter_slot': slot, 'coefficient': str(c)}
            for (w, slot), c in sorted(convergent_spectral_words(dw).items())],
        'convergent_coordinate_domain': 'Re(s) > -1; slot is zero-based',
        'delta_residue_polynomial': str(dpoly),
    }
    dest = Path(__file__).resolve().parents[1] / 'data'
    dest.mkdir(exist_ok=True)
    (dest / 'mixed_sixth_coordinates.json').write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
