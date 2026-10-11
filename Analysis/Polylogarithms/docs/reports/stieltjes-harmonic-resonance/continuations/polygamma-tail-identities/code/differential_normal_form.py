#!/usr/bin/env python3
"""Exact differential-polynomial normal forms with finite-part endpoints.

u_r stands for the r-th derivative of a scalar function, wt(u_r)=r+1.
The canonical representatives are monomials whose highest derivative occurs
at least twice, together with powers of u_0.  All coefficients are exact.
No numerical independence of the resulting special-function values is used.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import sympy as s

GAMMA = s.Symbol('g')
Z = {k: s.Symbol('z' + str(k)) for k in range(2, 31)}
MAX_ORDER = 24
U = s.symbols('u0:' + str(MAX_ORDER + 1))


def weight(mon):
    return sum(r + 1 for r in mon)


def clean(p):
    return {m: s.expand(c) for m, c in p.items() if s.expand(c) != 0}


def add(p, q, scale=1):
    out = dict(p)
    for mon, coeff in q.items():
        out[mon] = out.get(mon, 0) + scale * coeff
    return clean(out)


def multiply(p, q):
    out = {}
    for m, c in p.items():
        for n, d in q.items():
            mon = tuple(sorted(m + n))
            out[mon] = out.get(mon, 0) + c * d
    return clean(out)


def derivative(p):
    out = {}
    for mon, coeff in p.items():
        counts = Counter(mon)
        for r, count in counts.items():
            work = list(mon)
            work.remove(r)
            work.append(r + 1)
            key = tuple(sorted(work))
            out[key] = out.get(key, 0) + count * coeff
    return clean(out)


def irreducible(mon):
    return not mon or mon[-1] == 0 or mon.count(mon[-1]) >= 2


@lru_cache(maxsize=None)
def reduce_monomial(mon):
    if irreducible(mon):
        return {mon: s.Integer(1)}, {}
    r = mon[-1]
    pre = tuple(sorted(mon[:-1] + (r - 1,)))
    multiplicity = pre.count(r - 1)
    primitive = {pre: s.Rational(1, multiplicity)}
    remainder = add({mon: 1}, derivative(primitive), scale=-1)
    normal, extra = normal_form(remainder)
    return normal, add(primitive, extra)


def normal_form(p):
    normal, primitive = {}, {}
    for mon, coeff in p.items():
        n, h = reduce_monomial(mon)
        normal = add(normal, n, coeff)
        primitive = add(primitive, h, coeff)
    return normal, primitive


def as_expression(p):
    return s.expand(sum(c * s.prod(U[r] for r in mon)
                        for mon, c in p.items()))


def inverse_gamma_polynomial(m):
    """(-1)^m Gamma(x) D^m (1/Gamma(x)), as a universal polynomial."""
    p = {(): s.Integer(1)}
    for _ in range(m):
        p = add(multiply({(0,): 1}, p), derivative(p), -1)
    return p


def gamma_taylor_coefficients(m):
    """Return [t^j] Gamma(1-t), j <= m, using exact independent symbols."""
    coeffs = [s.Integer(1)]
    for n in range(1, m + 1):
        coeffs.append(s.expand((GAMMA * coeffs[n - 1] +
            sum(Z[k] * coeffs[n - k] for k in range(2, n + 1))) / n))
    return coeffs


def gamma_quotient_polynomial(m):
    """m![t^m] Gamma(1-t) Gamma(x)/Gamma(x-t)."""
    g = gamma_taylor_coefficients(m)
    out = {}
    for k in range(m + 1):
        out = add(out, inverse_gamma_polynomial(k),
                  s.factorial(m) * g[m - k] / s.factorial(k))
    return out


def local_derivative(r, max_base_degree, centered=False):
    """Laurent series of psi^(r), or psi+gamma when r=0 and centered."""
    out = {-r - 1: s.Integer((-1) ** (r + 1) * s.factorial(r))}
    if r == 0 and not centered:
        out[0] = -GAMMA
    for k in range(max(1, r), max_base_degree + 1):
        out[k - r] = (-1) ** (k + 1) * Z[k + 1] * s.factorial(k) / s.factorial(k - r)
    return out


def laurent_multiply(p, q):
    out = {}
    for j, c in p.items():
        for k, d in q.items():
            out[j + k] = out.get(j + k, 0) + c * d
    return {k: s.expand(v) for k, v in out.items() if s.expand(v) != 0}


@lru_cache(maxsize=None)
def constant_at_zero(mon, centered=False):
    w = weight(mon)
    prod = {0: s.Integer(1)}
    for r in mon:
        # Multiply x^(r+1) u_r, which is an ordinary series; the desired
        # Laurent constant is then [x^w].  Discarding powers above w is exact.
        shifted = {j + r + 1: c for j, c in
                   local_derivative(r, max(0, w - 1), centered).items()
                   if j + r + 1 <= w}
        next_prod = {}
        for j, c in prod.items():
            for k, d in shifted.items():
                if j + k <= w:
                    next_prod[j + k] = next_prod.get(j + k, 0) + c * d
        prod = {j: s.expand(c) for j, c in next_prod.items()}
    return s.expand(prod.get(w, 0))


def endpoint_at_one(mon, centered=False):
    return s.prod((0 if centered else -GAMMA) if r == 0 else
                  (-1) ** (r + 1) * s.factorial(r) * Z[r + 1] for r in mon)


def boundary_value(p, centered=False):
    return s.expand(sum(c * (endpoint_at_one(m, centered) -
                           constant_at_zero(m, centered))
                        for m, c in p.items()))


def monomials_at_weight(w, min_part=1):
    if w == 0:
        yield ()
        return
    for part in range(min_part, w + 1):
        for tail in monomials_at_weight(w - part, part):
            yield (part - 1,) + tail


def serialize_poly(p):
    return [{'derivative_orders': list(mon), 'coefficient': str(coeff)}
            for mon, coeff in sorted(p.items())]


def create_tables(destination):
    destination = Path(destination)
    destination.mkdir(parents=True, exist_ok=True)
    records = []
    for m in range(2, 11):
        a = inverse_gamma_polynomial(m)
        normal, primitive = normal_form(a)
        # Direct polynomial identity: A_m = N(A_m) + D H_m.
        assert not add(add(a, normal, -1), derivative(primitive), -1)
        records.append({
            'weight': m,
            'inverse_gamma': serialize_poly(a),
            'normal_form': serialize_poly(normal),
            'primitive': serialize_poly(primitive),
            'boundary': str(boundary_value(primitive)),
            'normal_form_expression': str(as_expression(normal)),
            'primitive_expression': str(as_expression(primitive)),
        })
    (destination / 'inverse_gamma_normal_forms.json').write_text(
        json.dumps(records, indent=2) + '\n')
    tex = []
    for row in records:
        m = row['weight']
        tex.append('\\paragraph{Weight ' + str(m) + '.}')
        tex.append('\\begin{align*}')
        tex.append('N(\\mathcal A_{' + str(m) + '}) &=' +
                   s.latex(s.sympify(row['normal_form_expression'])) + r'\\')
        tex.append('\\Delta H_{' + str(m) + '} &=' +
                   s.latex(s.sympify(row['boundary'])))
        tex.append('\\end{align*}')
    (destination / 'normal_form_tables.tex').write_text('\n'.join(tex) + '\n')
    return records


if __name__ == '__main__':
    destination = Path(__file__).resolve().parents[1] / 'data'
    records = create_tables(destination)
    for row in records:
        if row['weight'] <= 8:
            print(row['weight'], row['normal_form_expression'])
            print('boundary =', row['boundary'])
