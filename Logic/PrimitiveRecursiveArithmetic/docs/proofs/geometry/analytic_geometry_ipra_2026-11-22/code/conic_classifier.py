#!/usr/bin/env python3
"""Exact rational affine classification, with checkable coefficient certificates.

This program implements the report's bounded conic reduction. It uses no
floating point arithmetic or real sign oracle. The certificate verifies an
identity of six polynomial coefficients; it is not a Lean or iPRA proof term.
Python Fraction is a convenient host representation of the report's integer
pair codes. Run this file directly to check the finite regression set.
"""

from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


def matmul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def matvec(a, v):
    return tuple(sum(a[i][j] * v[j] for j in range(2)) for i in range(2))


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def evaluate(q, x, y):
    a, b, c, d, e, f = q
    return a*x*x + b*x*y + c*y*y + d*x + e*y + f


def substitute(q, m, t):
    """Coefficients of q(M (u,v) + t), obtained by exact expansion."""
    a, b, c, d, e, f = q
    p, r = m[0]
    s, w = m[1]
    h, k = t
    return (a*p*p + b*p*s + c*s*s,
            2*a*p*r + b*(p*w+r*s) + 2*c*s*w,
            a*r*r + b*r*w + c*w*w,
            2*a*h*p + b*(h*s+k*p) + 2*c*k*s + d*p + e*s,
            2*a*h*r + b*(h*w+k*r) + 2*c*k*w + d*r + e*w,
            evaluate(q, h, k))


def sampled_coefficients(q, m, t):
    """A separate identity check, reconstructing coefficients at six points."""
    def f(u, v):
        x, y = matvec(m, (F(u), F(v)))
        return evaluate(q, x+t[0], y+t[1])
    z = f(0, 0)
    up, um = f(1, 0), f(-1, 0)
    vp, vm = f(0, 1), f(0, -1)
    a, c = (up+um)/2-z, (vp+vm)/2-z
    d, e = (up-um)/2, (vp-vm)/2
    b = f(1, 1)-a-c-d-e-z
    return a, b, c, d, e, z


def classify_normal(q):
    a, b, c, d, e, f = q
    if a == b == c == 0:
        if d != 0 or e != 0:
            return 'line'
        return 'whole_plane' if f == 0 else 'empty_constant'
    if not (a != 0 and b == 0 and d == 0):
        raise ValueError('Input has not been reduced to the specified form')
    if c != 0:
        if e != 0:
            raise ValueError('Central conic has an unremoved linear term')
        if a*c > 0:
            r = -f/a
            return 'ellipse' if r > 0 else 'point' if r == 0 else 'empty_definite'
        return 'hyperbola' if f != 0 else 'intersecting_lines'
    if e != 0:
        return 'parabola'
    r = -f/a
    return 'parallel_lines' if r > 0 else 'repeated_line' if r == 0 else 'empty_rank_one'


def reduce_conic(coefficients):
    """Return an affine substitution, its reduced polynomial and its type.

    A certificate means input(M * output_coordinates + t) == normal.
    Its transformation is invertible. No irrational point is claimed rational.
    """
    q0 = tuple(F(v) for v in coefficients)
    if len(q0) != 6:
        raise ValueError('Expected A, B, C, D, E, F')
    q = q0
    m = ((F(1), F(0)), (F(0), F(1)))
    t = (F(0), F(0))
    steps = []

    def change(n, u, name):
        nonlocal q, m, t
        n = tuple(tuple(F(x) for x in row) for row in n)
        u = tuple(F(x) for x in u)
        if det(n) == 0:
            raise AssertionError('Internal noninvertible change')
        q = substitute(q, n, u)
        mu = matvec(m, u)
        t = tuple(mu[i]+t[i] for i in range(2))
        m = matmul(m, n)
        steps.append(name)

    a, b, c, d, e, f = q
    if a == 0:
        if c != 0:
            change(((0, 1), (1, 0)), (0, 0), 'exchange coordinates')
        elif b != 0:
            change(((1, 1), (1, -1)), (0, 0), 'create nonzero diagonal pivot')
    a, b, c, d, e, f = q
    if a != 0:
        change(((1, -b/(2*a)), (0, 1)), (-d/(2*a), 0),
               'complete first square')
        a, b, c, d, e, f = q
        if c != 0:
            change(((1, 0), (0, 1)), (0, -e/(2*c)),
                   'complete second square')
    certificate = {'input': q0, 'matrix': m, 'translation': t,
                   'normal': q, 'kind': classify_normal(q), 'steps': steps}
    if not verify_certificate(certificate):
        raise AssertionError('Internal certificate failure')
    return certificate


def verify_certificate(c):
    """Verify polynomial identity and classification using exact arithmetic."""
    q0, m, t, q = c['input'], c['matrix'], c['translation'], c['normal']
    if det(m) == 0 or sampled_coefficients(q0, m, t) != q:
        return False
    a, b, cc, *_ = q0
    aa, bb, ccc, *_ = q
    if bb*bb-4*aa*ccc != det(m)**2*(b*b-4*a*cc):
        return False
    return classify_normal(q) == c['kind']


def serializable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: serializable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serializable(v) for v in value]
    return value


def regression():
    counts = {}
    checked = 0
    for coefficients in product(range(-2, 3), repeat=6):
        c = reduce_conic(coefficients)
        counts[c['kind']] = counts.get(c['kind'], 0) + 1
        checked += 1
    fixtures = {
        'empty ellipse equation': (1, 0, 1, 0, 0, 1),
        'ellipse': (4, 0, 1, 0, 0, -4),
        'hyperbola': (1, 0, -1, 0, 0, -1),
        'parabola': (0, 0, 1, -4, 0, 0),
        'intersecting real irrational-slope lines': (1, 0, -2, 0, 0, 0),
        'parallel lines': (1, 0, 0, 0, 0, -2),
        'double line': (1, 2, 1, 2, 2, 1),
        'point': (1, 0, 1, -2, -4, 5),
        'line': (0, 0, 0, 2, 3, 5),
    }
    results = {name: serializable(reduce_conic(q)) for name, q in fixtures.items()}
    # The checker must reject a material change to the polynomial identity.
    bad = dict(reduce_conic(fixtures['ellipse']))
    altered = list(bad['normal'])
    altered[-1] += 1
    bad['normal'] = tuple(altered)
    assert not verify_certificate(bad)
    return {'status': 'pass', 'exact_certificates_checked': checked,
            'input_domain': 'all six integer coefficients in [-2, 2]',
            'type_counts': counts, 'fixtures': results,
            'tampered_certificate_rejected': True,
            'scope': 'finite exact arithmetic verification, not a formal proof'}


if __name__ == '__main__':
    report = regression()
    output = Path(__file__).resolve().parent.parent / 'artifacts' / 'conic_classifier_checks.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'fixtures'}, indent=2))
