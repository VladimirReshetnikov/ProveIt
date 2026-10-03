#!/usr/bin/env python3
"""Exact finite checks for Exponential Contact Depth in Surreal Polytopes.

Uses only integer arithmetic for all minor/sign checks.  SymPy is needed only
for the optional, separately reported projective reconstruction test.
These tests are not a proof of the infinite family or a Lean formalization.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
from pathlib import Path
from typing import Dict, Tuple

Poly = Dict[int, int]  # exponent -> integer coefficient
Point = Tuple[Poly, Poly, Poly]

def add(a: Poly, b: Poly, scale: int = 1) -> Poly:
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) + scale * c
        if out[e] == 0:
            del out[e]
    return out

def mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for e, c in a.items():
        for f, d in b.items():
            out[e + f] = out.get(e + f, 0) + c * d
    return {e: c for e, c in out.items() if c}

def mono(e: int = 0, c: int = 1) -> Poly:
    return {e: c} if c else {}

def det(a: Point, b: Point, c: Point) -> Poly:
    out: Poly = {}
    for p in itertools.permutations(range(3)):
        inversions = sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
        out = add(out, mul(mul(a[p[0]], b[p[1]]), c[p[2]]),
                  -1 if inversions % 2 else 1)
    return out

def sign(n: int) -> int:
    return (n > 0) - (n < 0)

def sign_at_reciprocal(p: Poly, denominator: int = 7) -> int:
    if not p:
        return 0
    degree = max(p)
    return sign(sum(c * denominator ** (degree-e) for e, c in p.items()))

def configuration(k: int) -> dict[str, Point]:
    if not isinstance(k, int) or not 1 <= k <= 12:
        raise ValueError('k must be an integer between 1 and 12 for finite checks')
    z, o, neg = {}, mono(), mono(c=-1)
    points: dict[str, Point] = {
        'O': (z,z,o), 'I': (o,z,o), 'J': (z,o,o),
        'U': (o,z,z), 'V': (z,o,z), 'W': (o,neg,z),
        'X0': (mono(1),z,o), 'A0': (z,mono(1),o),
    }
    for i in range(k):
        e = 2 ** i
        points[f'B{i}'] = (o, mono(e), o)
        points[f'C{i}'] = (mono(e), mono(2*e), o)
        points[f'A{i+1}'] = (z, mono(2*e), o)
        points[f'X{i+1}'] = (mono(2*e), z, o)
    assert len(points) == 4*k + 8
    return points

def require_collinear(points: dict[str, Point], *names: str) -> None:
    assert len(names) == 3
    assert not det(*(points[name] for name in names)), names

def check_configuration(k: int) -> dict:
    p = configuration(k)
    for names in [('O','I','U'), ('O','J','V'), ('U','V','W'),
                  ('I','J','W'), ('X0','W','A0')]:
        require_collinear(p,*names)
    for i in range(k):
        for names in [(f'A{i}','U',f'B{i}'), ('I','V',f'B{i}'),
                      ('O',f'B{i}',f'C{i}'), (f'X{i}','V',f'C{i}'),
                      (f'C{i}','U',f'A{i+1}'), ('O','V',f'A{i+1}'),
                      (f'A{i+1}','W',f'X{i+1}'), ('O','U',f'X{i+1}')]:
            require_collinear(p,*names)
    zero = positive = negative = 0
    max_degree = max_l1 = 0
    for names in itertools.combinations(p,3):
        d = det(*(p[name] for name in names))
        if not d:
            zero += 1
            continue
        lead = d[min(d)]
        assert sum(abs(c) for c in d.values()) <= 6
        assert sum(abs(c) for e,c in d.items() if e != min(d)) <= 5
        assert sign_at_reciprocal(d) == sign(lead)
        # Affine chart L=X+2Y+Z: only W has a negative denominator.
        adjusted = sign(lead) * (-1 if 'W' in names else 1)
        positive += adjusted > 0
        negative += adjusted < 0
        max_degree = max(max_degree,max(d))
        max_l1 = max(max_l1,sum(abs(c) for c in d.values()))
    # A constant rank-three witness survives deletion of every point.
    frame = ('O','I','J','U','V','W')
    for removed in p:
        assert any(det(*(p[a] for a in triple))
                   for triple in itertools.combinations([a for a in frame if a != removed],3))
    return {'k': k, 'projective_points': len(p), 'polytope_vertices': 2*len(p),
            'dimension': len(p)+2, 'minors': math.comb(len(p),3),
            'zero_minors': zero, 'positive_chart_minors': positive,
            'negative_chart_minors': negative, 'max_minor_degree': max_degree,
            'max_coefficient_l1': max_l1, 'tested_real_parameter': '1/7',
            'cross_ratio_orders': [2**i for i in range(k+1)]}

def reconstruction_test() -> dict:
    import sympy as sp
    p = configuration(1)
    names = list(p)
    m = len(names)
    h = m+3
    t = sp.Rational(1,7)
    def ev(poly: Poly):
        return sum(sp.Integer(c)*t**e for e,c in poly.items())
    points = []
    for name in names:
        X,Y,Z = map(ev,p[name])
        L = X+2*Y+Z
        points.append(sp.Matrix([X/L,Y/L,1]))
    vertices = []
    for i,b in enumerate(points):
        lower = sp.zeros(h,1); lower[3+i] = 1
        upper = lower.copy(); upper[:3,0] = b
        vertices.append((lower,upper))
    # Invertible constant projective transformation, mixing the coordinate blocks.
    T = sp.eye(h)
    for i in range(h-1):
        T[i,i+1] = (i % 3) + 1
    T = T * T.T
    transformed = [(T*a,T*b) for a,b in vertices]
    recovered = []
    for i in range(m):
        others = [v for j,pair in enumerate(transformed) if j != i for v in pair]
        A = sp.Matrix.vstack(*(v.T for v in others))
        ns = A.nullspace()
        assert len(ns) == 1
        H = ns[0]
        lo,up = transformed[i]
        a = (H.dot(lo))*up - (H.dot(up))*lo
        assert a != sp.zeros(h,1)
        recovered.append(a)
    byname = dict(zip(names,recovered))
    O,I,U = (byname[n] for n in ('O','I','U'))
    idx = next((a,b) for a,b in itertools.combinations(range(h),2)
               if O[a]*U[b]-O[b]*U[a] != 0)
    def bracket(a,b):
        return a[idx[0]]*b[idx[1]]-a[idx[1]]*b[idx[0]]
    cross_ratios = {}
    for i in range(2):
        X = byname[f'X{i}']
        value = sp.cancel(bracket(X,O)*bracket(I,U)/(bracket(X,U)*bracket(I,O)))
        assert value == t**(2**i)
        cross_ratios[f'x{i}'] = str(value)
    return {'status': 'passed', 'field': 'rational numbers',
            'k': 1, 'recovered_facets': m,
            'homogeneous_dimension': h,
            'recovered_cross_ratios': cross_ratios,
            'scope': 'Exact finite reconstruction; not a face-lattice enumeration.'}

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k',type=int,default=6)
    parser.add_argument('--output',type=Path,default=Path('verification.json'))
    parser.add_argument('--skip-reconstruction',action='store_true')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Run without -O: verification assertions must be enabled.')
    if not args.skip_reconstruction:
        try:
            import sympy  # noqa: F401; fail early with an actionable message
        except ImportError:
            parser.error('Install sympy, or use --skip-reconstruction.')
    if not 1 <= args.max_k <= 12:
        parser.error('--max-k must be between 1 and 12')
    result = {'scope': 'Finite exact-arithmetic tests, not a formal proof.',
              'configurations': [check_configuration(k) for k in range(1,args.max_k+1)]}
    result['projective_reconstruction'] = (
        {'status':'skipped'} if args.skip_reconstruction else reconstruction_test())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
