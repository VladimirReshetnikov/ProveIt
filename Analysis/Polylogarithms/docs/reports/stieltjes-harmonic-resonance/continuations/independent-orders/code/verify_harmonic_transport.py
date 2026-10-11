#!/usr/bin/env python3
"""Exact finite checks and independent floating-point continuation diagnostics.

The all-index continuation theorem is proved analytically in the article.
These checks audit signs, order, finite reductions, and cancellation at
several singular intersections. Numerical results are not interval proofs.
"""
from __future__ import annotations

import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp


@lru_cache(maxsize=None)
def finite_z(word, shift, count, star=False):
    """Direct finite nested sum by a one-pass dynamic program."""
    if not word:
        return sp.Integer(1)
    values = [sp.Integer(0)] * len(word) + [sp.Integer(1)]
    for n in range(count):
        x = shift + n
        order = range(len(word)-1, -1, -1) if star else range(len(word))
        for j in order:
            values[j] += x**(-word[j]) * values[j+1]
    return values[0]


def finite_quotient(word, a, b, tail_count, interval_count):
    """F_a^{-1}F_b with exactly aligned finite upper cutoffs."""
    @lru_cache(maxsize=None)
    def h(w):
        if not w:
            return sp.Integer(1)
        ans = finite_z(w, b, tail_count + interval_count)
        for j in range(1, len(w)+1):
            ans -= finite_z(w[:j], a, tail_count) * h(w[j:])
        return ans
    return h(tuple(word))


def exact_checks():
    count = 0
    b = sp.Rational(2, 3)
    interval = 5
    a = b + interval
    words = [w for depth in range(1, 5)
             for w in itertools.product((-1, 0, 1, 3), repeat=depth)]
    for word in words:
        direct = finite_z(word, b, interval)
        quotient = finite_quotient(word, a, b, 7, interval)
        assert quotient == direct
        count += 1
        star_expression = sum(
            (-1)**j * finite_z(tuple(reversed(word[:j])), a, 7, True)
            * finite_z(word[j:], b, 7+interval)
            for j in range(len(word)+1))
        assert star_expression == direct
        count += 1
    for m in range(6):
        for s in range(-3, 7):
            h = lambda t: finite_z((t,), b, interval)
            rhs = (sum(sp.binomial(m+1, j)*sp.bernoulli(m+1-j, 0)*h(s-j)
                       for j in range(m+2))
                   - sp.bernoulli(m+1, b)*h(s))/(m+1)
            assert rhs == finite_z((s, -m), b, interval)
            count += 1
    # A sign corruption of the depth-two quotient must be detected.
    w = (2, 3)
    wrong = (finite_z(w, b, 7+interval)-finite_z(w, a, 7)
             + finite_z((2,), a, 7)
             * (finite_z((3,), b, 7+interval)-finite_z((3,), a, 7)))
    assert wrong != finite_z(w, b, interval)
    count += 1
    # Pole coefficient examples, independently expanded from EM steps.
    x, y = sp.symbols('x y')
    beta0 = lambda z: 1/(z-1)
    c30 = beta0(x)*beta0(x+y-1)
    assert sp.cancel(c30-1/((x-1)*(x+y-2))) == 0
    c31 = -sp.Rational(1, 2)*(beta0(x)+beta0(x+y))
    assert sp.cancel(c31+(2*x+y-2)/(2*(x-1)*(x+y-1))) == 0
    count += 2
    return {'assertions': count, 'finite_words': len(words),
            'negative_inner_cases': 60, 'corruption_control': 'passed'}


def em_terms(s, order):
    out = {-1: 1/(s-1), 0: -mp.mpf('0.5')}
    for k in range(1, order+1):
        out[2*k-1] = mp.bernoulli(2*k)/mp.factorial(2*k)*mp.rf(s, 2*k-1)
    return out


class Continuation:
    """Direct finite outer-tail sums plus finite Euler--Maclaurin tails."""
    def __init__(self, cutoff=28, order=14):
        self.cutoff = cutoff
        self.order = order
        self.cache = {}

    def z(self, word, a):
        key = (tuple(word), a)
        if key in self.cache:
            return self.cache[key]
        if len(word) == 0:
            ans = mp.mpf(1)
        elif len(word) == 1:
            ans = mp.zeta(word[0], a)
        elif len(word) == 2:
            s, t = word
            ans = mp.fsum(mp.zeta(s, a+n+1)/(a+n)**t
                          for n in range(self.cutoff))
            ans += mp.fsum(c*mp.zeta(s+t+j, a+self.cutoff)
                           for j, c in em_terms(s, self.order).items())
        elif len(word) == 3:
            s, t, v = word
            harmonic = mp.mpf(0)
            ans = mp.mpf(0)
            for n in range(self.cutoff):
                x = a+n
                ans += mp.zeta(s, x+1)*harmonic/x**t
                harmonic += x**(-v)
            outer = em_terms(s, self.order)
            inner = em_terms(v, self.order)
            inner[0] = mp.mpf('0.5')  # zeta(v,x), not zeta(v,x+1)
            convolution = {}
            for j, c in outer.items():
                for k, d in inner.items():
                    convolution[j+k] = convolution.get(j+k, 0) + c*d
            ans += mp.zeta(v, a)*mp.fsum(
                c*mp.zeta(s+t+j, a+self.cutoff) for j, c in outer.items())
            ans -= mp.fsum(c*mp.zeta(s+t+v+j, a+self.cutoff)
                           for j, c in convolution.items())
        else:
            raise ValueError('Numerical continuation implemented through depth three')
        self.cache[key] = ans
        return ans

    def h(self, word, a, b):
        word = tuple(word)
        if not word:
            return mp.mpf(1)
        return self.z(word, b) - mp.fsum(
            self.z(word[:j], a)*self.h(word[j:], a, b)
            for j in range(1, len(word)+1))


def elementary_diagonal(r, p, a, b):
    h = [None]
    for k in range(1, r+1):
        if p*k == 1:
            h.append(mp.digamma(a)-mp.digamma(b))
        else:
            h.append(mp.zeta(p*k, b)-mp.zeta(p*k, a))
    e = [mp.mpf(1)]
    for n in range(1, r+1):
        e.append(mp.fsum((-1)**(k-1)*h[k]*e[n-k]
                         for k in range(1, n+1))/n)
    return e[r]


def numeric_checks(dps):
    mp.mp.dps = dps
    rows = []
    def record(name, residual, **metadata):
        rows.append({'name': name, 'absolute_residual': mp.nstr(abs(residual), 12),
                     **metadata})
    a, b, c = map(mp.mpf, ('2.3', '0.8', '1.4'))
    cont = Continuation()
    cases = [(mp.mpc('.4', '.1'), mp.mpc('.7', '-.2')),
             (mp.mpc('1.2', '.2'), mp.mpc('-.8', '.1')),
             (mp.mpc('-2.2', '.4'), mp.mpc('1.3', '-.2'))]
    for i, w in enumerate(cases):
        s, t = w
        h = lambda x: mp.zeta(x, b)-mp.zeta(x, a)
        record('depth_two_stuffle', cont.h(w,a,b)+cont.h(w[::-1],a,b)
               +h(s+t)-h(s)*h(t), case=i)
        record('upper_shift', cont.h(w,a+1,b)-cont.h(w,a,b)
               -a**(-s)*h(t), case=i)
        record('lower_shift', cont.h(w,a,b)-cont.h(w,a,b+1)
               -b**(-t)*(mp.zeta(s,b+1)-mp.zeta(s,a)), case=i)
    for m in range(5):
        s = mp.mpc('1.1', '.23')
        h = lambda x: mp.zeta(x, b)-mp.zeta(x, a)
        rhs = (mp.fsum(mp.binomial(m+1,j)*mp.bernpoly(m+1-j,0)*h(s-j)
                       for j in range(m+2))
               -mp.bernpoly(m+1,b)*h(s))/(m+1)
        record('negative_inner_reduction', cont.h((s,mp.mpf(-m)),a,b)-rhs, m=m)
    w = (mp.mpc('.8','.13'),mp.mpc('1.2','-.21'),mp.mpc('-.4','.17'))
    composition = mp.fsum(cont.h(w[:j],a,c)*cont.h(w[j:],c,b)
                          for j in range(4))
    record('depth_three_composition',cont.h(w,a,b)-composition)
    # Cauchy means recover the constant at a singular intersection of the
    # separate Z factors along distinct rays. H itself is entire.
    for p, depth, slopes in [(1,2,(1,2)),(1,2,(2,-.5)),
                             (0,2,(1,2)),(1,3,(1,2,3)),
                             (0,3,(1,2,3))]:
        nodes = 16
        radius = mp.mpf('.002')
        vals = []
        local = Continuation(cutoff=30,order=15)
        for j in range(nodes):
            eps = radius*mp.exp(2j*mp.pi*(j+mp.mpf('.5'))/nodes)
            word = tuple(mp.mpf(p)+mp.mpf(q)*eps for q in slopes)
            vals.append(local.h(word,a,b))
        mean = mp.fsum(vals)/nodes
        target = elementary_diagonal(depth,p,a,b)
        record('Cauchy_intersection',mean-target,base_index=p,depth=depth,
               slopes=list(slopes),nodes=nodes)
    # Independent Gamma root evaluation against an ordinary finite product.
    for u, v in [(mp.mpf('.07'),mp.mpf('-.03')),
                 (mp.mpc('.03','.02'),mp.mpc('.04','-.01'))]:
        bb = mp.mpf('.7'); aa=bb+5
        disc = mp.sqrt(u*u-4*v)
        roots = ((-u+disc)/2,(-u-disc)/2)
        gamma = mp.fprod(mp.gamma(aa-r)*mp.gamma(bb)
                         /(mp.gamma(aa)*mp.gamma(bb-r)) for r in roots)
        direct = mp.fprod(1+u/(bb+n)+v/(bb+n)**2 for n in range(5))
        record('Gamma_alphabet_finite_product',gamma-direct)
    # The normalized primitive is checked by ordinary parameter quadrature.
    for s in (mp.mpc('.4','.2'),mp.mpc('2.1','-.3')):
        target = ((a-b)*mp.zeta(s,b)
                  +(mp.zeta(s-1,a)-mp.zeta(s-1,b))/(s-1))
        direct = mp.quad(lambda x:mp.zeta(s,b)-mp.zeta(s,x),[b,a])
        record('normalized_primitive',target-direct)
    worst = max(mp.mpf(row['absolute_residual']) for row in rows)
    return {'dps':dps,'checks':rows,'max_absolute_residual':mp.nstr(worst,12),
            'status':'floating-point diagnostics; not interval bounds'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'results'/'harmonic_transport_checks.json')
    parser.add_argument('--dps',type=int,default=65)
    parser.add_argument('--exact-only',action='store_true')
    args = parser.parse_args()
    result = {'exact':exact_checks()}
    print('Exact checks passed:',result['exact']['assertions'],flush=True)
    if not args.exact_only:
        result['numeric'] = numeric_checks(args.dps)
        print('Numerical checks:',len(result['numeric']['checks']),
              'maximum residual',result['numeric']['max_absolute_residual'],flush=True)
        assert mp.mpf(result['numeric']['max_absolute_residual']) < mp.mpf('1e-25')
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')


if __name__ == '__main__':
    main()
