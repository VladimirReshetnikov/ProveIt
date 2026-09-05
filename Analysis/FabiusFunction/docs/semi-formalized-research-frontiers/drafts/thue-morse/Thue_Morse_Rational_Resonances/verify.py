#!/usr/bin/env python3
"""Reproduce the algebraic and numerical checks in the accompanying article.

Run: python verify.py --output results
Dependencies: Python >= 3.10, sympy, mpmath.

The exact tests use arithmetic in Q[x]/Phi_q(x), not floating-point roots of
unity.  The analytic experiments use high precision, but are checks, not
interval-arithmetic certificates or substitutes for the proofs in the paper.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable
import mpmath as mp
import sympy as sp

X = sp.Symbol('x')

class CyclotomicRing:
    """Small exact quotient ring with rational coefficients.

    A ring element is a fixed-length tuple of Fraction objects. Only the
    denominators 1-x^a (a not divisible by q) need polynomial inversion;
    SymPy performs those inversions and the result is cached.
    """
    def __init__(self, q: int):
        if q < 2:
            raise ValueError('q must be at least 2')
        self.q = q
        self.phi = sp.Poly(sp.cyclotomic_poly(q, X), X, domain=sp.QQ)
        self.d = self.phi.degree()
        self.low = tuple(F(self.phi.nth(i)) for i in range(self.d))
        self.zero = (F(0),) * self.d
        self.one = (F(1),) + (F(0),) * (self.d - 1)
        self.x = self.reduce([0, 1])
        self.powers = [self.pow(self.x, j) for j in range(q)]
        self._inverses: dict[int, tuple[F, ...]] = {}

    def reduce(self, vals: Iterable) -> tuple[F, ...]:
        a = [F(v) for v in vals]
        a.extend([F(0)] * max(0, self.d - len(a)))
        for k in range(len(a) - 1, self.d - 1, -1):
            if a[k]:
                for j in range(self.d):
                    a[k - self.d + j] -= a[k] * self.low[j]
        return tuple(a[:self.d])

    def add(self, a, b):
        return tuple(u + v for u, v in zip(a, b))

    def scale(self, a, c):
        c = F(c)
        return tuple(v * c for v in a)

    def mul(self, a, b):
        v = [F(0)] * (2 * self.d - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        v[i + j] += x * y
        return self.reduce(v)

    def pow(self, a, n: int):
        if n < 0:
            raise ValueError('negative exponent not supported here')
        ans = self.one
        while n:
            if n & 1:
                ans = self.mul(ans, a)
            a = self.mul(a, a)
            n >>= 1
        return ans

    def root(self, a: int):
        return self.powers[a % self.q]

    def inv_one_minus_root(self, a: int):
        a %= self.q
        if a == 0:
            raise ZeroDivisionError('root is 1')
        if a not in self._inverses:
            poly = sp.Poly(sp.invert(1 - X**a, self.phi.as_expr(), X), X)
            self._inverses[a] = self.reduce(poly.nth(i) for i in range(self.d))
        return self._inverses[a]

    def li(self, n: int, a: int):
        """Li_{1-n}(x^a), as a rational function in the quotient ring."""
        if n < 1:
            raise ValueError('n must be positive')
        expr = X / (1 - X)
        for _ in range(n - 1):
            expr = sp.cancel(X * sp.diff(expr, X))
        # Multiplication by (1-x)^n leaves an Eulerian polynomial.
        num = sp.Poly(sp.cancel(expr * (1 - X)**n), X)
        numerator = self.zero
        for (j,), v in num.terms():
            numerator = self.add(numerator, self.scale(self.root(a * j), F(v)))
        return self.mul(numerator, self.pow(self.inv_one_minus_root(a), n))

    def exp_coefficients(self, cumulants: list, order: int):
        """Coefficient recurrence used ONLY to independently evaluate Bell sums.

        If exp(sum kappa_n z^n/n!) = sum h_n z^n, then
        n h_n = sum_{j=1}^n kappa_j h_{n-j}/(j-1)!.
        The article itself gives nonrecursive finite partition formulas.
        """
        h = [self.one]
        for n in range(1, order + 1):
            value = self.zero
            for j in range(1, n + 1):
                term = self.mul(cumulants[j - 1], h[n - j])
                value = self.add(value, self.scale(term, F(1, math.factorial(j - 1))))
            h.append(self.scale(value, F(1, n)))
        return h

    def to_mp(self, a):
        root = mp.exp(2j * mp.pi / self.q)
        return sum(mp.mpf(v.numerator) / v.denominator * root**j
                   for j, v in enumerate(a))


def order_two(q: int) -> int:
    if q < 3 or q % 2 == 0:
        raise ValueError('q must be odd and at least 3')
    return int(sp.n_order(2, q))


def cumulants(ring: CyclotomicRing, phase: int, order: int):
    L = order_two(ring.q)
    ans = []
    for n in range(1, order + 1):
        value = ring.zero
        for k in range(1, L + 1):
            exponent = pow(2, (phase - k) % L, ring.q)
            value = ring.add(value, ring.scale(ring.li(n, exponent), F(1, 2**(k*n))))
        ans.append(ring.scale(value, -F(1, 1 - F(1, 2**(L*n)))))
    return ans


def direct_moment(ring: CyclotomicRing, m: int, h: int):
    ans = ring.zero
    for n in range(2**m):
        ans = ring.add(ans, ring.scale(ring.root(n), (-1)**n.bit_count() * n**h))
    return ans


def exact_checks():
    count = 0
    for q in (3, 5, 7, 9):
        ring = CyclotomicRing(q)
        L = order_two(q)
        cache = {s: cumulants(ring, s, 6) for s in range(L)}
        for m in range(9):
            b = ring.one
            for j in range(m):
                b = ring.mul(b, ring.add(ring.one, ring.scale(ring.root(2**j), -1)))
            ks = [ring.add(ring.scale(cache[m % L][n-1], 2**(m*n)),
                           ring.scale(cache[0][n-1], -1)) for n in range(1, 7)]
            hcoef = ring.exp_coefficients(ks, 6)
            for h in range(7):
                prediction = ring.scale(ring.mul(b, hcoef[h]), math.factorial(h))
                assert prediction == direct_moment(ring, m, h), (q, m, h)
                count += 1
    dyadic_count = 0
    for r in range(1, 5):
        ring = CyclotomicRing(2**r)
        head = ring.one
        for j in range(r):
            head = ring.mul(head, ring.add(ring.one, ring.scale(ring.root(2**j), -1)))
        for M in range(6):
            m = r + M
            ks = []
            for n in range(1, 4):
                hn = ring.zero
                for j in range(r):
                    hn = ring.add(hn, ring.scale(ring.li(n, 2**j), -(2**(j*n))))
                beta = F(1, 2) if n == 1 else F(sp.bernoulli(n)) / n
                tail = beta * F(2**(m*n) - 2**(r*n), 2**n - 1)
                ks.append(ring.add(hn, ring.scale(ring.one, tail)))
            hc = ring.exp_coefficients(ks, 3)
            scale = (-1)**M * 2**(M*(2*r + M - 1)//2)
            for h in range(M):
                assert direct_moment(ring, m, h) == ring.zero, (r, M, h)
                dyadic_count += 1
            for h in range(4):
                prediction = ring.scale(ring.mul(head, hc[h]), scale*math.factorial(M+h))
                assert direct_moment(ring, m, M+h) == prediction, (r, M, h)
                dyadic_count += 1
    residue_rows = []
    for t in range(1, 6):
        N = 4**t
        vals = [sum((-1)**n.bit_count()*n**h for n in range(0, N, 3)) for h in range(4)]
        assert vals[0] == 2*3**(t-1)
        assert vals[1] == 3**(t-1)*(N-1)
        if t >= 2:
            assert vals[2] == 3**(t-1)*(19*N*N - 26*N + 7)//27
            assert vals[3] == 3**(t-1)*(N-1)*(5*N*N - 4*N - 1)//9
        residue_rows.append([t, N] + vals)
    return {'odd_order_exact_equalities': count,
            'dyadic_exact_equalities': dyadic_count,
            'modulo_three_rows': residue_rows}


def g(z):
    return mp.expm1(z)/z if z != 0 else mp.mpf(1)


def U(z, depth: int = 270):
    return mp.fprod(g(z/mp.mpf(2)**k) for k in range(1, depth+1))


def H(q: int, a: int, phase: int, z, depth: int = 270):
    L = order_two(q)
    root = mp.exp(2j*mp.pi/q)
    out = mp.mpc(1)
    for k in range(1, depth+1):
        b = root**((a*pow(2, (phase-k) % L, q)) % q)
        out *= (1 - b*mp.exp(z/mp.mpf(2)**k))/(1-b)
    return out


def Q(q: int, a: int, m: int, z):
    root = mp.exp(2j*mp.pi/q)
    return mp.fprod((1-root**((a*pow(2,j,q))%q)*mp.exp(z/mp.mpf(2)**(m-j))) /
                   (1-root**((a*pow(2,j,q))%q)) for j in range(m))


def numeric_checks():
    mp.mp.dps = 65
    z = mp.mpc(1, mp.mpf(1)/3)
    ring = CyclotomicRing(3)
    kappa = cumulants(ring, 0, 3)
    cs = ring.exp_coefficients([ring.scale(k, -1) for k in kappa], 3)
    cs = [ring.to_mp(c) for c in cs]
    rows = []
    for m in (4,8,12,16):
        h = H(3,1,0,z)
        actual = Q(3,1,m,z)
        approx = h*sum(cs[k]*(z/mp.mpf(2)**m)**k for k in range(4))
        rows.append([m, mp.nstr(abs(actual-h), 12), mp.nstr(abs(actual-approx), 12)])
    tail_errors=[]
    for q in (3,5,7,9,15):
        for m in (0,1,3,8):
            rhs = Q(q,1,m,z)*H(q,1,0,z/mp.mpf(2)**m)
            tail_errors.append(abs(rhs-H(q,1,m % order_two(q),z)))
    assert max(tail_errors) < mp.mpf('1e-58')
    norm_errors=[]
    for q in (3,5,7,9,15):
        norm=mp.fprod(H(q,a,0,z) for a in range(1,q))
        norm_errors.append(abs(norm-U(q*z)/U(z)))
    assert max(norm_errors) < mp.mpf('1e-55')
    gaussian=[]
    hierarchy=[]
    c=2j*mp.pi
    for p in (0,1,2):
        for M in (2,3,4,5,6,7,8):
            eps=mp.mpf(2)**(-M)
            r=2**((p+1)*M)  # r eps^(p+1) = 1 exactly
            depth=min(r,270)
            subtract=sum((-1)**(j-1)*(eps*z/c)**j/j for j in range(1,p+1))
            logarithm=r*(mp.log1p(eps*z/c)-subtract)
            value=U(z)/U(eps*z)*mp.exp(logarithm)*U(c+eps*z,depth)/U(c,depth)
            limit=U(z)*mp.exp((-1)**p*(z/c)**(p+1)/(p+1))
            row=[p,M,r,mp.nstr(abs(value-limit),12)]
            hierarchy.append(row)
            if p==1:
                gaussian.append([M,r,row[-1]])
    return {'precision_decimal_digits':mp.mp.dps,'product_depth':270,
            'finite_depth_errors':rows,
            'max_tail_identity_residual':mp.nstr(max(tail_errors),8),
            'max_cyclotomic_norm_residual':mp.nstr(max(norm_errors),8),
            'gaussian_errors':gaussian,'hierarchy_errors':hierarchy}


def save_csv(path, header, rows):
    with path.open('w',newline='',encoding='utf-8') as f:
        w=csv.writer(f);w.writerow(header);w.writerows(rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('results'))
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    report={'exact':exact_checks(),'numerical':numeric_checks(),
            'versions':{'sympy':sp.__version__,'mpmath':mp.__version__}}
    (args.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    save_csv(args.output/'modulo_three_moments.csv',['t','4^t','degree_0','degree_1','degree_2','degree_3'],report['exact']['modulo_three_rows'])
    save_csv(args.output/'finite_depth_errors.csv',['m','uncorrected_error','cubic_corrected_error'],report['numerical']['finite_depth_errors'])
    save_csv(args.output/'gaussian_limit_errors.csv',['M','r=4^M','absolute_error'],report['numerical']['gaussian_errors'])
    save_csv(args.output/'hierarchy_errors.csv',['p','M','r','absolute_error'],report['numerical']['hierarchy_errors'])
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
