#!/usr/bin/env python3
"""Exact checks of the torsion window, using only the Python standard library."""
from fractions import Fraction as F
from itertools import product
from math import comb, inf
from random import Random


def vp(integer, prime):
    if integer == 0:
        return inf
    value = 0
    while integer % prime == 0:
        integer //= prime
        value += 1
    return value


class Cyclotomic:
    """Elements of Z[pi], pi = zeta_(p^H)-1, in the Eisenstein power basis."""

    def __init__(self, p, H):
        self.p = p
        self.order = p**H
        step = self.order // p
        self.degree = (p - 1) * step
        # Phi_(p^H)(1+T) = sum_{k=0}^{p-1} (1+T)^(k*step).
        self.modulus = [
            sum(comb(k*step, j) for k in range(p))
            for j in range(self.degree + 1)
        ]
        assert self.modulus[-1] == 1 and vp(self.modulus[0], p) == 1
        assert all(x % p == 0 for x in self.modulus[:-1])
        self.one = self.reduce([1])
        self.zero = self.reduce([])
        self.zeta = self.reduce([1, 1])
        powers = [self.one]
        for _ in range(1, self.order):
            powers.append(self.mul(powers[-1], self.zeta))
        assert self.mul(powers[-1], self.zeta) == self.one
        self.points = [self.sub(z, self.one) for z in powers]

    def reduce(self, coeffs):
        d = self.degree
        coeffs = list(coeffs) + [0]*max(0, d - len(coeffs))
        while len(coeffs) > d:
            lead = coeffs.pop()
            offset = len(coeffs) - d
            if lead:
                for j, m in enumerate(self.modulus[:-1]):
                    coeffs[offset + j] -= lead * m
        return tuple(coeffs)

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def mul(self, a, b):
        coeffs = [0]*(2*self.degree - 1)
        for j, x in enumerate(a):
            if x:
                for k, y in enumerate(b):
                    coeffs[j+k] += x*y
        return self.reduce(coeffs)

    def val(self, a):
        # Different powers j<degree have distinct valuation classes mod 1.
        return min((F(vp(x, self.p)) + F(j, self.degree)
                    for j, x in enumerate(a) if x), default=inf)

    def poly_at(self, poly, x):
        value = self.zero
        for coeff in reversed(poly):
            value = self.add(self.mul(value, x), coeff)
        return value

    def polynomial(self, roots):
        poly = [self.one]
        for x in roots:
            updated = [self.zero]*(len(poly)+1)
            for j, coeff in enumerate(poly):
                updated[j] = self.sub(updated[j], self.mul(x, coeff))
                updated[j+1] = self.add(updated[j+1], coeff)
            poly = updated
        return poly


def check_exact_field(p, h0, H, rng):
    K = Cyclotomic(p, H)
    m = p**(h0-1)
    n = K.order//m
    D = F(H-h0+1, m)
    rho = F(1, (p-1)*m)
    fibers = [range(a, K.order, n) for a in range(1, n)]
    for offset in (False, True):
        nodes = [K.points[rng.choice(f) if offset else f[0]] for f in fibers]
        P = K.polynomial(nodes)
        assert min(K.val(c) + j*rho for j,c in enumerate(P)) == D
        assert all(K.val(K.poly_at(P, K.points[b])) > D for f in fibers for b in f)
        for j, x in enumerate(nodes):
            others = K.polynomial(nodes[:j] + nodes[j+1:])
            deriv_val = K.val(K.poly_at(others, x))
            assert deriv_val == D - K.val(x)
            assert min(K.val(c) + k*rho for k,c in enumerate(others)) == deriv_val
    # Evaluate mixed-coefficient polynomials directly for budgets < D.
    tested = 0
    for _ in range(40):
        poly = [K.reduce([rng.randrange(-3, 4) for _ in range(3)]) for _ in range(4)]
        A = min(K.val(c) + j*rho for j,c in enumerate(poly))
        baseline = min(K.val(c) for c in poly)
        if A < inf and A - baseline < D:
            assert any(all(K.val(K.poly_at(poly, K.points[b])) <= A for b in f) for f in fibers)
            tested += 1
    print(f"p={p} h0={h0} H={H} threshold={D} coset_size={m} sample_polynomials={tested}")


def check_unramified():
    checked = 0
    for p, h0, H in [(2, 2, 3), (3, 2, 2)]:
        K = Cyclotomic(p,H)
        rho = F(1, (p-1)*p**(h0-1))
        for coeffs in product(range(-p,p+1), repeat=3):
            if not any(coeffs):
                continue
            A = min(vp(c,p)+j*rho for j,c in enumerate(coeffs))
            if A - min(vp(c,p) for c in coeffs) >= H-h0+1:
                continue
            fs = [K.reduce([c]) for c in coeffs]
            shells = [[b for b in range(1,K.order) if H-vp(b,p)==h] for h in range(h0,H+1)]
            assert any(all(K.val(K.poly_at(fs,K.points[b]))<=A for b in shell) for shell in shells)
            checked += 1
    print(f"Unramified whole-shell tests: {checked}")


if __name__ == '__main__':
    rng = Random(20261125)
    for case in [(2,1,1), (2,1,3), (2,2,4), (2,3,4), (3,1,2), (3,2,3), (3,2,4), (5,2,2)]:
        check_exact_field(*case, rng)
    check_unramified()
