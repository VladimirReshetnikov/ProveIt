#!/usr/bin/env python3
"""Finite certificates for the arbitrary-phase order-five cube formulas.

Only Python's standard library is required.  The proof of the asymptotic
maximum is in order5_exact_optimization.tex; this script verifies the exact
identities and coefficient arithmetic on which that proof depends.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import cos, pi, sqrt
import cmath
import csv
from pathlib import Path
import random


def coefficients(delta, rho, b, alpha, beta):
    A, B = rho * cmath.exp(1j * alpha), b * cmath.exp(1j * beta)
    return [complex(delta), A, B, B.conjugate(), A.conjugate()]


def direct_cube(a):
    vals = [sum(a[r] * cmath.exp(2j * pi * r * x / 5)
                for r in range(5)).real for x in range(5)]
    total = 0.0
    vertices = tuple(product((0, 1), repeat=3))
    for x, h1, h2, h3 in product(range(5), repeat=4):
        term = 1.0
        for v in vertices:
            term *= vals[(x + v[0]*h1 + v[1]*h2 + v[2]*h3) % 5]
        total += term
    return total / 625


def all_T(a):
    return {(s,t): sum(a[r] * a[(r+s)%5].conjugate()
                       * a[(r+t)%5].conjugate() * a[(r+s+t)%5]
                       for r in range(5))
            for s,t in product(range(5), repeat=2)}


def table_T(delta, rho, b, alpha, beta):
    theta, phi = 2*alpha-beta, 3*alpha+beta
    psi = phi-theta
    return [
        (1, delta**4+2*rho**4+2*b**4),
        (4, 2*delta**2*rho**2+2*rho**2*b**2+b**4),
        (4, 2*delta**2*b**2+2*rho**2*b**2+rho**4),
        (4, delta**2*rho**2+2*delta*rho**2*b*cos(theta)
            +2*rho*b**3*cos(2*theta-phi)),
        (4, delta**2*b**2+2*delta*rho*b**2*cos(psi)
            +2*rho**3*b*cos(phi)),
        (8, rho**2*b**2+2*delta*rho**2*b*cos(theta)
            +2*delta*rho*b**2*cos(psi)),
    ]


def norm_formula(rho, b, alpha, beta):
    theta, phi = 2*alpha-beta, 3*alpha+beta
    return (8*rho**8 + 16*(1+cos(phi)**2)*rho**6*b**2
            +48*rho**4*b**4
            +16*(1+cos(2*theta-phi)**2)*rho**2*b**6+8*b**8)


def full_formula(delta, rho, b, alpha, beta):
    theta, phi = 2*alpha-beta, 3*alpha+beta
    psi = phi-theta
    return (
        delta**8+24*delta**4*(rho**4+b**4)
        +16*delta**3*(rho**4*b*cos(theta)+rho*b**4*cos(psi))
        +24*delta**2*((3+cos(2*theta))*rho**4*b**2
            +(3+cos(2*psi))*rho**2*b**4
            +2*rho**3*b**3*(cos(phi)+cos(2*theta-phi)))
        +16*delta*(rho**4*b**3*(3*cos(theta)+cos(2*phi-theta))
            +rho**3*b**4*(3*cos(psi)+cos(3*theta-phi)))
        +norm_formula(rho,b,alpha,beta)
    )


def cube_monomials():
    """a_0^c0 a_1^c1 ... a_4^c4, with exact integer coefficients."""
    counts = Counter()
    for s,t,v,w in product(range(5), repeat=4):
        frequencies = [s+t+v+2*w, -s-t-w, -s-v-w, s,
                       -t-v-w, t, v, w]
        c = Counter(r % 5 for r in frequencies)
        counts[tuple(c[r] for r in range(5))] += 1
    assert sum(counts.values()) == 625
    assert all(sum(powers) == 8 for powers in counts)
    return counts


def evaluate_monomials(counts, a):
    total = 0j
    for powers, multiplicity in counts.items():
        term = complex(multiplicity)
        for r in range(5):
            term *= a[r] ** powers[r]
        total += term
    return total


def rational_series():
    degree = 4
    def add(*polys):
        return [sum(p[i] if i<len(p) else F(0) for p in polys)
                for i in range(degree+1)]
    def mul(p,q):
        return [sum(p[j]*q[i-j] for j in range(i+1)
                    if j<len(p) and i-j<len(q)) for i in range(degree+1)]
    def scale(p,c): return [v*c for v in p]
    def power(p,n):
        out = [F(1)]+[F(0)]*degree
        for _ in range(n): out = mul(out,p)
        return out
    z = [F(0),F(1)]+[F(0)]*(degree-1)
    X = [F(1)]+[F(0)]*degree
    for i in range(1,degree+1):
        P = add(power(X,4), scale(mul(power(X,3),z),2),
                scale(mul(power(X,2),power(z,2)),6),
                scale(mul(X,power(z,3)),2), power(z,4))
        X[i] = -P[i]/4
    assert X == [F(1),-F(1,2),-F(9,8),F(3,4),F(39,128)]
    square = power(X,2)
    assert square[:4] == [F(1),-F(1),-F(2),F(21,8)]
    # k0=q/3, q^4=1/8.  No floating point is used in this evaluation.
    C8 = F(1)-F(24,81)*F(1,8)-F(16,27)*F(1,8)+F(96,9)*F(1,8)
    assert C8 == F(20,9)
    return X, C8


def main():
    counts = cube_monomials()
    csv_path = Path(__file__).resolve().parents[1] / 'data' / 'order5_cube_fourier_certificate.csv'
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    with csv_path.open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['a0_power','a1_power','a2_power','a3_power','a4_power',
                         'multiplicity'])
        for powers, multiplicity in sorted(counts.items()):
            writer.writerow([*powers, multiplicity])
    rng = random.Random(20261006)
    worst = 0.0
    for _ in range(24):
        delta,rho,b = [rng.uniform(.03,.95) for _ in range(3)]
        alpha,beta = [rng.uniform(-pi,pi) for _ in range(2)]
        a = coefficients(delta,rho,b,alpha,beta)
        ref = direct_cube(a)
        T = all_T(a)
        candidates = [sum(abs(v)**2 for v in T.values()),
                      sum(m*v*v for m,v in table_T(delta,rho,b,alpha,beta)),
                      full_formula(delta,rho,b,alpha,beta),
                      evaluate_monomials(counts,a)]
        assert max(abs(v.imag) for v in T.values()) < 1e-12
        for value in candidates:
            error = abs(value-ref)/max(1,abs(ref))
            worst = max(worst,error)
            assert error < 3e-12, (ref,value,error)
        centered = direct_cube(coefficients(0,rho,b,alpha,beta))
        assert abs(centered-norm_formula(rho,b,alpha,beta)) < 3e-11
    X,C8 = rational_series()
    print('PASS: exact enumeration has 625 assignments and',len(counts),'monomials.')
    print('PASS: direct cube, Fourier T, six-slot table, monomials, and full polynomial agree.')
    print('Maximum relative floating point discrepancy:',format(worst,'.3g'))
    print('PASS: exact rational X coefficients:', ', '.join(map(str,X)))
    print('PASS: exact order-eight coefficient:',C8)
    print('Certificate:',csv_path)


if __name__ == '__main__':
    main()
