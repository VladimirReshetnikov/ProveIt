#!/usr/bin/env python3
"""Finite exact arithmetic for Report181; Python standard library only.

All series below are FINITE formal truncations. They do not evaluate the
infinite formal H-series at any nonzero point and prove no asymptotic bounds.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb, factorial


def need(condition, message):
    if not condition:
        raise ValueError(message)


def degree(n, maximum=10000):
    need(type(n) is int and 0 <= n <= maximum, 'invalid finite degree')
    return n


def product_coefficients(n):
    """Ordinary integer convolution of product (1+q^k prod_{j<=k}(1-q^j)^-1).

    After iteration k, p counts partitions using parts <=k and f is the
    product of its first k factors, truncated through q^n. Each update reads
    the preceding f, not an in-place product. No integer digit packing occurs.
    """
    degree(n)
    p = [1] + [0] * n
    f = p.copy()
    for k in range(1, n + 1):
        for j in range(k, n + 1):
            p[j] += p[j-k]
        new = f.copy()
        for j in range(k, n + 1):
            new[j] += sum(f[i] * p[j-k-i] for i in range(j-k+1))
        f = new
    return f


def composition_count(n):
    """Recursive compositions whose decreasing-run leaders strictly increase."""
    degree(n, 24)
    def walk(left, last, leader):
        if left == 0:
            return 1
        total = 0
        for part in range(1, left+1):
            if last is None or part <= last:
                total += walk(left-part, part, part if last is None else leader)
            elif part > leader:
                total += walk(left-part, part, part)
        return total
    return walk(n, None, 0)


def series_mul(a, b, n):
    degree(n, 100)
    need(len(a) == len(b) == n+1, 'series length mismatch')
    out = [Q(0)] * (n+1)
    for i in range(n+1):
        for j in range(n+1-i):
            out[i+j] += a[i]*b[j]
    return out


def exp_linear(a, n):
    return [Q(a)**j/factorial(j) for j in range(n+1)]


def series_log_one_plus(a, n):
    need(len(a) == n+1 and a[0] == 0, 'log requires zero constant term')
    out = [Q(0)] * (n+1)
    power = [Q(1)] + [Q(0)]*n
    for k in range(1, n+1):
        power = series_mul(power, a, n)
        for j in range(n+1):
            out[j] += Q((-1)**(k+1), k)*power[j]
    return out


def formal_h(n):
    """[z^j] sum_{k=1}^n log(1+e^(kz) prod_{r=1}^k(1-e^(-rz)))."""
    degree(n, 30)
    product = [Q(1)] + [Q(0)]*n
    out = [Q(0)]*(n+1)
    for k in range(1, n+1):
        factor = [-v for v in exp_linear(-k, n)]
        factor[0] += 1
        product = series_mul(product, factor, n)
        term = series_log_one_plus(series_mul(exp_linear(k, n), product, n), n)
        out = [x+y for x,y in zip(out, term)]
    return out


def edgeworth_tuples(h):
    """All m_j with sum_{j=3}^{2h+2}(j-2)m_j=2h, deterministically."""
    degree(h, 6)
    need(h > 0, 'Edgeworth order must be positive')
    js = list(range(3, 2*h+3))
    def walk(position, left, powers):
        if position == len(js):
            if left == 0:
                yield tuple(powers)
            return
        j = js[position]
        for m in range(left//(j-2)+1):
            yield from walk(position+1, left-(j-2)*m, powers+[m])
    return list(walk(0, 2*h, []))


def edgeworth_terms(h):
    """Each row encodes c b^(-J/2) prod kappa_j^m_j exactly."""
    rows = []
    for powers in edgeworth_tuples(h):
        jtotal = sum(j*m for j,m in zip(range(3, 2*h+3), powers))
        need(jtotal % 2 == 0, 'odd Gaussian power')
        half = jtotal//2
        coefficient = Q((-1)**half*factorial(jtotal), 2**half*factorial(half))
        for j,m in zip(range(3, 2*h+3), powers):
            coefficient /= factorial(m)*factorial(j)**m
        rows.append({'coefficient':str(coefficient), 'b_power':-half,
                     'cumulant_powers':list(powers), 'gaussian_degree':jtotal,
                     'weighted_degree':2*h})
    return rows


# Small sparse Laurent polynomial implementation. Keys are tuples of integer
# exponents in a documented ordered basis, and values are exact Fractions.
def poly_constant(q, dimensions):
    q=Q(q)
    return {(0,)*dimensions:q} if q else {}


def poly_monomial(q, powers):
    q=Q(q)
    return {tuple(powers):q} if q else {}


def poly_add(*polys):
    out={}
    for p in polys:
        for powers,q in p.items():
            out[powers]=out.get(powers,Q(0))+q
            if not out[powers]:
                del out[powers]
    return out


def poly_scale(p, q):
    return {powers:v*Q(q) for powers,v in p.items() if v*Q(q)}


def poly_mul(a,b):
    out={}
    for x,p in a.items():
        for y,q in b.items():
            need(len(x)==len(y),'polynomial dimension mismatch')
            powers=tuple(i+j for i,j in zip(x,y))
            out[powers]=out.get(powers,Q(0))+p*q
    return {powers:q for powers,q in out.items() if q}


def poly_pow(p,n):
    degree(n,100)
    need(bool(p),'zero polynomial power requires explicit basis')
    out=poly_constant(1,len(next(iter(p))))
    for _ in range(n):
        out=poly_mul(out,p)
    return out


def poly_rows(p):
    return [{'powers':list(powers),'coefficient':str(q)} for powers,q in sorted(p.items())]


def bernoulli(n):
    """B_n from sum_{k=0}^{m} C(m+1,k) B_k=0 for m>=1."""
    degree(n,100)
    out=[Q(1)]
    for m in range(1,n+1):
        out.append(-sum(Q(comb(m+1,k))*out[k] for k in range(m))/Q(m+1))
    return out


def zeta_negative_odd(m):
    need(type(m) is int and m >= 1 and m % 2 == 1,'negative odd zeta index required')
    return -bernoulli(m+1)[m+1]/(m+1)


def macmahon_coefficients(n):
    return {m:zeta_negative_odd(m-1)*zeta_negative_odd(m+1)/factorial(m)
            for m in range(2,n+1,2)}


def free_energy_polynomial(n=10):
    """Classical-piece Laurent algebra in (t,A,ell,Z), Z=zeta(3).

    Excludes the separately tracked -log(t)/12-zeta'(-1).
    mu=A/t+ell/2-t/24; compute mu^2/(2t)+A/t+mu/2+t/12-Z/t^2
    minus the positive-power MacMahon series, plus formal H.
    """
    degree(n,30)
    term=lambda q,t=0,A=0,ell=0,Z=0:poly_monomial(q,(t,A,ell,Z))
    mu=poly_add(term(1,-1,1),term(Q(1,2),ell=1),term(Q(-1,24),1))
    out=poly_add(poly_mul(term(Q(1,2),-1),poly_pow(mu,2)),term(1,-1,1),
                 poly_scale(mu,Q(1,2)),term(Q(1,12),1),term(-1,-2,Z=1))
    for j,h in enumerate(formal_h(n)):
        out=poly_add(out,term(h,j))
    for j,c in macmahon_coefficients(n).items():
        out=poly_add(out,term(-c,j))
    return out


def edgeworth_leading(h):
    """Substitute b=6 A^2/t^5, k_j=(A^2/2)(3)_j/t^(3+j).

    The two-variable basis is (t,A). This checks only formal leading algebra.
    """
    out={}
    for row in edgeworth_terms(h):
        coefficient=Q(row['coefficient'])*Q(6)**row['b_power']
        tpower=-5*row['b_power']; apower=2*row['b_power']
        for j,m in zip(range(3,2*h+3),row['cumulant_powers']):
            coefficient*=Q(factorial(j+2),4)**m
            tpower-=(j+3)*m; apower+=2*m
        out=poly_add(out,poly_monomial(coefficient,(tpower,apower)))
    return out


def constant_order_identity():
    """Independent Laurent check of the constant-order Legendre cancellation.

    Basis (s,A,D,ell,C); B is replaced by D+A/4.
    """
    term=lambda q,s=0,A=0,D=0,ell=0,C=0:poly_monomial(q,(s,A,D,ell,C))
    u=term(Q(1,2),s=-2,D=1)
    B=poly_add(term(1,D=1),term(Q(1,4),A=1))
    raw=poly_add(poly_mul(term(Q(-10,3),s=-2),poly_pow(u,3)),
                 poly_mul(poly_mul(poly_add(poly_scale(B,6),term(Q(-5,2),A=1)),
                                   term(Q(1,2),s=-4)),poly_pow(u,2)),
                 poly_mul(poly_mul(poly_add(term(Q(1,4),ell=1),term(-1,C=1)),
                                   term(1,s=-2)),u))
    claim=poly_add(term(Q(1,3),s=-8,D=3),term(Q(-1,8),s=-8,A=1,D=2),
                   term(Q(1,8),s=-4,D=1,ell=1),term(Q(-1,2),s=-4,D=1,C=1))
    need(raw==claim,'constant-order identity failed')
    return raw
