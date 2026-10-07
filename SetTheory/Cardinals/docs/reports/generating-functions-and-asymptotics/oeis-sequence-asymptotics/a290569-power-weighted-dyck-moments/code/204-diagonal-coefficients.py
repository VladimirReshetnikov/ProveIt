#!/usr/bin/env python3
"""Finite geometric-multiplicity and independent square-box coefficient engines.

Multiplicities with largest part at most J use the normalized conditional law.
The square-box engine returns an unnormalized partition sum divided by Q(tau).
Ordinary mpmath evaluations are diagnostics, not directed-rounding enclosures.
"""
from fractions import Fraction
from functools import lru_cache
from math import factorial

import mpmath as mp
import sympy as sp


def require(condition, label):
    if not condition:
        raise RuntimeError(label)


def weighted_exponents(budget, weights):
    if not weights:
        yield ()
        return
    for a in range(budget // weights[0] + 1):
        for tail in weighted_exponents(budget - a * weights[0], weights[1:]):
            yield (a,) + tail


@lru_cache(maxsize=None)
def compile_multiplicity(order=4, include_size=False):
    """Compile an exact finite weighted-moment update; symbolic part label j."""
    require(isinstance(order, int) and order >= 1, 'order must be a positive integer')
    S, M, j, h = sp.symbols('S M j h')
    tau, sigma = sp.symbols('tau sigma')
    degrees = tuple(range(1 if include_size else 2, order + 2))
    ds = {k: sp.Symbol('D' + str(k)) for k in degrees}
    variables = (S,) + tuple(ds[k] for k in degrees)
    weights = (1,) + degrees
    states = tuple(weighted_exponents(2 * order, weights))
    index = {e: i for i, e in enumerate(states)}
    shifts = [S + M]
    for k in degrees:
        added = sp.expand(sp.summation(
            sp.expand(((S + h + j)**k - (S + h)**k) / sp.Integer(k)),
            (h, 0, M - 1)))
        require(sp.Poly(added, S, M).total_degree() <= k, 'moment closure degree')
        shifts.append(ds[k] + added)
    polys = []
    poly_index = {}
    transforms = []
    for e in states:
        pol = sp.Poly(sp.prod(x**a for x, a in zip(shifts, e)), *variables, M)
        terms = []
        for power, c in pol.terms():
            require(power[:-1] in index, 'moment closure state')
            cp = tuple((int(p[0]), int(v.p), int(v.q))
                       for p, v in sp.Poly(c, j).terms())
            if cp not in poly_index:
                poly_index[cp] = len(polys)
                polys.append(cp)
            terms.append((index[power[:-1]], power[-1], poly_index[cp]))
        transforms.append(tuple(terms))
    b = [sp.Integer(1)]
    for r in range(1, order + 1):
        value = 0
        for k in range(1, r + 1):
            ak = tau * ds[k + 1]
            if include_size:
                ak += sigma * ds[k]
            value -= k * ak * b[r - k] / sp.Integer(r)
        b.append(sp.expand(value))
    expectations = []
    for br in b:
        terms = []
        for powers, c in sp.Poly(br, *variables, tau, sigma).terms():
            require(powers[:-2] in index, 'coefficient moment closure')
            terms.append((index[powers[:-2]], powers[-2], powers[-1],
                          int(c.p), int(c.q)))
        expectations.append(tuple(terms))
    return {'states': states, 'index': index, 'polynomials': tuple(polys),
            'transforms': tuple(transforms), 'expectations': tuple(expectations),
            'order': order, 'include_size': include_size}


def multiplicity_coefficients(J=200, order=4, tau=1, sigma=0, q=None):
    """Return c_0..c_order with largest part <=J.

    With a Fraction q and rational tau/sigma this uses exact rational arithmetic;
    otherwise q defaults to exp(-tau), evaluated at the current mp.mp.dps.
    The optional formal q is useful for finite algebra checks.
    """
    require(isinstance(J, int) and J >= 0, 'J must be a nonnegative integer')
    rational = isinstance(q, Fraction)
    number = Fraction if rational else mp.mpf
    tau, sigma = number(tau), number(sigma)
    if q is None:
        require(tau > 0, 'tau must be positive')
        q = mp.exp(-tau)
    else:
        q = number(q)
    require(0 < q < 1, 'q must lie between zero and one')
    compiled = compile_multiplicity(order, sigma != 0)
    states = compiled['states']
    index = compiled['index']
    zero, one = number(0), number(1)
    v = [zero] * len(states)
    v[index[(0,) * len(states[0])]] = one
    K = 2 * order
    stirling = [[0] * (K + 1) for _ in range(K + 1)]
    stirling[0][0] = 1
    for n in range(1, K + 1):
        for k in range(1, n + 1):
            stirling[n][k] = stirling[n-1][k-1] + k * stirling[n-1][k]
    for part in range(J, 0, -1):
        z = q**part
        y = z / (1 - z)
        geom = [one] + [sum((stirling[k][l] * factorial(l) * y**l
                            for l in range(1, k + 1)), zero)
                        for k in range(1, K + 1)]
        powers = [part**k for k in range(K + 1)]
        coefficients = [sum((number(num) * powers[degree] / den
                             for degree, num, den in pol), zero)
                        for pol in compiled['polynomials']]
        v = [sum((coefficients[pi] * v[vi] * geom[mi]
                  for vi, mi, pi in terms), zero)
             for terms in compiled['transforms']]
    answer = [sum((number(num) / den * tau**tp * sigma**spow * v[vi]
                   for vi, tp, spow, num, den in terms), zero)
              for terms in compiled['expectations']]
    return answer


def partition_product(tau=1, terms=1200):
    """Finite evaluation of Q(tau); its omitted product tail is separate."""
    tau = mp.mpf(tau)
    require(tau > 0 and terms >= 1, 'positive tau and product cutoff required')
    q = mp.exp(-tau)
    return mp.exp(mp.fsum(-mp.log1p(-q**j) for j in range(1, terms + 1)))


def row_box_coefficients(L=175, order=4, tau=1, sigma=0):
    """Independent O(L^2 order^2) row recurrence, divided by Q(tau).

    This computes only diagrams inside an L by L square. In particular c_0
    is less than one, unlike the normalized multiplicity calculation.
    """
    require(isinstance(L, int) and L >= 0 and order >= 0, 'valid box and order required')
    tau, sigma = mp.mpf(tau), mp.mpf(sigma)
    require(tau > 0, 'tau must be positive')
    q = mp.exp(-tau)
    qpow = [q**j for j in range(L + 1)]
    nxt = [[mp.mpf(1)] + [mp.mpf(0)] * order for _ in range(L + 1)]
    for i in range(L, 0, -1):
        row = [[mp.mpf(1)] + [mp.mpf(0)] * order]
        for j in range(1, L + 1):
            a = [mp.mpf(0)] + [
                tau * mp.mpf((i-1+j)**(r+1) - (i-1)**(r+1)) / (r+1)
                + sigma * mp.mpf((i-1+j)**r - (i-1)**r) / r
                for r in range(1, order + 1)]
            w = [mp.mpf(1)]
            for r in range(1, order + 1):
                w.append(-mp.fsum(k * a[k] * w[r-k] for k in range(1, r+1)) / r)
            row.append([row[j-1][r] + qpow[j] * mp.fsum(
                w[k] * nxt[j][r-k] for k in range(r+1))
                for r in range(order+1)])
        nxt = row
    Q = partition_product(tau)
    return [x / Q for x in nxt[L]]


def logarithmic_coefficients(c):
    """Formal log of 1 + c_1 z + ...; c[0] must be one."""
    require(c[0] == 1, 'logarithmic series requires c_0=1')
    ell = [c[0] * 0]
    for r in range(1, len(c)):
        ell.append(c[r] - sum((j * ell[j] * c[r-j] for j in range(1, r)), c[0] * 0) / r)
    return ell


def normalized_walk(n, tau=1, sigma=0):
    """Normalized height transfer for Z_n(tau*n+sigma)/(n!)^(tau*n+sigma)."""
    require(isinstance(n, int) and n >= 1, 'positive integer n required')
    p = mp.mpf(tau) * n + mp.mpf(sigma)
    states = {0: mp.mpf(1)}
    for step in range(2*n):
        nxt = {}
        for h, w in states.items():
            downs = (step-h) // 2
            ups = step-downs
            if ups < n:
                nxt[h+1] = nxt.get(h+1, 0) + w
            if h:
                factor = (mp.mpf(h) / (n-downs))**p
                nxt[h-1] = nxt.get(h-1, 0) + w * factor
        states = nxt
    return states[0]


def cutoff_majorants(J, r, theta):
    """Evaluate proved diagonal largest-part cutoff majorants (not intervals)."""
    theta = mp.mpf(theta)
    require(r >= 1 and J >= 0 and 0 < theta < 1, 'valid cutoff parameters required')
    require(J + 1 >= 2*r/(1-theta), 'tail monotonicity condition failed')
    # b_r = [z^r] exp(z/(1-z)), using r*b_r=sum_{k=1}^r k*b_{r-k}.
    b = [Fraction(1)]
    for k in range(1, r + 1):
        b.append(sum(j*b[k-j] for j in range(1, k+1)) / k)
    br = mp.mpf(b[r].numerator) / b[r].denominator
    missing = br * mp.exp(mp.pi**2/(6*theta)) * (J+1)**(2*r) * mp.exp(-(1-theta)*(J+1))
    normalization = (br * mp.exp(mp.pi**2/3) * (4*r/mp.e)**(2*r)
                     * mp.exp(-J-1) / (1-mp.exp(-1)))
    return {'majorant_coefficient': str(b[r]), 'missing_tail': missing,
            'normalization': normalization, 'total': missing + normalization}
