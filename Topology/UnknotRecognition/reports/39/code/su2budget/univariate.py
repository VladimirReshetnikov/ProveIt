"""Exact two-meridian traceless SU(2) feasibility by Q[t] gcd and Sturm.

Output concerns the supplied presentation, not the topology of an unchecked PD.
A meridian flag declares a precondition; it is never accepted as a proof of it.
Only an upstream independently verified knot/meridian certificate permits
mapping EXISTS to KNOTTED and NONE to UNKNOT.
"""
from __future__ import annotations
from fractions import Fraction
from functools import reduce
from math import gcd, lcm
from dataclasses import dataclass
from .slp import Presentation, LimitExceeded


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return tuple(a)


def add(a, b):
    out = [0] * max(len(a), len(b))
    for i, c in enumerate(a): out[i] += c
    for i, c in enumerate(b): out[i] += c
    return trim(out)


def neg(a):
    return tuple(-x for x in a)


def sub(a, b):
    return add(a, neg(b))


@dataclass
class Budget:
    max_degree: int = 2048
    max_coefficient_bits: int = 100000
    max_pairs: int = 20000000
    pairs: int = 0
    peak_degree: int = 0
    peak_bits: int = 0
    check: object = lambda: None

    def inspect(self, a):
        self.check()
        degree = max(0, len(a)-1)
        bits = max((max(abs(Fraction(x).numerator).bit_length(),
                        Fraction(x).denominator.bit_length()) for x in a), default=0)
        if degree > self.max_degree:
            raise LimitExceeded('univariate degree cap')
        if bits > self.max_coefficient_bits:
            raise LimitExceeded('univariate coefficient bit cap')
        self.peak_degree = max(self.peak_degree, degree)
        self.peak_bits = max(self.peak_bits, bits)
        return a

    def charge(self, amount):
        self.check()
        if self.pairs + amount > self.max_pairs:
            raise LimitExceeded('univariate arithmetic work cap')
        self.pairs += amount


def mul(a, b, budget=None):
    if not a or not b:
        return ()
    if budget:
        if len(a)+len(b)-2 > budget.max_degree:
            raise LimitExceeded('univariate degree cap before multiplication')
        budget.charge(len(a)*len(b))
    out = [0] * (len(a)+len(b)-1)
    for i, c in enumerate(a):
        for j, d in enumerate(b): out[i+j] += c*d
    out = trim(out)
    return budget.inspect(out) if budget else out


def power(a, e, budget=None):
    out = (1,)
    while e:
        if e & 1: out = mul(out, a, budget)
        e >>= 1
        if e: a = mul(a, a, budget)
    return out


def primitive(a, positive_leading=False):
    """Multiply by a positive rational, unless positive_leading requested."""
    a = trim(a)
    if not a: return ()
    den = lcm(*(Fraction(c).denominator for c in a))
    nums = [int(Fraction(c)*den) for c in a]
    content = reduce(gcd, (abs(c) for c in nums))
    nums = [c//content for c in nums]
    if positive_leading and nums[-1] < 0:
        nums = [-c for c in nums]
    return tuple(nums)


def divrem(a, b, budget=None):
    if not b: raise ZeroDivisionError('zero polynomial')
    r = list(map(Fraction, a))
    b = tuple(map(Fraction, b))
    quotient = [Fraction(0)] * max(0, len(a)-len(b)+1)
    while r and len(r) >= len(b):
        if budget: budget.charge(len(b))
        k, scale = len(r)-len(b), r[-1]/b[-1]
        quotient[k] += scale
        for j, c in enumerate(b): r[k+j] -= scale*c
        r = list(trim(r))
        if budget: budget.inspect(r)
    return trim(quotient), trim(r)


def polynomial_gcd(a, b, budget=None):
    a, b = primitive(a, True), primitive(b, True)
    while b:
        _, r = divrem(a, b, budget)
        a, b = b, primitive(r, True)
    return primitive(a, True)


def derivative(a):
    return trim(i*a[i] for i in range(1, len(a)))


def variations(signs):
    nonzero = [s for s in signs if s]
    return sum(a != b for a, b in zip(nonzero, nonzero[1:]))


def sign(x):
    return (x > 0) - (x < 0)


def positive_roots(g, budget=None):
    """Number of distinct positive real roots; None means zero polynomial."""
    g = primitive(g, True)
    if not g:
        return dict(count=None, polynomial=[], sturm=[], at_zero=[], at_infinity=[])
    while len(g) > 1 and not g[0]:
        g = g[1:]  # zero is outside the open domain t>0
    if len(g) <= 1:
        return dict(count=0, polynomial=list(g), sturm=[list(g)],
                    at_zero=[sign(g[0])], at_infinity=[sign(g[-1])])
    repeated = polynomial_gcd(g, derivative(g), budget)
    quotient, remainder = divrem(g, repeated, budget)
    assert not remainder
    g = primitive(quotient, True)
    chain = [g, primitive(derivative(g))]
    while chain[-1]:
        _, r = divrem(chain[-2], chain[-1], budget)
        if not r: break
        # Positive scaling preserves Sturm signs; do NOT force leading positive.
        chain.append(primitive(neg(r)))
    zero = [sign(f[0]) for f in chain]
    infinity = [sign(f[-1]) for f in chain]
    return dict(count=variations(zero)-variations(infinity), polynomial=list(g),
                sturm=[list(f) for f in chain], at_zero=zero, at_infinity=infinity)


def qmul(p, q, budget):
    a,b,c,d = p; e,f,g,h = q
    M = lambda x,y: mul(x,y,budget)
    return (sub(sub(sub(M(a,e),M(b,f)),M(c,g)),M(d,h)),
            sub(add(add(M(a,f),M(b,e)),M(c,h)),M(d,g)),
            add(add(sub(M(a,g),M(b,h)),M(c,e)),M(d,f)),
            add(sub(add(M(a,h),M(b,g)),M(c,f)),M(d,e)))


def residuals(p: Presentation, budget=None):
    if p.rank != 2 or not p.meridian_generators:
        raise ValueError('requires exactly two declared meridian generators')
    budget = budget or Budget()
    # Preflight without expanding coefficients. This accounts for represented
    # B multiplicities, not merely the number of SLP nodes.
    ecount = {0: 0}
    for v in p.live():
        r = p.rules[v]
        e = int(abs(r[1]) == 2) if r[0] == 't' else ecount[r[1]]+ecount[r[2]]
        if 2*e > budget.max_degree:
            raise LimitExceeded('represented B-degree cap (preflight)')
        ecount[v] = e
    I = ((1,), (), (), ())
    A = ((), (1,), (), ())
    B = ((), (1,0,-1), (0,2), ())
    values = {0: I}
    for v in p.live():
        r = p.rules[v]
        if r[0] == 't':
            out = A if abs(r[1]) == 1 else B
            if r[1] < 0: out = tuple(neg(x) for x in out)
        else:
            out = qmul(values[r[1]], values[r[2]], budget)
        values[v] = out
        for polynomial in out: budget.inspect(polynomial)
    result = []
    dcache = {0: (1,)}
    def denom_power(e):
        if e not in dcache: dcache[e] = power((1,0,1),e,budget)
        return dcache[e]
    for u,v in p.relations:
        e = max(ecount[u], ecount[v])
        pu, pv = denom_power(e-ecount[u]), denom_power(e-ecount[v])
        for a,b in zip(values[u],values[v]):
            result.append(budget.inspect(sub(mul(a,pu,budget),mul(b,pv,budget))))
    return tuple(result), budget


def solve(p: Presentation, *, budget=None):
    """Return EXISTS, NONE, or UNKNOWN. Invalid input raises ValueError."""
    budget = budget or Budget()
    try:
        polynomials, budget = residuals(p,budget)
        g = ()
        for f in polynomials:
            g = polynomial_gcd(g,f,budget)
            if len(g) == 1: break
        roots = positive_roots(g,budget)
        answer = 'EXISTS' if roots['count'] is None or roots['count'] > 0 else 'NONE'
        return dict(status=answer, presentation_digest=p.digest(), gcd=list(g),
                    roots=roots, residuals=[list(f) for f in polynomials],
                    work=budget.pairs, peak_degree=budget.peak_degree,
                    peak_coefficient_bits=budget.peak_bits,
                    scope='two-generator meridian-traceless representation feasibility; '
                          'knot provenance must be independently verified')
    except LimitExceeded as exc:
        return dict(status='UNKNOWN', presentation_digest=p.digest(), reason=str(exc),
                    work=budget.pairs, scope='no mathematical conclusion')


def verify(p: Presentation, certificate: dict, *, budget=None) -> bool:
    """Replay from source presentation, not supplied residuals or sign lists.

    This shares the arithmetic kernel with solve; external SymPy/Wolfram checks
    in the package are the independent implementation comparisons.
    """
    if certificate.get('status') not in ('EXISTS','NONE'):
        return False
    answer = solve(p,budget=budget)
    keys = ('status','presentation_digest','gcd','roots','residuals')
    return all(answer.get(k) == certificate.get(k) for k in keys)
