"""Certify a zero-free central interval from ten real log derivatives.

Python 3.11+ standard library. The only non-computational inputs are Dirichlet
GRH, the quadratic functional equation, the Hadamard product, and the bounds
on psi (Chebyshev) and digamma described in the accompanying proof.
"""
from decimal import Decimal, getcontext
from math import comb, isqrt

getcontext().prec = 38
D = Decimal

class I:
    """Closed decimal interval. Each rounded operation is expanded by one ulp."""
    def __init__(self, lo, hi=None):
        self.lo = D(lo)
        self.hi = self.lo if hi is None else D(hi)

    def __add__(self, other):
        y = as_interval(other)
        return I((self.lo + y.lo).next_minus(), (self.hi + y.hi).next_plus())
    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-as_interval(other))
    def __rsub__(self, other):
        return as_interval(other) + (-self)

    def __mul__(self, other):
        y = as_interval(other)
        values = [u * v for u in (self.lo, self.hi) for v in (y.lo, y.hi)]
        return I(min(values).next_minus(), max(values).next_plus())
    __rmul__ = __mul__

    def __truediv__(self, other):
        y = as_interval(other)
        assert not (y.lo <= 0 <= y.hi)
        return self * I((1/y.hi).next_minus(), (1/y.lo).next_plus())

    def ln(self):
        return I(self.lo.ln().next_minus(), self.hi.ln().next_plus())
    def exp(self):
        return I(self.lo.exp().next_minus(), self.hi.exp().next_plus())
    def sqrt(self):
        return I(self.lo.sqrt().next_minus(), self.hi.sqrt().next_plus())

def as_interval(x):
    return x if isinstance(x, I) else I(x)

def primes_to(n):
    flags = bytearray(b'\x01') * (n+1)
    for p in range(2, isqrt(n)+1):
        if flags[p]:
            flags[p*p::p] = b'\x00' * ((n-p*p)//p + 1)
    return [p for p in range(2, n+1) if flags[p]]

def digamma(x):
    y = x + 128
    base = y.ln() - I(1)/(2*y)
    error = I(1)/(12*y*y)
    base = I((base.lo-error.hi).next_minus(), base.hi)
    return base - sum(I(1)/(x+i) for i in range(128))

def test(q, k, n, g):
    assert q>2 and q%2 and all(q%p for p in primes_to(isqrt(q)))
    parity = (q-1)//2 % 2
    logqpi = (I(q) / I((I(333)/106).lo, (I(355)/113).hi)).ln()
    terms = []
    for p in primes_to(n):
        lp = I(p).ln()
        eps = pow(p,(q-1)//2,q)
        eps = -1 if eps==q-1 else eps
        assert eps in (-1,0,1)
        power, chi, l_power = p, eps, lp
        while power <= n:
            terms.append((l_power, chi*lp))
            power *= p
            l_power, chi = l_power+lp, chi*eps
    logn = I(n).ln()
    psi_bound = 4*I(2).ln()
    B, gap_weight = I(0), I(2)
    for j in range(1,k+1):
        a = I(j).sqrt()
        s = I('0.5')+a
        prime_sum = sum(weight*(-s*log_power).exp() for log_power,weight in terms)
        tail = psi_bound * s/(s-1) * ((1-s)*logn).exp()
        d = (logqpi+digamma((s+parity)/2))/2 - prime_sum + I(-tail.hi,tail.hi)
        B = B + ((-1)**(j-1)*comb(k,j))*a*d
        gap_weight = gap_weight * I(j)/(I(j)+g*g)
    print('q =',q,'k =',k,'N =',n)
    print('B_k in [',B.lo,',',B.hi,']')
    print('2 K_k(g^2) in [',gap_weight.lo,',',gap_weight.hi,']')
    assert B.hi < gap_weight.lo
    print('PASS: no zero for |Im(s)| <=',g.lo,'on the critical line.')

if __name__ == '__main__':
    test(1000004329, 10, 65536, I('0.2'))
