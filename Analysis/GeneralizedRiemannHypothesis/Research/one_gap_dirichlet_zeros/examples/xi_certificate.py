#!/usr/bin/env python3
"""Interval certificate for two marked balance points of the Riemann Xi function.

Run python3 xi_certificate.py, or add --high for orders 65 and 67.
Only the Python standard library is needed.
Scaled integer endpoints enclose all algebraic operations. Exponentials
use Decimal.exp, correctly rounded to nearest, widened by one Decimal ulp.
No zeta values, zero tables, or floating-point quadrature are inputs.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import comb

PLACES = 70
S = 10**PLACES
N = 44
PANEL_DEN = 32
NODES = 20
LAST_N = 5
BASE_ORDER = 9
BISECTIONS = 79
ERROR = F(1, 10**26)

def high_order_settings():
    global PLACES, S, N, NODES, LAST_N, BASE_ORDER, BISECTIONS, ERROR
    PLACES, N, NODES, LAST_N, BASE_ORDER, BISECTIONS = 170, 182, 80, 10, 65, 325
    S = 10**PLACES
    ERROR = F(1, 10**116)


class I:
    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi
        assert self.lo <= self.hi

    def __add__(self, y):
        y = iv(y)
        return I(self.lo + y.lo, self.hi + y.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, y):
        return self + (-iv(y))

    def __rsub__(self, y):
        return iv(y) - self

    def __mul__(self, y):
        y = iv(y)
        ends = [a*b for a in (self.lo, self.hi) for b in (y.lo, y.hi)]
        return I(min(ends)//S, -((-max(ends))//S))

    __rmul__ = __mul__

    def __truediv__(self, y):
        y = iv(y)
        assert y.lo > 0 or y.hi < 0
        return self * I(S*S//y.hi, -((-S*S)//y.lo))

    def __rtruediv__(self, y):
        return iv(y) / self

    def __pow__(self, k):
        if k < 0:
            return 1 / (self**(-k))
        if k == 0:
            return iv(1)
        half = self**(k//2)
        return half*half*self if k % 2 else half*half

    def __lt__(self, y):
        return self.hi < iv(y).lo

    def exp(self):
        with localcontext() as ctx:
            ctx.prec = PLACES + 25
            def endpoint(n, direction):
                # scaleb is exact for the bounded-size input endpoints here.
                x = Decimal(n).scaleb(-PLACES)
                assert F(x) == F(n, S)
                z = x.exp()
                z = z.next_minus() if direction < 0 else z.next_plus()
                return iv(F(z))
            return I(endpoint(self.lo, -1).lo, endpoint(self.hi, 1).hi)

    def display(self, digits):
        unit = 10**(PLACES-digits)
        def write(v):
            a, b = divmod(v, 10**digits)
            return f'{a}.{b:0{digits}d}'
        return '[' + write(self.lo//unit) + ', ' + write(-((-self.hi)//unit)) + ']'


def iv(x):
    if isinstance(x, I):
        return x
    f = F(x)*S
    n, d = f.as_integer_ratio()
    return I(n//d, -((-n)//d))


def pi_interval():
    # Machin's identity, bracket each alternating arctangent series.
    def atan_inv(k):
        terms = [F((-1)**j, (2*j+1)*k**(2*j+1)) for j in range(2*PLACES+2)]
        a, b = iv(sum(terms[:-1])), iv(sum(terms))
        return I(min(a.lo,b.lo), max(a.hi,b.hi))
    return 16*atan_inv(5) - 4*atan_inv(239)


def panel_weights():
    # Integrate the equispaced Lagrange polynomials on one panel.
    m = NODES-1
    result = []
    for i in range(m+1):
        coeff, den = [1], 1
        for j in range(m+1):
            if j != i:
                coeff = [-j*a+b for a,b in zip(coeff+[0],[0]+coeff)]
                den *= i-j
        value = sum(F(a*m**(k+1), k+1) for k,a in enumerate(coeff))
        result.append(value/(den*m*PANEL_DEN))
    assert sum(result) == F(1,PANEL_DEN)
    return result


def xi_coefficients():
    # Xi(t) = 1/2 - (t^2+1/4) integral exp(v/4) psi(exp(v)) cos(tv/2) dv.
    # psi(w)=sum_{n>=1} exp(-pi*n^2*w); v runs from 0 to infinity.
    wt = panel_weights()
    grid_weights = {}
    for panel in range(5*PANEL_DEN):
        for j,w in enumerate(wt):
            i = (NODES-1)*panel + j
            grid_weights[i] = grid_weights.get(i, F(0)) + w
    pi = pi_interval()
    moments = [iv(0) for _ in range(N+1)]
    for i,w in grid_weights.items():
        v = iv(F(i, (NODES-1)*PANEL_DEN))
        base = (-pi*v.exp()).exp()
        psi = sum(base**(n*n) for n in range(1,LAST_N+1))
        value = iv(w)*(v/4).exp()*psi
        factor = (v/2)**2
        for j in range(0,N+1,2):
            moments[j] += value
            value = value*factor/((j+1)*(j+2))
    # Error proof for each cosine coefficient integrand, including 1/j!.
    # On disks of radius 1 centered on [0,5], cos(Im v)>=1/2, Re(v)>=-1,
    # so Re(exp(v))>=1/6. Thus sum exp(-pi*n^2/6)<2, |exp(v/4)|<5,
    # and |(v/2)^j/j!|<=exp(3)<21. The product is <210. By Cauchy,
    # |f^(NODES)|/NODES! < 210. Interpolation on a panel of width 1/32
    # gives integrated quadrature error <=5*210/32^NODES on [0,5].
    # For v in [0,5], ignoring n>LAST_N costs at most
    # 5*4*13*2 exp(-3*(LAST_N+1)^2), by comparison with a geometric sum.
    # For v>=5, the full integrand is <=2 exp(3v/4-3 exp(v))
    # <=exp(-2 exp(v)), whose integral is < exp(-2 exp(5)).
    quad_error = iv(F(5*210, PANEL_DEN**NODES))
    n_tail = 520*iv(-3*(LAST_N+1)**2).exp()
    v_tail = (-2*iv(5).exp()).exp()
    assert quad_error + n_tail + v_tail < ERROR
    err = iv(ERROR)
    signed = [iv(0) for _ in range(N+1)]
    for j in range(0,N+1,2):
        signed[j] = (-1)**(j//2)*(moments[j] + I(-err.hi,err.hi))
    xi = [-signed[j]/4 - (signed[j-2] if j>=2 else 0) for j in range(N+1)]
    xi[0] += F(1,2)
    return xi


def marked_field(xi, x, p):
    # On |t|<=2, psi(exp(v))<=2 exp(-3 exp(v)), |cos(tv/2)|<=exp(v),
    # exp(v)>=1+v gives |Xi(t)|<=1/2+(17/4)*2 exp(-3)/(7/4)<1.
    # Cauchy therefore bounds missing original coefficient k by 2^-k.
    # For |x|<=1/10, the omitted contribution to [s^j]Xi(x+s)
    # is <=sum_{k>N} |x|^(k-j) since binom(k,j)<=2^k.
    assert x.lo >= 0 and x.hi <= S//10 and p <= BASE_ORDER+2
    err = iv(F(2, 10**(N+1-p)))
    jet = []
    for j in range(p+1):
        value = iv(0)
        for k in reversed(range(j,N+1)):
            value = value*x + comb(k,j)*xi[k]
        jet.append(value + I(-err.hi,err.hi))
    # quotient coefficients of Xi'/Xi; q[p-1]=p*[s^p] log Xi(x+s).
    q = []
    for k in range(p):
        q.append(((k+1)*jet[k+1] - sum(jet[j]*q[k-j] for j in range(1,k+1)))/jet[0])
    return endpoint_field(p,x) + q[-1]


def endpoint_field(p,x):
    return 2/(1+x)**p - 1/(1-x)**p


def measure(xi,p):
    lo, hi = F(0), F(1,10)
    if BASE_ORDER > 11:
        # The artificial endpoints alone give an inexpensive initial guess.
        # A Newton step with their slope suggests a much smaller bracket.
        # Only the verified opposite signs of the FULL fields accept it.
        for _ in range(360):
            mid = (lo+hi)/2
            sign = endpoint_field(p,iv(mid))
            if sign.lo > 0:
                lo = mid
            elif sign.hi < 0:
                hi = mid
            else:
                break
        near = iv((lo+hi)/2)
        slope = -p*(2/(1+near)**(p+1) + 1/(1-near)**(p+1))
        proposal = near-marked_field(xi,near,p)/slope
        center = F(proposal.lo+proposal.hi,2*S)
        lo, hi = center - F(1,10**100), center + F(1,10**100)
    assert iv(0)<marked_field(xi,iv(lo),p) and marked_field(xi,iv(hi),p)<0
    for _ in range(BISECTIONS if BASE_ORDER<=11 else 0):
        mid = (lo+hi)/2
        sign = marked_field(xi,iv(mid),p)
        if sign.lo>0:
            lo=mid
        elif sign.hi<0:
            hi=mid
        else:
            break
    x = I(iv(lo).lo,iv(hi).hi)
    assert x.hi-x.lo < S//10**(21 if p<=11 else 92)
    return x, endpoint_field(p,x)/(2*p*x)


def atom(p,r,x):
    r = iv(r)
    return ((r-x)**(-p) - (r+x)**(-p))/(2*p*x)


def main():
    if not __debug__:
        raise RuntimeError("Run without -O so all certificate checks are active.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--high', action='store_true', help='use orders 65 and 67')
    args = parser.parse_args()
    if args.high:
        high_order_settings()
    p = BASE_ORDER
    xi = xi_coefficients()
    x, first = measure(xi,p)
    y, second = measure(xi,p+2)
    low, high, mass_cap = ('14.10','14.23','1.10') if not args.high else (
        '14.1347251417337','14.1347251417510','1.000000000082')
    assert first < atom(p,F(low),x)
    assert atom(p+2,F(high),y)/atom(p,F(high),x) < second/first
    mass_bound = first/atom(p,F(high),x)
    assert mass_bound < F(mass_cap)
    print(f'x_{p} in', x.display(42 if args.high else 24))
    print(f'x_{p+2} in', y.display(42 if args.high else 24))
    print(f'D_{p} in', first.display(100 if args.high else 26))
    print(f'D_{p+2} in', second.display(102 if args.high else 27))
    print(f'D_{p}/A_{p}({high},x_{p}) in', mass_bound.display(15 if args.high else 8))
    print(f'The two-order enclosure gives {low} < gamma_1 < {high} and multiplicity 1.')


if __name__ == '__main__':
    main()
