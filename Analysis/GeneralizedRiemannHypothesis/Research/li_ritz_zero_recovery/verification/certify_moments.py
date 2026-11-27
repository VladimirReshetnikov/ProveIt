"""Certified scaled reciprocal-zero moments from Taylor coefficients of xi.

Only the Python standard library is used. Run in any directory; the JSON
result is written alongside this script. Decimal arithmetic uses directed
rounding, except ln, which Decimal computes correctly rounded to nearest;
we bracket that value by its immediately adjacent representable numbers.
"""
from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json

DEGREE = 17
SCALE = 200
PRECISION = 190
CUTOFF = 256
ORDER = 96
DOWN = Context(prec=PRECISION, rounding=ROUND_FLOOR)
UP = Context(prec=PRECISION, rounding=ROUND_CEILING)
NEAR = Context(prec=PRECISION, rounding=ROUND_HALF_EVEN)


@dataclass(frozen=True)
class Ball:
    lo: Decimal
    hi: Decimal

    def __add__(self, other):
        b = interval(other)
        return Ball(DOWN.add(self.lo, b.lo), UP.add(self.hi, b.hi))

    __radd__ = __add__

    def __neg__(self):
        return Ball(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-interval(other))

    def __mul__(self, other):
        b = interval(other)
        pairs = [(x, y) for x in (self.lo, self.hi) for y in (b.lo, b.hi)]
        return Ball(min(DOWN.multiply(x,y) for x,y in pairs),
                    max(UP.multiply(x,y) for x,y in pairs))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = interval(other)
        assert b.lo > 0
        one = Decimal(1)
        return self * Ball(DOWN.divide(one, b.hi), UP.divide(one, b.lo))

    def log(self):
        assert self.lo > 0
        return Ball(DOWN.next_minus(NEAR.ln(self.lo)),
                    UP.next_plus(NEAR.ln(self.hi)))


def interval(x):
    if isinstance(x, Ball):
        return x
    if isinstance(x, Fraction):
        a, b = Decimal(x.numerator), Decimal(x.denominator)
        return Ball(DOWN.divide(a, b), UP.divide(a, b))
    d = Decimal(x)
    return Ball(d, d)


def symmetric_error(e):
    return Ball(interval(e).hi.copy_negate(), interval(e).hi)


def pi_interval():
    def atan_inverse(q):
        # Alternating power series, with exact rational bounds.
        v = Fraction(0)
        j = 0
        while True:
            term = Fraction((-1)**j, (2*j+1)*q**(2*j+1))
            if abs(term) < Fraction(1,10**(PRECISION+5)):
                return Ball(interval(min(v,v+term)).lo, interval(max(v,v+term)).hi)
            v += term
            j += 1
    return 16*atan_inverse(5)-4*atan_inverse(239)


def bernoulli_table(n):
    numbers = [Fraction(1)]
    for j in range(1, n+1):
        numbers.append(-sum(comb(j+1,k)*b for k,b in enumerate(numbers))/(j+1))
    return numbers


def exp_minus_log(n, degree):
    L = -interval(n).log()
    coeffs = [interval(1)]
    for j in range(1, degree+1):
        coeffs.append(coeffs[-1]*L/j)
    return coeffs


def zeta_regularized(B, d, n, p):
    # Taylor of Z(u) = u*zeta(1+u). The tail of the Dirichlet series,
    # starting at n, is integrated by Euler--Maclaurin through B_(2p).
    one, zero = interval(1), interval(0)
    co = [zero]*(d+1)
    for a in range(1,n):
        for k,c in enumerate(exp_minus_log(a,d-1)):
            co[k+1] += c/a
    # The tail is exp(-u log n) times 1 + u/(2n) +
    # u sum_{j=1}^p (B_(2j)/(2j)!) (1+u)_(2j-1) n^(-2j).
    tail = [one, one/(2*n)] + [zero]*(d-1)
    rising = [1]+[0]*(d-1)
    for step in range(1,2*p):
        rising = [step*c + (rising[k-1] if k else 0) for k,c in enumerate(rising)]
        if step%2:
            r = step+1
            factor = B[r]/(factorial(r)*n**r)
            for k,c in enumerate(rising):
                tail[k+1] += interval(c*factor)
    ex = exp_minus_log(n,d)
    for k in range(d+1):
        co[k] += sum(ex[j]*tail[k-j] for j in range(k+1))
    # On |u|=1/2 the periodic Bernoulli remainder for Z has modulus
    # <=4*(2p+1)!*n/(6n)^(2p). Indeed |(1+u)_(2p)| <=(2p+1)!,
    # int_n^infty t^(-1-Re u-2p)dt <= n^(1-2p), and 2*pi>6.
    E = Fraction(4*factorial(2*p+1)*n,(6*n)**(2*p))
    for k in range(1,d+1):
        co[k] += symmetric_error(2**k*E)   # Cauchy's coefficient estimate
    co[0] = one  # the pole residue
    return co


def zeta_integer(j,B,n,p):
    # Exact rational Euler--Maclaurin sum for zeta(j), j>=2.
    value = sum(Fraction(1,a**j) for a in range(1,n))
    value += Fraction(1,(j-1)*n**(j-1)) + Fraction(1,2*n**j)
    for r in range(2,2*p+1,2):
        value += B[r]*Fraction(comb(j+r-2,r-1),r*n**(j+r-1))
    E = Fraction(4*factorial(j+2*p-1),
                 factorial(j-1)*6**(2*p)*(j+2*p-1)*n**(j+2*p-1))
    return interval(value) + symmetric_error(E)


def scaled_moments():
    d,n,p = DEGREE,CUTOFF,ORDER
    B = bernoulli_table(2*p)
    Z = zeta_regularized(B,d,n,p)
    # From Z'=Z (log Z)' compute the formal logarithm.
    values = [interval(0)]*(d+1)
    for k in range(1,d+1):
        cross_terms = sum((j*values[j]*Z[k-j] for j in range(1,k)), interval(0))
        values[k] = Z[k] - cross_terms/k
    # log(2 xi(1+u)) = log(1+u) + log Z(u) - (u/2)log pi
    #                  + log Gamma((1+u)/2) - log Gamma(1/2).
    # Z[1]=Euler's constant. The higher log-Gamma coefficients use the
    # Hurwitz-zeta sum over positive half-integers.
    values[1] += interval(1) - (Z[1]+2*interval(2).log()+pi_interval().log())/2
    for k in range(2,d+1):
        z = zeta_integer(k,B,n,p)
        values[k] += interval(Fraction((-1)**(k+1),k))
        values[k] += ((-1)**k)*z*Fraction(2**k-1, k*2**k)
    # Write log(2 xi(1+u))=sum c_k * (u+u^2)^k. Then
    # c_k=(-1)^(k-1) p_k/k, p_k=sum multiplicity*x^k for x=1/(rho(1-rho)).
    moments = []
    for k in range(1,d+1):
        for j in range((k+1)//2,k):
            values[k] -= comb(j,k-j)*values[j]
        s = (-1)**(k-1)*k*SCALE**k*values[k]
        assert DOWN.subtract(s.hi,s.lo) < Decimal('1e-100') and s.lo > 0
        moments.append(dict(k=k,lower=str(s.lo),upper=str(s.hi)))
    return dict(scale=SCALE,moments=moments)


if __name__ == '__main__':
    data = scaled_moments()
    out = Path(__file__).with_name('certified_moments.json')
    out.write_text(json.dumps(data,indent=2)+'\n')
    for m in data['moments']:
        width = UP.subtract(Decimal(m['upper']), Decimal(m['lower']))
        print(f"k={m['k']:2d}   lower endpoint starts {m['lower'][:22]}   width < 1e{width.adjusted()+1}")
