"""A rational certificate for different cubic and quartic outcomes at shift zero."""
from dataclasses import dataclass
from fractions import Fraction as F
from math import comb, factorial, prod


@dataclass(frozen=True)
class Interval:
    lo: F
    hi: F

    def __post_init__(self):
        assert self.lo <= self.hi

    def __add__(self, other):
        other = box(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-box(other))

    def __mul__(self, other):
        other = box(other)
        ends = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(ends), max(ends))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.hi < 0 or self.lo > 0
        return Interval(1/self.hi, 1/self.lo)


def box(x):
    return x if isinstance(x, Interval) else Interval(F(x), F(x))


t = F(1, 10000)
c = F(4, 5)


def moment(n):
    p = F(2*n+1, 2)
    rising = [prod(p+i for i in range(j)) for j in range(31)]
    # E[V^j], V = t² X² + c t³ X³ for a Gamma(p,1) variable X.
    def expected_power(j):
        return sum(comb(j,k)*c**k*t**(2*j+k)*rising[2*j+k] for k in range(j+1))
    lower = sum((-1)**j*expected_power(j)/F(factorial(j)) for j in range(10))
    upper = lower + expected_power(10)/factorial(10)
    return Interval(lower, upper)


def centered_coefficients(d):
    # Coefficients of t^(-d) J(-1+t y) in ascending order.
    return [
        sum(comb(d,k)*comb(k,j)*(-1)**(k-j)*t**(j-d)*moment(k)
            for k in range(j,d+1))
        for j in range(d+1)
    ]


def evaluate(coeffs, y):
    out = box(0)
    for a in reversed(coeffs):
        out = out*y + a
    return out


def check():
    coeffs = centered_coefficients(3)
    for y, sign in [(-4,-1), (0,1), (F(7,5),-1), (3,1)]:
        value = evaluate(coeffs,y)*sign
        assert value.lo > 0
    print('Cubic signs at -4, 0, 7/5, 3: -, +, -, +.')

    coeffs = centered_coefficients(4)
    monic = [a*coeffs[-1].reciprocal() for a in reversed(coeffs)]
    sums = [box(4)]
    for k in range(1,5):
        # Newton sums for the roots of the monic quartic.
        sums.append(-sum((monic[i]*sums[k-i] for i in range(1,k)), box(0)) - k*monic[k])
    d, a, b, v, w = sums
    determinant = d*(b*w-v*v) - a*(a*w-v*b) + b*(a*v-b*b)
    assert -11000 < determinant.lo <= determinant.hi < -1000
    print('Quartic root-moment 3x3 determinant is strictly between -11000 and -1000.')
    print('The shift-zero cubic has three distinct real roots. The quartic has a nonreal pair.')


if __name__ == '__main__':
    check()
