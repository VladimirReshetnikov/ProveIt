#!/usr/bin/env python3
"""Exact fixed-order saddle coefficients for A118096 (Python standard library).

All arithmetic is in Q(sqrt(5)); no numerical fitting or floating-point input.
The expansion variable is s=sqrt(t). Every product is truncated by its entire
s-degree, not by the Gaussian variable's degree. See README.md for formulas.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import factorial
import argparse
import json


def natural(value, name='order'):
    if type(value) is not int:
        raise TypeError(name + ' must be an integer, not a boolean or float')
    if value < 0:
        raise ValueError(name + ' must be nonnegative')
    return value


def rational(value):
    if type(value) is int or isinstance(value, Fraction):
        return Fraction(value)
    raise TypeError('exact coefficients accept only int or Fraction')


@dataclass(frozen=True)
class Q5:
    """a+b*sqrt(5), with canonical Fraction coordinates."""
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self):
        object.__setattr__(self, 'a', rational(self.a))
        object.__setattr__(self, 'b', rational(self.b))

    @staticmethod
    def of(value):
        return value if isinstance(value, Q5) else Q5(value)

    def __add__(self, other):
        v = self.of(other)
        return Q5(self.a + v.a, self.b + v.b)

    __radd__ = __add__

    def __neg__(self):
        return Q5(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.of(other)

    def __rsub__(self, other):
        return self.of(other) + -self

    def __mul__(self, other):
        v = self.of(other)
        return Q5(self.a*v.a + 5*self.b*v.b, self.a*v.b + self.b*v.a)

    __rmul__ = __mul__

    def inverse(self):
        norm = self.a*self.a - 5*self.b*self.b
        if not norm:
            raise ZeroDivisionError('zero in Q(sqrt(5))')
        return Q5(self.a/norm, -self.b/norm)

    def __truediv__(self, other):
        return self * self.of(other).inverse()

    def __rtruediv__(self, other):
        return self.of(other) * self.inverse()

    def __pow__(self, power):
        if type(power) is not int:
            raise TypeError('field exponent must be an integer')
        if power < 0:
            return self.inverse() ** (-power)
        out, base = Q5(1), self
        while power:
            if power & 1:
                out = out * base
            base = base * base
            power //= 2
        return out

    def __bool__(self):
        return bool(self.a or self.b)

    def record(self):
        return {'rational': str(self.a), 'sqrt5': str(self.b)}


ZERO, ONE = Q5(), Q5(1)
PHI = Q5(Fraction(1, 2), Fraction(1, 2))
RHO = PHI - 1
CURVATURE = 3*PHI - 4


def bernoulli_through(n):
    """B_1=-1/2 convention, via its defining triangular recurrence."""
    natural(n)
    out = [Fraction(1)]
    for m in range(1, n + 1):
        total, choose = Fraction(0), 1
        for k in range(m):
            total += choose * out[k]
            choose = choose * (m + 1 - k) // (k + 1)
        out.append(-total / (m + 1))
    return out


def multiply_series(left, right, degree):
    natural(degree, 'degree')
    out = [ZERO] * (degree + 1)
    for i, a in enumerate(left[:degree + 1]):
        for j, b in enumerate(right[:degree + 1 - i]):
            out[i + j] += a*b
    return out


def inverse_series(series, degree):
    natural(degree, 'degree')
    if not series:
        raise ValueError('cannot invert an empty series')
    first = Q5.of(series[0])
    if not first:
        raise ZeroDivisionError('series constant term must be nonzero')
    out = [first.inverse()]
    for n in range(1, degree + 1):
        out.append(-sum((series[k]*out[n-k] for k in range(1, min(n + 1, len(series)))), ZERO)/first)
    return out


def f_derivatives(rho, degree):
    """f^(m)(x), m=1..degree, from f'(x)=-z/(1-z), z=rho*exp(-u)."""
    natural(degree, 'degree')
    rho = Q5.of(rho)
    if degree == 0:
        return [ZERO]
    z = [rho * Fraction((-1)**k, factorial(k)) for k in range(degree)]
    denominator = [-v for v in z]
    denominator[0] += 1
    quotient = multiply_series(z, inverse_series(denominator, degree-1), degree-1)
    return [ZERO] + [-quotient[m-1]*factorial(m-1) for m in range(1, degree+1)]


def polynomial_add(left, right):
    out = dict(left)
    for k, v in right.items():
        out[k] = out.get(k, ZERO) + v
        if not out[k]:
            del out[k]
    return out


def polynomial_scale(poly, scalar):
    return {k: v*scalar for k, v in poly.items() if v*scalar}


def polynomial_multiply(left, right):
    out = {}
    for i, a in left.items():
        for j, b in right.items():
            out[i+j] = out.get(i+j, ZERO) + a*b
    return {k: v for k, v in out.items() if v}


def exponent_terms(order):
    """E[d][m] is the coefficient of s^d Y^m in the finite exponent."""
    natural(order)
    degree = 2*order
    fd1 = f_derivatives(RHO, degree+1)
    fd2 = f_derivatives(RHO**2, degree+1)
    bern = bernoulli_through(order+2)
    out = [{} for _ in range(degree+1)]
    def put(d, m, value):
        if d < 1 or d > degree:
            raise ValueError('internal whole-degree truncation violation')
        out[d] = polynomial_add(out[d], {m: value})
    for m in range(3, degree+3):
        put(m-2, m, (2**m*fd2[m-1]-fd1[m-1])/factorial(m))
    for m in range(1, degree+1):
        ell = (fd1[m]+2**m*fd2[m])/2 - (3 if m == 1 else 0)
        put(m, m, ell/factorial(m))
    for r in range(1, (degree+2)//4+1):
        shift = 4*r-2
        for m in range(degree-shift+1):
            value = bern[2*r] * (2**m*fd2[2*r-1+m]-fd1[2*r-1+m])
            put(shift+m, m, value / (factorial(2*r)*factorial(m)))
    return out


def gaussian_moment(power):
    natural(power, 'Gaussian power')
    if power % 2:
        return ZERO
    out = ONE
    for k in range(1, power, 2):
        out *= k/CURVATURE
    return out


def radial_coefficients(order):
    """Return [c_0,...,c_order] using n B_n=sum k E_k B_(n-k)."""
    natural(order)
    exponent = exponent_terms(order)
    expansion = [{0: ONE}]
    for n in range(1, 2*order+1):
        term = {}
        for k in range(1, n+1):
            term = polynomial_add(term, polynomial_scale(
                polynomial_multiply(exponent[k], expansion[n-k]), k))
        expansion.append(polynomial_scale(term, Fraction(1, n)))
    return [sum((v*gaussian_moment(m) for m, v in expansion[2*j].items()), ZERO)
            for j in range(order+1)]


def coefficient_transfer(radial):
    """Return d_r as polynomials in U=sqrt(A), A=pi^2/30.

    A polynomial is a dictionary {nonnegative U exponent: Q5 coefficient}.
    """
    if not radial:
        raise ValueError('radial coefficient list must include c_0')
    if Q5.of(radial[0]) != ONE:
        raise ValueError('radial constant coefficient must be one')
    result = []
    for r in range(len(radial)):
        term = {}
        for j in range((r+1)//2, r+1):
            scale = Fraction((-1)**(r-j)*factorial(r),
                             factorial(r-j)*factorial(2*j-r)*4**(r-j))
            term[2*j-r] = Q5.of(radial[j])*scale
        result.append(term)
    return result


def partition_counts(max_n):
    """Exact [q^n] sum_{k>=1} q^(3k)/prod_{j=k}^{2k}(1-q^j).

    P_(k+1)=P_k(1-q^k)/((1-q^(2k+1))(1-q^(2k+2))).
    Each operation is integer, truncated to the remaining required degree.
    Time O(max_n^2); memory O(max_n). a(0)=a(1)=a(2)=0.
    """
    natural(max_n, 'max_n')
    counts = [0]*(max_n+1)
    if max_n < 3:
        return counts
    product = [j//2+1 for j in range(max_n-2)]
    for k in range(1, max_n//3+1):
        limit = max_n-3*k
        for j in range(limit+1):
            counts[j+3*k] += product[j]
        next_limit = limit-3
        if next_limit < 0:
            break
        del product[next_limit+1:]
        for j in range(next_limit, k-1, -1):
            product[j] -= product[j-k]
        for part in (2*k+1, 2*k+2):
            for j in range(part, next_limit+1):
                product[j] += product[j-part]
    return counts


def nonnegative_cli(text):
    try:
        value = int(text)
    except ValueError as error:
        raise argparse.ArgumentTypeError('expected a nonnegative integer') from error
    if value < 0:
        raise argparse.ArgumentTypeError('expected a nonnegative integer')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=nonnegative_cli, default=4)
    parser.add_argument('--counts', type=nonnegative_cli, help='also generate a(0)..a(N)')
    args = parser.parse_args()
    cs = radial_coefficients(args.order)
    out = {'field': 'Q(sqrt(5))', 'order': args.order,
           'radial': [c.record() for c in cs],
           'coefficient_polynomials_in_sqrt_A': [
               {str(k): v.record() for k, v in sorted(p.items())}
               for p in coefficient_transfer(cs)]}
    if args.counts is not None:
        out['counts'] = partition_counts(args.counts)
    print(json.dumps(out, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
