"""Finite coefficient checks for the resonant Gauss equation. Python 3 only."""
from dataclasses import dataclass
from fractions import Fraction
from math import factorial


@dataclass(frozen=True)
class Gaussian:
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    @staticmethod
    def cast(x):
        return x if isinstance(x, Gaussian) else Gaussian(Fraction(x))

    def __add__(self, x):
        z = self.cast(x)
        return Gaussian(self.re + z.re, self.im + z.im)

    __radd__ = __add__

    def __neg__(self):
        return Gaussian(-self.re, -self.im)

    def __sub__(self, x):
        return self + -self.cast(x)

    def __rsub__(self, x):
        return self.cast(x) + -self

    def __mul__(self, x):
        z = self.cast(x)
        return Gaussian(self.re*z.re - self.im*z.im, self.re*z.im + self.im*z.re)

    __rmul__ = __mul__

    def __truediv__(self, integer):
        assert isinstance(integer, int) and integer
        return Gaussian(self.re/Fraction(integer), self.im/Fraction(integer))

    def norm(self):
        return abs(self.re) + abs(self.im)


ONE, ZERO = Gaussian.cast(1), Gaussian.cast(0)


def convolution_at(left, right, n):
    return sum((left[j]*right[n-j] for j in range(n+1)), ZERO)


def rising(x, m):
    product = ONE
    for j in range(m):
        product = product * (x+j)
    return product


def check(a, b, m, extra=7):
    a, b = Gaussian.cast(a), Gaussian.cast(b)
    q = m-a-b
    nmax = m+extra
    u, g, w, w2, h = [ONE], [ONE], [ONE], [ONE], [ONE]
    D = max(1, max(1, a.norm())*max(1, b.norm()), q.norm())
    K = 6*D
    for n in range(nmax):
        u.append(u[-1]*(n+a)*(n+b) / ((n+1)*(n+m+1)))
        g.append(g[-1]*(n-q) / (n+1))
        w.append(-sum((u[j]*w[n+1-j] for j in range(1,n+2)), ZERO))
        w2.append(convolution_at(w, w, n+1))
        h.append(convolution_at(g, w2, n+1))
        assert convolution_at(u, w, n+1) == ZERO
        assert u[-1].norm() <= D**(n+1) and g[-1].norm() <= D**(n+1)
        assert w[-1].norm() <= (2*D)**(n+1) and h[-1].norm() <= K**(n+1)
    expected = (-1)**m*rising(a-m,m)*rising(b-m,m) / (factorial(m)**2)
    assert h[m] == expected
    assert (h[m] == ZERO) == (a in [Gaussian.cast(i) for i in range(1,m+1)] or
                              b in [Gaussian.cast(i) for i in range(1,m+1)])
    d = []
    for j in range(nmax+1):
        d.append(sum((u[i]*h[j-i]/(j-i-m) for i in range(j+1) if j-i!=m), ZERO))
        k = j-m
        lhs = k*j*d[j]
        if j:
            lhs = lhs-(k-1+a)*(k-1+b)*d[j-1]
        if k >= 0:
            lhs = lhs+h[m]*(2*k+m)*u[k]
        if k > 0:
            lhs = lhs-h[m]*(2*(k-1)+a+b)*u[k-1]
        assert lhs == ZERO, (m, j, lhs)
    return h[m]


if __name__ == '__main__':
    params = [0, 1, 2, -2, Fraction(1,2), Fraction(-3,2),
              Gaussian(Fraction(1),Fraction(1,2))]
    total = 0
    for m in range(8):
        for a in params:
            for b in params:
                check(a,b,m)
                total += 1
    assert check(Fraction(1,2), Fraction(1,2), 2) == Gaussian.cast(Fraction(9,64))
    print(f'{total} Gaussian-rational parameter triples passed all coefficient checks.')
    print('For a=b=1/2 and m=2, the log coefficient is 9/64.')
