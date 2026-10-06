#!/usr/bin/env python3
"""Standard-library exact Laurent-polynomial and integer calculations.

Ring variables are (b,v,j,y). Only b may have negative powers. During the
Riccati derivation the first two slots temporarily mean (x,a). y represents
it, so Gaussian integration sends y^(2m) to (-1)^m (2m-1)!! b^(-m).
No floating-point arithmetic, eval(), CAS, or removable assertions are used.
"""
from fractions import Fraction as F
from math import comb, factorial


def need(ok, message):
    if not ok:
        raise ValueError(message)


class P:
    def __init__(self, value=0):
        self.d = ({k: F(v) for k, v in value.items() if v} if isinstance(value, dict)
                  else ({(0, 0, 0, 0): F(value)} if value else {}))

    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        d = dict(self.d)
        for key, val in other.d.items():
            d[key] = d.get(key, F(0)) + val
        return P(d)
    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.d.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, P) else -F(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        d = {}
        for k, a in self.d.items():
            for h, c in other.d.items():
                key = tuple(x + y for x, y in zip(k, h))
                d[key] = d.get(key, F(0)) + a * c
        return P(d)
    __rmul__ = __mul__

    def __pow__(self, n):
        need(type(n) is int, 'integer exponent required')
        if n < 0:
            need(len(self.d) == 1, 'negative power requires monomial')
            (k, c), = self.d.items()
            need(not any(k[1:]), 'only b can be inverted')
            return P({tuple(n * h for h in k): c ** n})
        value, base = P(1), self
        while n:
            if n % 2:
                value = value * base
            base = base * base
            n //= 2
        return value

    def __truediv__(self, other):
        other = other if isinstance(other, P) else P(other)
        return self * other ** -1

    def __eq__(self, other):
        return self.d == (other.d if isinstance(other, P) else P(other).d)

    def diff(self, index):
        d = {}
        for key, value in self.d.items():
            if key[index]:
                power = list(key)
                power[index] -= 1
                d[tuple(power)] = value * key[index]
        return P(d)

    def substitute(self, index, replacement):
        value = P(0)
        for key, coefficient in self.d.items():
            powers = list(key)
            exponent, powers[index] = powers[index], 0
            value += P({tuple(powers): coefficient}) * replacement ** exponent
        return value

    def serial(self):
        return [{'powers': list(k), 'coefficient': str(v)} for k, v in sorted(self.d.items())]


B = P({(1, 0, 0, 0): 1})
V = P({(0, 1, 0, 0): 1})
J = P({(0, 0, 1, 0): 1})
Y = P({(0, 0, 0, 1): 1})


def stirling2(n, k):
    row = [1]
    for i in range(n):
        row = [0] + [row[h - 1] + h * (row[h] if h < len(row) else 0)
                     for h in range(1, i + 2)]
    return row[k] if k < len(row) else 0


def bernoulli(n):
    out = [F(1)]
    for m in range(1, n + 1):
        out.append(-sum(F(comb(m + 1, k)) * out[k] for k in range(m)) / (m + 1))
    return out


def stirling_coefficients(order):
    """Exponentiate the Bernoulli logarithmic Stirling series, any fixed order."""
    numbers = bernoulli(order + 1)
    log = [F(0)] * (order + 1)
    for k in range(1, order + 1, 2):
        log[k] = numbers[k + 1] / (k * (k + 1))
    s = [F(1)]
    for k in range(1, order + 1):
        s.append(sum(h * log[h] * s[k - h] for h in range(1, k + 1)) / k)
    return s


def cumulants_riccati(order):
    """Repeated 2x*d/dx+(4x-a^2)*d/da, then a=1, x=(b+1)/4."""
    poly = V
    out = [P(0)]
    for h in range(1, order + 1):
        out.append(poly.substitute(1, P(1)).substitute(0, (B + 1) / 4))
        poly = 2 * B * poly.diff(0) + (4 * B - V ** 2) * poly.diff(1)
    return out


def cumulants_raw_ode(order):
    """Independent differentiated Bessel ODE, raw moments, cumulant recurrence."""
    x = (B + 1) / 4
    g = [P(1), P(1)]
    for m in range(order - 1):
        value = -(2*m + 1)*g[m+1] - (m*m - 4*x)*g[m]
        if m:
            value += 8*m*x*g[m-1]
        if m >= 2:
            value += 4*m*(m-1)*x*g[m-2]
        g.append(value)
    moments, cumulants = [P(1)], [P(0)]
    for k in range(1, order + 1):
        moments.append(sum(stirling2(k, h)*g[h] for h in range(1, k + 1)))
        cumulants.append(moments[k] - sum(comb(k-1, h-1)*cumulants[h]*moments[k-h]
                                         for h in range(1, k)))
    return cumulants


def amplitude_moments(order):
    x = (B + 1)/4
    return [sum(stirling2(k, h) * x**(h//2) * (V if h % 2 else P(1))
                for h in range(k+1)) for k in range(order+1)]


def weighted_partitions(total, h=3):
    if total == 0:
        yield {}
        return
    if h > total + 2:
        return
    for m in range(total//(h-2) + 1):
        for tail in weighted_partitions(total-m*(h-2), h+1):
            yield ({h: m, **tail} if m else tail)


def double_factorial(n):
    result = 1
    while n > 0:
        result *= n
        n -= 2
    return result


def gaussian(poly):
    result = P(0)
    for key, c in poly.d.items():
        power = key[3]
        if power % 2:
            continue
        k = list(key)
        k[0] -= power//2
        k[3] = 0
        result += P({tuple(k): c * (-1)**(power//2) * double_factorial(power-1)})
    return result


def parity_mean(poly, moments):
    result = P(0)
    for key, c in poly.d.items():
        k = list(key)
        degree, k[2] = k[2], 0
        result += P({tuple(k): c}) * moments[degree]
    return result


def corrections_partition(order, cumulants):
    mu, saddle = amplitude_moments(2*order), []
    for ell in range(order+1):
        value = P(0)
        for j in range(2*ell+1):
            for counts in weighted_partitions(2*ell-j):
                degree = j + sum(h*m for h,m in counts.items())
                term = mu[j] * F((-1)**(degree//2)*double_factorial(degree-1), factorial(j)) * B**(-degree//2)
                for h, m in counts.items():
                    term *= cumulants[h]**m / (factorial(m)*factorial(h)**m)
                value += term
        saddle.append(value)
    st = stirling_coefficients(order)
    return [sum(st[j]*saddle[k-j] for j in range(k+1)) for k in range(order+1)]


def corrections_exponential(order, cumulants):
    """Independent formal exponential recurrence with z^j insertion."""
    e = [P(0)] + [cumulants[k+2]*Y**(k+2)/factorial(k+2)
                   for k in range(1, 2*order+1)]
    if order:
        e[1] += J*Y
    p = [P(1)]
    for k in range(1, 2*order+1):
        p.append(sum(h*e[h]*p[k-h] for h in range(1,k+1))/k)
    need(all(gaussian(p[k]) == 0 for k in range(1,2*order+1,2)), 'odd Gaussian terms')
    st = stirling_coefficients(order)
    inserted = [sum(st[h]*gaussian(p[2*(k-h)]) for h in range(k+1)) for k in range(order+1)]
    moments = amplitude_moments(2*order)
    ordinary = [parity_mean(poly, moments) for poly in inserted]
    q = [P(1)]
    for k in range(1,order+1):
        q.append(inserted[k] - sum(ordinary[h]*q[k-h] for h in range(1,k+1)))
        need(parity_mean(q[k], moments) == 0, 'probability correction is not centered')
    return ordinary, q


def integer_rows(max_n):
    """(k!)^2[t^k](sum t^j/(j!)^2)^d, computed by binomial convolution."""
    kmax = max_n//2
    choose = [[comb(k,j)**2 for j in range(k+1)] for k in range(kmax+1)]
    rows = [[1]+[0]*kmax]
    for dim in range(1,max_n+1):
        prev = rows[-1]
        rows.append([sum(choose[k][j]*prev[k-j] for j in range(k+1)) for k in range(kmax+1)])
    return rows


def zero_counts(n, row):
    return {n-2*k: comb(n,2*k)*comb(2*k,k)*row[k] for k in range(n//2+1)}


def count_riccati(n):
    """Independent coefficient recurrence from D a=4z^2-a^2 and D F^n=n a F^n."""
    a, c = [F(0)], [F(1)]
    for k in range(1,n//2+1):
        a.append((F(4 if k==1 else 0)-sum(a[h]*a[k-h] for h in range(1,k)))/(2*k))
        c.append(F(n,2*k)*sum(a[h]*c[k-h] for h in range(1,k+1)))
    total = factorial(n)*sum(c[k]/factorial(n-2*k) for k in range(n//2+1))
    need(total.denominator == 1, 'nonintegral Riccati count')
    return total.numerator


def positive_rows(max_pairs):
    rows = [[1]+[0]*max_pairs]
    for axes in range(1,max_pairs+1):
        prev = rows[-1]
        rows.append([sum(comb(k,h)**2*prev[k-h] for h in range(1,k+1)) for k in range(max_pairs+1)])
    return rows


def joint_counts(n, positive):
    out = []
    for pairs in range(n//2+1):
        zeros = n-2*pairs
        multiplier = comb(n,zeros)*comb(2*pairs,pairs)
        for axes in range(pairs+1):
            count = multiplier*comb(n,axes)*positive[axes][pairs]
            if count:
                out.append((zeros,axes,count))
    return out
