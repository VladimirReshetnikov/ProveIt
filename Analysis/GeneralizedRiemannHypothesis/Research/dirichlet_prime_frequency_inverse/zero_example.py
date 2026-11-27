"""Reproduce Gaussian prime-frequency sums over the zeros of xi and xi'.

Run: python zero_example.py
Requires Python 3, NumPy, SciPy and mpmath. Typical runtime: one minute.
The calculation is a floating-point illustration. Proofs are in the paper.
"""
from math import ceil, factorial, log, pi, sqrt
import mpmath as mp
import numpy as np
from scipy.optimize import brentq
from scipy.special import bernoulli, digamma, loggamma

M = 16
BERNOULLI = bernoulli(2 * M)
COEFF = [BERNOULLI[2*k] / factorial(2*k) for k in range(1, M+1)]


class CriticalLine:
    """Evaluate real multiples of xi and its ordinate derivative on a window."""

    def __init__(self, upper):
        self.n = int(ceil(upper / 2)) + 32
        ns = np.arange(1, self.n, dtype=np.float64)
        self.logs = np.log(ns)
        self.weights = ns ** (-0.5)
        self.logn = log(self.n)

    def values(self, t):
        s = 0.5 + 1j * t
        series = self.weights * np.exp(-1j * t * self.logs)
        # Euler--Maclaurin, truncating the Dirichlet sum at n-1.
        scale = np.exp(-s * self.logn)
        tail = self.n / (s-1) + 0.5
        tail_d = -self.n / (s-1)**2
        rising, rising_d = 1.0, 0.0
        for j in range(2*M-1):
            factor = (s+j) / self.n
            rising, rising_d = rising * factor, rising_d * factor + rising/self.n
            if j % 2 == 0:
                coefficient = COEFF[j//2]
                tail += coefficient * rising
                tail_d += coefficient * rising_d
        zeta = np.sum(series) + scale * tail
        zeta_d = -np.dot(series, self.logs) + scale * (tail_d-self.logn*tail)
        theta = loggamma(s/2).imag - 0.5*t*log(pi)
        phase = np.exp(1j * theta)
        g = 1/s + 1/(s-1) + (digamma(s/2)-log(pi))/2
        # s(s-1) < 0 on this line. The same arbitrary sign is omitted in both.
        return ((phase*zeta).real, (1j*phase*(zeta_d+g*zeta)).real)


def ordinates(center, width):
    # Extra outside zeros bracket the end gaps, then trim to the actual window.
    left, right = center - 8*width, center + 8*width
    a, b = left-10, right+10
    cf = CriticalLine(b)
    count = int(mp.nzeros(b)-mp.nzeros(a))
    step = 0.2
    for _ in range(6):
        grid = np.linspace(a, b, ceil((b-a)/step)+1)
        value = np.array([cf.values(x)[0] for x in grid])
        flips = np.flatnonzero(np.signbit(value[:-1]) != np.signbit(value[1:]))
        if len(flips) == count:
            break
        step /= 2
    else:
        raise ArithmeticError("Failed to match the independent zeta zero count")
    plain = np.array([brentq(lambda t: cf.values(t)[0],grid[i],grid[i+1],
                             xtol=2e-11) for i in flips])
    if plain[0] >= left or plain[-1] <= right:
        raise ArithmeticError("Enlarge padding for the derivative zeros")
    # One xi' zero per gap, by the interlacing theorem in the paper.
    deriv = np.array([brentq(lambda t: cf.values(t)[1],p,q,xtol=2e-11)
                      for p,q in zip(plain[:-1],plain[1:])])
    return [x[(left <= x) & (x <= right)] for x in (plain,deriv)]


def window_sum(zeros, t, h, p):
    weight = np.exp(-0.5*((zeros-t)/h)**2)
    total = np.dot(weight,np.exp(1j*zeros*log(p)))
    return 2*pi*sqrt(p)*total/(sqrt(2*pi)*h)


def fmt(x):
    return f"{x.real:+.6f} {x.imag:+.6f}i"


if __name__ == '__main__':
    for t,h in [(1500,45), (6000,90)]:
        z, dz = ordinates(t,h)
        print(f"T={t}, H={h}, counts within 8H: xi={len(z)}, xi'={len(dz)}")
        print(" p | xi observed          | xi' observed         | xi' predicted")
        for p in (2,3,5,7):
            g = 0.5*log(t/(2*pi)) + 1j*pi/4
            pred = -log(p)*(1-log(p)/g)
            print(f"{p:2d} | {fmt(window_sum(z,t,h,p))} | "
                  f"{fmt(window_sum(dz,t,h,p))} | {fmt(pred)}")
