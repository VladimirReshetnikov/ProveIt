"""Numerical checks for the endpoint paper. Requires Python, NumPy, SciPy and mpmath."""
import math
import numpy as np
from scipy.integrate import quad
from scipy.special import i0e, i1e
import mpmath as mp


def kernel(v):
    if v < 1e-5:
        return 0.5 * math.log(2 * math.pi) - math.log(v) - v * v / 8
    u = 1 / v**2
    if u < 1e-5:
        return u * (1 - u / 4 + u**3 / 64)
    return -math.log(i0e(u))


def moment(fn):
    return sum(quad(fn, a, b, epsabs=2e-11, epsrel=2e-11, limit=300)[0]
               for a, b in [(0, 1), (1, math.inf)])


def check_tilt():
    weights = np.array([1.0, .7, .2, .4])
    freqs = np.array([1.0, 2.0, 3.0, 1.0])  # includes dependence and multiplicity
    for tmax in (0.7, 5.0, 27.0):
        for s in (0.3, 3.0, 9.0):
            def weighted(t, order):
                d = np.dot(weights, 1 - np.cos(freqs * t))
                return 2 * (1 - t / tmax) / tmax * math.exp(-s * d) * d**order
            z, zd = [quad(weighted, 0, tmax, args=(k,), epsabs=1e-12, limit=300)[0]
                     for k in (0, 1)]
            z_ind = np.prod(i0e(s * weights))
            mean_ind = np.dot(weights, 1 - i1e(s * weights) / i0e(s * weights))
            assert z >= z_ind - 1e-11 and zd / z <= mean_ind + 1e-11
            print(f"T={tmax:4.1f}  s={s:3.1f}  Z/Z_ind={z/z_ind:8.5f}  "
                  f"mean={zd/z:.6f}  independent={mean_ind:.6f}")


def mangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            while n % p == 0:
                n //= p
            return mp.log(p) if n == 1 else 0


def check_ramp():
    mp.mp.dps = 24
    gammas = [mp.im(mp.zetazero(k)) for k in range(1, 33)]
    mass = 2 + mp.euler - mp.log(4 * mp.pi)
    rem = mass - sum(2 / (mp.mpf('.25') + g*g) for g in gammas)
    for x in (10, 73, 257):
        t, z = mp.log(x), mp.mpf(1)/x
        observed = mp.sqrt(x)*(sum(mangoldt(n)*(mp.mpf(1)/n - z) for n in range(2, x+1))
                              - t + 1 + mp.euler)
        trivial = z + (1-z)*mp.log(1-z)/2 - (1+z)*mp.log(1+z)/2
        exact_kernel = observed + mp.sqrt(x)*(trivial - z*mp.log(2*mp.pi))
        trunc = sum(2*mp.cos(g*t)/(mp.mpf('.25')+g*g) for g in gammas)
        assert abs(exact_kernel-trunc) <= rem
        print(f"x={x:3d}  kernel from primes={float(exact_kernel): .7f}  "
              f"32-zero sum={float(trunc): .7f}  omitted mass={float(rem):.7f}")


if __name__ == '__main__':
    a = moment(kernel)
    b = moment(lambda v: kernel(v)*math.log(v))
    c = a / (2*math.pi)
    print(f"A={a:.12f}  B={b:.12f}  C={c:.12f}  C^2={c*c:.12f}")
    check_tilt()
    check_ramp()
