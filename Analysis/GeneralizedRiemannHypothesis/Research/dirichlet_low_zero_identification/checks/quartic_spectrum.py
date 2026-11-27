"""A signed-zero explicit-formula example. Dependencies: NumPy, SciPy, mpmath.

The output is a floating-point illustration. A sign scan need not detect a
zero of even multiplicity or an unresolved pair of zeros.
"""
import cmath
import math

import mpmath as mp
import numpy as np
from scipy.optimize import brentq
from scipy.special import bernoulli, loggamma

Q = 5
CHI = np.array([1, 1j, -1j, -1], dtype=complex)  # residues 1,2,3,4
RESIDUES = np.arange(1, Q)
TAU = np.dot(CHI, np.exp(2j * np.pi * RESIDUES / Q))
ROOT_NUMBER = TAU / (1j * math.sqrt(Q))

# Hurwitz zeta via Euler--Maclaurin. The four residue classes are combined
# after adding the endpoint terms, then multiplied by 5^{-s}.
TERMS, ORDER = 120, 9
A = RESIDUES / Q
LOG_BASES = np.log(np.arange(TERMS)[:, None] + A)
ENDPOINT = TERMS + A
LOG_ENDPOINT = np.log(ENDPOINT)
BERNOULLI = bernoulli(2 * ORDER)
CORRECTIONS = [BERNOULLI[2 * k] / math.factorial(2 * k)
               for k in range(1, ORDER + 1)]


def lvalue(t):
    s = 0.5 + 1j * t
    hurwitz = np.exp(-s * LOG_BASES).sum(axis=0)
    last_power = np.exp(-s * LOG_ENDPOINT)
    hurwitz += last_power * (ENDPOINT / (s - 1) + 0.5)
    rising = s
    for k, coefficient in enumerate(CORRECTIONS, 1):
        hurwitz += coefficient * rising * last_power * ENDPOINT ** (1 - 2 * k)
        rising *= (s + 2 * k - 1) * (s + 2 * k)
    return Q ** (-s) * np.dot(CHI, hurwitz)


def hardy(t):
    phase = (0.5 * t * math.log(Q / math.pi)
             + loggamma(0.75 + 0.5j * t).imag
             - 0.5 * cmath.phase(ROOT_NUMBER))
    return (cmath.exp(1j * phase) * lvalue(t)).real


def scan(cutoff, step):
    samples = np.arange(-cutoff, cutoff + step / 2, step)
    values = np.array([hardy(t) for t in samples])
    changes = np.flatnonzero(np.signbit(values[:-1]) != np.signbit(values[1:]))
    return np.array([brentq(hardy, samples[k], samples[k + 1], xtol=1e-12)
                     for k in changes])


def main():
    # Independent evaluation of L by mpmath's Hurwitz zeta.
    mp.mp.dps = 35
    controls = [-241.125, -73.25, -1, 0, 12.5, 117.75, 242.125]
    discrepancies = []
    for t in controls:
        s = mp.mpc(0.5, t)
        check = Q ** (-s) * sum(complex(c) * mp.zeta(s, mp.mpf(int(a)) / Q)
                                 for a, c in zip(RESIDUES, CHI))
        discrepancies.append(abs(lvalue(t) - complex(check)))
    print(f"Maximum L discrepancy at {len(controls)} control points: "
          f"{max(discrepancies):.2e}")

    cutoff, radius = 256, 0.36
    coarse = scan(cutoff, 1 / 8)
    fine = scan(cutoff, 1 / 32)
    print(f"Sign-change roots at meshes 1/8 and 1/32: {len(coarse)}, {len(fine)}")
    if len(coarse) != len(fine) or not np.allclose(coarse, fine, rtol=0, atol=1e-8):
        print("The two scans differ. All reported sums use the fine scan.")
    print("Nearest signed ordinates:",
          np.array2string(fine[np.argsort(np.abs(fine))[:6]], precision=8))

    # In log-prime space the probe is a spline centered at log 2. It is the
    # convolution of four uniform densities on [-radius/4,radius/4], rescaled
    # to have value 1 at its center. numpy.sinc(y) = sin(pi*y)/(pi*y).
    # For the conjugate character the signed ordinates are reflected.
    expected = -2j * math.log(2) / math.sqrt(2)
    print(f"Arithmetic difference, chi minus conjugate: {expected.imag:+.9f}i")
    for height in (32, 64, 128, 256):
        gamma = fine[np.abs(fine) <= height]
        weight = (3 * radius / 4) * np.sinc(radius * gamma / (4 * np.pi)) ** 4
        s_chi = np.sum(weight * np.exp(1j * gamma * math.log(2)))
        difference = s_chi - np.conj(s_chi)
        print(f"H={height:3d}  roots={len(gamma):3d}  "
              f"sum(chi)={s_chi.real:+.8f}{s_chi.imag:+.8f}i  "
              f"difference={difference.imag:+.9f}i  "
              f"absolute error={abs(difference - expected):.2e}")


if __name__ == "__main__":
    main()
