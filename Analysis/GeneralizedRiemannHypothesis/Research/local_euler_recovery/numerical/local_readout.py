"""Floating-point illustration of a local Dirichlet zero readout.

Run with Python 3, NumPy and SciPy. The path being evaluated is
Dirichlet L -> critical-line sign changes -> local weighted sum -> Euler factor.
Sign-change searches and double-precision integration are diagnostic only.
"""

from dataclasses import dataclass
from math import factorial
from itertools import combinations_with_replacement

import numpy as np
from scipy.integrate import quad, simpson
from scipy.interpolate import BSpline
from scipy.optimize import brentq
from scipy.special import bernoulli, digamma, loggamma, roots_legendre


@dataclass
class Character:
    name: str
    q: int
    parity: int
    # values at 1,...,q
    values: tuple

    def chi(self, n):
        return self.values[(n - 1) % self.q]


CHARACTERS = (
    Character("zeta", 1, 0, (1,)),
    Character("beta", 4, 1, (1, 0, -1, 0)),
    Character("quartic5", 5, 1, (1, 1j, -1j, -1, 0)),
)


class CriticalLine:
    """Euler--Maclaurin for sum_a chi(a) q^(-s) zeta(s,a/q)."""

    def __init__(self, character, highest_t):
        self.chi = character
        self.n = int(highest_t) + 8
        self.order = 8
        q = character.q
        residues = [a for a in range(1, q+1) if character.chi(a)]
        self.values = np.array([character.chi(a) for a in residues], dtype=complex)
        self.ends = self.n + np.array(residues, dtype=float) / q
        self.logs = np.log((np.arange(self.n)[:, None] +
                            np.array(residues)[None, :] / q) * q)
        self.amplitudes = self.values[None, :] * np.exp(-self.logs / 2)
        bern = bernoulli(2 * self.order)
        self.coefficients = [bern[2*k]/factorial(2*k) for k in range(1, self.order+1)]
        eps = (sum(character.chi(a)*np.exp(2j*np.pi*a/q)
                   for a in range(1, q+1)) / (1j**character.parity * np.sqrt(q)))
        self.phase = np.angle(eps)/2

    def l_value(self, s):
        if s.real == 0.5:
            main = (self.amplitudes * np.exp(-1j*s.imag*self.logs)).sum()
        else:
            main = (self.values[None, :] * np.exp(-s*self.logs)).sum()
        w = self.ends
        tail = w/(s-1) + 0.5
        rising = s
        for k, coefficient in enumerate(self.coefficients, 1):
            tail = tail + coefficient*rising*w**(1-2*k)
            rising *= (s+2*k-1)*(s+2*k)
        return main + (self.values * np.exp(-s*np.log(self.chi.q*w)) * tail).sum()

    def theta(self, t):
        return (loggamma((0.5+1j*t+self.chi.parity)/2).imag
                + (t/2)*np.log(self.chi.q/np.pi) - self.phase)

    def value(self, t):
        return np.exp(1j*self.theta(t))*self.l_value(0.5+1j*t)

    def endpoint_index(self, t, subdivisions):
        # On sigma=2, |L-1| <= zeta(2)-1 < 1. Continue its principal argument
        # horizontally to Re(s)=1/2. Differences of endpoint indices count all
        # complex zeros by the argument principle and the functional equation.
        sigmas = 0.5 + 1.5*np.linspace(1, 0, subdivisions+1)**2
        vals = [self.l_value(sigma+1j*t) for sigma in sigmas]
        phases = np.unwrap(np.angle(vals))
        if np.max(np.abs(np.diff(phases))) >= np.pi/3:
            raise ArithmeticError("horizontal argument step too large")
        index = (self.theta(t)+phases[-1])/np.pi
        if abs(index - round(index)) > 1e-7:
            raise ArithmeticError("endpoint phase failed integer check")
        return round(index)

    def zeros(self, lo, hi, step):
        grid = np.linspace(lo, hi, int(np.ceil((hi-lo)/step))+1)
        curve = np.array([self.value(t) for t in grid])
        changes = np.flatnonzero(np.signbit(curve.real[1:]) != np.signbit(curve.real[:-1]))
        roots = [brentq(lambda t: self.value(t).real, grid[k], grid[k+1], xtol=3e-12)
                 for k in changes]
        return np.array(roots), np.max(np.abs(curve.imag))


def kernel_nodes(R, degree):
    # The compact cutoff only affects this floating-point quadrature.
    def raw(x):
        c = np.cosh(np.pi*x)
        return np.exp(-np.cosh(np.pi*x/2) - R*c/(R+c))
    norm = 2*quad(raw, 0, 7, epsabs=1e-14, epsrel=1e-14)[0]
    nodes, weights = roots_legendre(degree)
    return 7*nodes, 7*weights*raw(7*nodes)/norm


def parameters(T, Q, p):
    m, b = 4, 8*p
    L = np.log(np.exp(np.e)*Q*(T+3))
    R = 32*np.log(L)
    B = m*b
    H = 2*B + np.log(4*R)/np.pi + 2
    return m, b, R, B, H


def local_readout(zeros, T, Q, p, degree):
    m, b, R, B, H = parameters(T, Q, p)
    local = zeros[np.abs(zeros-T) <= H]
    nodes, weights = kernel_nodes(R, degree)
    spline = BSpline.basis_element(np.arange(m+1), extrapolate=False)
    dspline = spline.derivative()
    u = np.log(p)

    def test(t):
        s = (t[:, None]-T-nodes[None, :]+B)/(2*b)
        density = np.nan_to_num(spline(s), nan=0.0) @ weights/(2*b)
        slope = np.nan_to_num(dspline(s), nan=0.0) @ weights/(2*b)**2
        return np.exp(1j*u*t)*(density+slope/(1j*u))

    # int h = 0 exactly, so remove a constant before quadrature. The kernel
    # integral was truncated to [-7,7] and the spline is supported in [-B,B].
    grid = np.linspace(T-B-7, T+B+7, 40*(B+7)+1)
    hgrid = np.concatenate([test(t) for t in np.array_split(grid, (len(grid)+511)//512)])
    gamma_density = digamma((0.5+1j*grid)/2).real
    gamma = simpson(hgrid*(gamma_density-digamma((0.5+1j*T)/2).real), x=grid)
    scale = np.sqrt(p)/u
    zero_reading = -2*np.pi*scale*test(local).sum()
    return len(local), zero_reading+scale*gamma, zero_reading


def main():
    T, Q = 1000, 5
    primes = [2, 3, 5, 7]
    _, _, R, _, largest_radius = parameters(T, Q, max(primes))
    print(f"T = {T}, Q = {Q}, m = 4, b = 8p, B = 32p, R = {R:.8f};")
    print(f"H = 2B + log(4R)/pi + 2; largest radius {largest_radius:.5f}")
    print("sign-change steps 0.11 and 0.055; quadrature degrees 160 and 240")
    print("all root counts matched the argument principle at 64 and 128 horizontal subdivisions")
    print("character  prime   roots  Re(readout)   Im(readout)    Re(chi)  Im(chi)  error")
    root_lists = {}
    for character in CHARACTERS:
        z = CriticalLine(character, T+largest_radius)
        old, _ = z.zeros(T-largest_radius, T+largest_radius, 0.11)
        roots, phase_error = z.zeros(T-largest_radius, T+largest_radius, 0.055)
        if len(old) != len(roots) or np.max(np.abs(old-roots)) > 2e-9:
            raise ArithmeticError("root list changed on refinement")
        if phase_error > 1e-8:
            raise ArithmeticError("functional-equation phase check failed")
        root_lists[character.name] = roots
        for p in primes:
            _, check_result, _ = local_readout(roots, T, Q, p, 160)
            n, result, _ = local_readout(roots, T, Q, p, 240)
            if abs(result - check_result) > 2e-6:
                raise ArithmeticError("quadrature changed on refinement")
            H = parameters(T, Q, p)[-1]
            for subdivisions in (64, 128):
                observed_count = (z.endpoint_index(T+H, subdivisions)
                                  - z.endpoint_index(T-H, subdivisions))
                if n != observed_count:
                    raise ArithmeticError("zero list disagrees with argument-principle count")
            expected = character.chi(p)
            if abs(result - expected) >= 1e-4:
                raise ArithmeticError("prime reading exceeds the reported experimental tolerance")
            print(f"{character.name:9} {p:4d} {n:7d}  {result.real: .8f}   "
                  f"{result.imag: .8f}   {expected.real:5.1f}    {expected.imag:5.1f}  "
                  f"{abs(result-expected):.3g}")

    # Form a single unlabeled list, including a repeated factor. The search
    # receives only this list and an upper bound of three on the factor count.
    planted = ("zeta", "quartic5", "quartic5")
    pooled = np.sort(np.concatenate([root_lists[name] for name in planted]))
    raw = np.array([local_readout(pooled, T, Q, p, 240)[2] for p in primes])
    scores = []
    for count in range(4):
        for candidate in combinations_with_replacement(CHARACTERS, count):
            signature = np.array([sum(chi.chi(p) for chi in candidate) for p in primes])
            error = np.max(np.abs(raw-signature))
            scores.append((error, tuple(chi.name for chi in candidate)))
    scores.sort()
    if scores[0][1] != planted or scores[0][0] >= 3e-4:
        raise ArithmeticError("pooled character identification failed")
    print()
    print(f"Unknown product among {len(scores)} candidates of degrees 0 through 3")
    print("Zero-only readings: " + ", ".join(f"{z.real:.6f}{z.imag:+.6f}i" for z in raw))
    print(f"Selected factors: {', '.join(scores[0][1])}; largest residual {scores[0][0]:.3g}")
    print(f"Next-closest candidate residual: {scores[1][0]:.6f}")


if __name__ == "__main__":
    main()
