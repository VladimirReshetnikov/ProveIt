#!/usr/bin/env python3
"""Numerical and exact-symbolic checks for the report

    Dyadic Multiresolution and Product-Series Representations
    in the Fabius--Rvachev System.

The mathematical arguments in the accompanying LaTeX report are analytic.
This program is a reproducibility companion: it checks signs and normalization
constants, compares several finite representations of the same Fourier
transform, and produces the numerical tables quoted in the report.

The script deliberately uses only standard scientific-Python packages and no
network access.  Its main ingredients are:

* mpmath, for high-precision evaluation of the infinite sinc product;
* SymPy, for exact Walsh-moment and Gaussian-binomial identities;
* NumPy and Matplotlib, for inexpensive vectorized plots.

Conventions
-----------
The angular-frequency Fourier transform is

    hat(f)(t) = integral_R f(x) exp(-i*t*x) dx.

Rvachev's up-function has characteristic function

    Phi(t) = product_{j>=1} sinc(t/2**j),

where sinc(z)=sin(z)/z.  On [0,1], the bounded Fabius distribution
function and its density are

    F(x) = up(x-1),                 p(x) = F'(x)=2*up(2*x-1).

Usage
-----
    python numerical_experiments.py

Outputs
-------
    numerical_results.txt
    multiresolution_convergence.pdf
    multiresolution_convergence.png
    haar_energy_asymptotics.pdf
    haar_energy_asymptotics.png

The default settings are conservative enough for the tables while keeping a
normal laptop run fairly quick.  Increasing ``decimal_digits`` and
``half_integer_modes`` gives an independent precision check.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import floor, log2
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import sympy as sp

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parent
RESULTS_PATH = ROOT / "numerical_results.txt"


@dataclass(frozen=True)
class Settings:
    """Central precision and truncation parameters."""

    decimal_digits: int = 55
    product_factors: int = 160
    half_integer_modes: int = 200
    maximum_dyadic_level: int = 7
    walsh_exact_bits: int = 7


SETTINGS = Settings()
mp.mp.dps = SETTINGS.decimal_digits


# ---------------------------------------------------------------------------
# 1.  Infinite products and a rapidly convergent evaluator for up and F
# ---------------------------------------------------------------------------

def sinc(z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Return sin(z)/z, with the removable value at zero."""

    if z == 0:
        return mp.mpf(1)
    return mp.sin(z) / z


def phi(t: mp.mpf | mp.mpc, factors: int = SETTINGS.product_factors) -> mp.mpf | mp.mpc:
    r"""Evaluate Phi(t)=prod_{j>=1} sinc(t/2^j).

    For t in a fixed compact set, the omitted logarithmic tail is O(4^-factors).
    The loop is therefore far more accurate than needed at the sample points
    used below.
    """

    value: mp.mpf | mp.mpc = mp.mpf(1)
    scale = mp.mpf(2)
    for _ in range(factors):
        value *= sinc(t / scale)
        scale *= 2
    return value


@lru_cache(maxsize=1)
def half_integer_coefficients() -> tuple[mp.mpf, ...]:
    r"""Return A_m=Phi((2m+1)pi), the period-two cosine coefficients of up."""

    return tuple(
        mp.re(phi((2 * m + 1) * mp.pi))
        for m in range(SETTINGS.half_integer_modes)
    )


def up(x: mp.mpf | float) -> mp.mpf:
    r"""Evaluate Rvachev's up-function on the real line.

    Periodizing the compactly supported C-infinity function with period two
    gives the exact, rapidly convergent series

        up(x) = 1/2 + sum_{m>=0} A_m cos((2m+1) pi x),  |x|<=1.

    Integer Fourier modes vanish; the half-integer modes survive.
    """

    x = mp.mpf(x)
    if abs(x) > 1:
        return mp.mpf(0)
    total = mp.mpf("0.5")
    for m, coefficient in enumerate(half_integer_coefficients()):
        total += coefficient * mp.cos((2 * m + 1) * mp.pi * x)
    # Tiny negative values can arise only from truncation at a flat endpoint.
    return total


def fabius(x: mp.mpf | float) -> mp.mpf:
    """Evaluate the bounded Fabius distribution function."""

    x = mp.mpf(x)
    if x <= 0:
        return mp.mpf(0)
    if x >= 1:
        return mp.mpf(1)
    return up(x - 1)


def density(x: mp.mpf | float) -> mp.mpf:
    """Evaluate p(x)=F'(x)=2 up(2x-1), extended by zero."""

    x = mp.mpf(x)
    if x < 0 or x > 1:
        return mp.mpf(0)
    return 2 * up(2 * x - 1)


# ---------------------------------------------------------------------------
# 2.  Dyadic masses, Haar coefficients, and Faber--Schauder coefficients
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def dyadic_masses(level: int) -> tuple[mp.mpf, ...]:
    r"""Return Delta_{N,k}=F((k+1)/2^N)-F(k/2^N)."""

    n = 1 << level
    values = [fabius(mp.mpf(k) / n) for k in range(n + 1)]
    return tuple(values[k + 1] - values[k] for k in range(n))


@lru_cache(maxsize=None)
def haar_coefficients(level: int) -> tuple[mp.mpf, ...]:
    r"""Return all normalized Haar coefficients c_{level,k} of p.

    h_{n,k}=2^(n/2)(1_left_child-1_right_child), hence

        c_{n,k}=2^(n/2)(Delta_{n+1,2k}-Delta_{n+1,2k+1}).
    """

    masses = dyadic_masses(level + 1)
    factor = mp.power(2, mp.mpf(level) / 2)
    return tuple(
        factor * (masses[2 * k] - masses[2 * k + 1])
        for k in range(1 << level)
    )


@lru_cache(maxsize=None)
def schauder_coefficients(level: int) -> tuple[mp.mpf, ...]:
    r"""Return peak-one Faber--Schauder coefficients d_{level,k} of F."""

    masses = dyadic_masses(level + 1)
    return tuple(
        (masses[2 * k] - masses[2 * k + 1]) / 2
        for k in range(1 << level)
    )


def piecewise_constant_density(level: int, x: mp.mpf | float) -> mp.mpf:
    """Evaluate the dyadic conditional expectation p_N."""

    x = mp.mpf(x)
    if x < 0 or x > 1:
        return mp.mpf(0)
    n = 1 << level
    if x == 1:
        k = n - 1
    else:
        k = int(mp.floor(n * x))
    return n * dyadic_masses(level)[k]


# ---------------------------------------------------------------------------
# 3.  Paley Walsh functions and their exact Fourier product
# ---------------------------------------------------------------------------

def binary_weight(m: int) -> int:
    """The Hamming weight s_2(m)."""

    return m.bit_count()


def walsh_signs(m: int, bits: int) -> tuple[int, ...]:
    r"""Signs of the Paley Walsh function w_m on the 2^bits dyadic cells.

    The least significant bit of m multiplies the first Rademacher function,
    which is constant on halves; the next bit multiplies the quarters
    Rademacher function, and so on.
    """

    if m >= (1 << bits):
        raise ValueError("bits must exceed the binary length of m")
    m_bits = [(m >> j) & 1 for j in range(bits)]
    result: list[int] = []
    for k in range(1 << bits):
        parity = 0
        for j, bit in enumerate(m_bits):
            # Rademacher r_j reads the (j+1)-st binary digit of x.  On cell k
            # at depth bits this is bit number bits-1-j of k.
            digit = (k >> (bits - 1 - j)) & 1
            parity ^= bit & digit
        result.append(-1 if parity else 1)
    return tuple(result)


@lru_cache(maxsize=None)
def walsh_coefficients(level: int) -> tuple[mp.mpf, ...]:
    r"""Return a_m=int_0^1 p(x) w_m(x) dx for m<2^level.

    Since w_m is constant on level-N cells, the formula is exact once N is
    large enough:

        a_m = sum_k sign(m,k) Delta_{N,k}.
    """

    masses = dyadic_masses(level)
    return tuple(
        mp.fsum(sign * mass for sign, mass in zip(walsh_signs(m, level), masses))
        for m in range(1 << level)
    )


def walsh_fourier_product(m: int, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    r"""Evaluate W_m(z)=int_0^1 w_m(x)e^{-izx}dx by a finite product.

    For m>0, put N=1+floor(log2 m), write m=sum b_j 2^j, and r=s_2(m).
    Then

      W_m(z)=exp(-iz/2) * 2^(N+1) i^r/z * sin(z/2^(N+1))
             * prod_{b_j=0} cos(z/2^(j+2))
             * prod_{b_j=1} sin(z/2^(j+2)).

    The value at zero is interpreted by continuity.
    """

    z = mp.mpc(z)
    if m == 0:
        if z == 0:
            return mp.mpf(1)
        return mp.e ** (-1j * z / 2) * 2 * mp.sin(z / 2) / z
    if z == 0:
        return mp.mpf(0)

    n = 1 + floor(log2(m))
    r = binary_weight(m)
    value = (
        mp.e ** (-1j * z / 2)
        * mp.power(2, n + 1)
        * (1j ** r)
        * mp.sin(z / mp.power(2, n + 1))
        / z
    )
    for j in range(n):
        argument = z / mp.power(2, j + 2)
        if (m >> j) & 1:
            value *= mp.sin(argument)
        else:
            value *= mp.cos(argument)
    return value


def walsh_fourier_direct(m: int, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Independent cell-by-cell evaluation of W_m, used as a check."""

    if m == 0:
        n = 1
    else:
        n = 1 + floor(log2(m))
    h = mp.mpf(1) / (1 << n)
    if z == 0:
        return mp.mpf(1 if m == 0 else 0)
    total: mp.mpf | mp.mpc = mp.mpc(0)
    for k, sign in enumerate(walsh_signs(m, n)):
        left = k * h
        right = (k + 1) * h
        total += sign * (mp.e ** (-1j * z * left) - mp.e ** (-1j * z * right)) / (1j * z)
    return total


@lru_cache(maxsize=None)
def walsh_transform_approx(level: int, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Approximate hat(p)(z) with the first 2^level Walsh modes."""

    coefficients = walsh_coefficients(level)
    return mp.fsum(
        coefficient * walsh_fourier_product(m, z)
        for m, coefficient in enumerate(coefficients)
    )


# ---------------------------------------------------------------------------
# 4.  Uniform-cell and beta-mixture transform representations
# ---------------------------------------------------------------------------

def centered_cell_midpoint(level: int, k: int) -> mp.mpf:
    """Midpoint of the corresponding up-cell in [-1,1]."""

    return mp.mpf(2 * k + 1) / (1 << level) - 1


@lru_cache(maxsize=None)
def uniform_cell_phi(level: int, t: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    r"""Fourier transform of the uniform-cell mixture for up.

      Phi_N(t)=sinc(t/2^N) sum_k Delta_{N,k} exp(-it u_{N,k}).
    """

    masses = dyadic_masses(level)
    window = sinc(t / (1 << level))
    return window * mp.fsum(
        mass * mp.e ** (-1j * t * centered_cell_midpoint(level, k))
        for k, mass in enumerate(masses)
    )


@lru_cache(maxsize=None)
def atomic_midpoint_phi(level: int, t: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Midpoint-atomic transform, i.e. the same formula without the sinc window."""

    masses = dyadic_masses(level)
    return mp.fsum(
        mass * mp.e ** (-1j * t * centered_cell_midpoint(level, k))
        for k, mass in enumerate(masses)
    )


@lru_cache(maxsize=None)
def beta_mixture_p_mgf(level: int, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    r"""MGF of the derivative of the Bernstein polynomial B_{2^N}F.

    The derivative is a positive mixture of beta(k+1,n-k) densities with
    weights Delta_{N,k}.  A beta(a,b) random variable has MGF
    1F1(a;a+b;z), hence

      P_N(z)=sum_k Delta_{N,k} 1F1(k+1;n+1;z).
    """

    n = 1 << level
    masses = dyadic_masses(level)
    return mp.fsum(
        mass * mp.hyp1f1(k + 1, n + 1, z)
        for k, mass in enumerate(masses)
    )


@lru_cache(maxsize=None)
def beta_mixture_phi(level: int, t: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    """Convert the beta-mixture MGF of p to the Fourier transform of up."""

    return mp.e ** (1j * t) * beta_mixture_p_mgf(level, -2j * t)


# ---------------------------------------------------------------------------
# 5.  Exact SymPy checks: moments, q-binomials, and Hadamard inversion
# ---------------------------------------------------------------------------

def exact_walsh_moment(m: int, degree: int) -> sp.Rational:
    r"""Compute integral_0^1 x^degree w_m(x) dx exactly."""

    if m == 0:
        return sp.Rational(1, degree + 1)
    n = 1 + floor(log2(m))
    denominator = sp.Integer(1 << n)
    total = sp.Rational(0)
    for k, sign in enumerate(walsh_signs(m, n)):
        total += sign * (
            sp.Rational((k + 1) ** (degree + 1) - k ** (degree + 1),
                        (degree + 1) * denominator ** (degree + 1))
        )
    return sp.factor(total)


def exact_first_moment_formula(m: int) -> sp.Rational:
    r"""The claimed first nonzero Walsh moment.

      integral x^r w_m(x) dx = (-1)^r r! 2^(-2r-sigma(m)),

    where r=s_2(m) and sigma(m)=sum_j j*b_j.
    """

    r = binary_weight(m)
    sigma = sum(j for j in range(m.bit_length()) if (m >> j) & 1)
    return sp.Rational((-1) ** r * sp.factorial(r), 2 ** (2 * r + sigma))


def q_binomial(n: int, r: int, q: sp.Rational) -> sp.Expr:
    """Gaussian binomial coefficient [n choose r]_q."""

    if r < 0 or r > n:
        return sp.Integer(0)
    if r == 0 or r == n:
        return sp.Integer(1)
    numerator = sp.prod(1 - q ** (n - j) for j in range(r))
    denominator = sp.prod(1 - q ** (j + 1) for j in range(r))
    return sp.factor(numerator / denominator)


def check_exact_walsh_identities(max_bits: int) -> tuple[int, int]:
    """Return (number checked, number failed) for exact moment identities."""

    checked = 0
    failed = 0
    for n in range(1, max_bits + 1):
        for m in range(1, 1 << n):
            r = binary_weight(m)
            for degree in range(r):
                checked += 1
                if exact_walsh_moment(m, degree) != 0:
                    failed += 1
            checked += 1
            if exact_walsh_moment(m, r) != exact_first_moment_formula(m):
                failed += 1
    return checked, failed


def check_q_binomial_aggregate(max_bits: int) -> tuple[int, int]:
    r"""Check

      sum_{m<2^N, s_2(m)=r} 2^{-sigma(m)}
       =2^{-r(r-1)/2} [N choose r]_{1/2}.
    """

    q = sp.Rational(1, 2)
    checked = 0
    failed = 0
    for n in range(1, max_bits + 1):
        for r in range(n + 1):
            lhs = sum([
                sp.Rational(1, 2 ** sum(j for j in range(n) if (m >> j) & 1))
                for m in range(1 << n)
                if binary_weight(m) == r
            ])
            rhs = q ** (r * (r - 1) // 2) * q_binomial(n, r, q)
            checked += 1
            if sp.simplify(lhs - rhs) != 0:
                failed += 1
    return checked, failed


def check_hadamard_parseval(level: int) -> mp.mpf:
    """Return the residual in finite Walsh--Hadamard Parseval."""

    masses = dyadic_masses(level)
    coefficients = walsh_coefficients(level)
    left = mp.fsum(a * a for a in coefficients)
    right = (1 << level) * mp.fsum(d * d for d in masses)
    return left - right


# ---------------------------------------------------------------------------
# 6.  Haar-scale energy and its Bell--Bernoulli/sinc^4 asymptotic
# ---------------------------------------------------------------------------

def haar_energy(level: int) -> mp.mpf:
    """E_n=sum_k c_{n,k}^2=||p_{n+1}-p_n||_2^2."""

    return mp.fsum(c * c for c in haar_coefficients(level))


def derivative_l2_norm(order: int) -> mp.mpf:
    r"""Compute ||p^(order)||_2^2 from the half-integer Fourier series.

    If A_m=Phi((2m+1)pi), then

      ||p^(r)||_2^2 = 2^(2r+1) sum_m A_m^2 ((2m+1)pi)^(2r).

    The coefficients decrease faster than every power, so the finite sum is
    stable for the modest orders used here.
    """

    total = mp.fsum(
        coefficient ** 2 * ((2 * m + 1) * mp.pi) ** (2 * order)
        for m, coefficient in enumerate(half_integer_coefficients())
    )
    return mp.power(2, 2 * order + 1) * total


def haar_energy_asymptotic(level: int, terms: int = 3) -> mp.mpf:
    r"""First terms of the all-orders expansion of E_n.

      E_n ~ h^2/16 ||p'||^2 - h^4/384 ||p''||^2
              + h^6/20480 ||p'''||^2 + ...,

    where h=2^-n.  The coefficients are those of sinc(z)^4.
    """

    h = mp.mpf(1) / (1 << level)
    # Coefficients alpha_j=[z^(2j)] sinc(z)^4 for j=0,1,2.
    alpha = [mp.mpf(1), -mp.mpf(2) / 3, mp.mpf(1) / 5]
    value = mp.mpf(0)
    for j in range(min(terms, len(alpha))):
        value += (
            h ** (2 * j + 2)
            * alpha[j]
            / (16 * 16 ** j)
            * derivative_l2_norm(j + 1)
        )
    return value


# ---------------------------------------------------------------------------
# 7.  Report tables and plots
# ---------------------------------------------------------------------------

def mpfmt(value: mp.mpf | mp.mpc, digits: int = 18) -> str:
    """Compact deterministic formatting for real or complex mpmath numbers."""

    if isinstance(value, mp.mpc) or (hasattr(value, "imag") and mp.im(value) != 0):
        return f"{mp.nstr(mp.re(value), digits)} {mp.nstr(mp.im(value), digits, strip_zeros=False)}i"
    return mp.nstr(mp.re(value), digits)


def produce_results() -> str:
    lines: list[str] = []
    add = lines.append

    add("Dyadic Multiresolution and Product-Series Representations")
    add("Numerical and exact-symbolic verification")
    add("=" * 72)
    add(f"mpmath decimal digits       : {SETTINGS.decimal_digits}")
    add(f"sinc-product factors        : {SETTINGS.product_factors}")
    add(f"half-integer Fourier modes  : {SETTINGS.half_integer_modes}")
    add("")

    add("1. Normalizations")
    add("-" * 72)
    add(f"F(1/4)                      = {mpfmt(fabius(mp.mpf(1)/4), 30)}")
    add(f"Expected F(1/4)             = {mpfmt(mp.mpf(5)/72, 30)}")
    add(f"absolute residual           = {mpfmt(abs(fabius(mp.mpf(1)/4)-mp.mpf(5)/72), 8)}")
    add(f"sum of level-7 masses       = {mpfmt(mp.fsum(dyadic_masses(7)), 30)}")
    add("")

    add("2. Exact Walsh moment and q-binomial checks")
    add("-" * 72)
    checked, failed = check_exact_walsh_identities(SETTINGS.walsh_exact_bits)
    add(f"Walsh moment identities     : {checked} checked, {failed} failed")
    checked, failed = check_q_binomial_aggregate(SETTINGS.walsh_exact_bits)
    add(f"q-binomial aggregates       : {checked} checked, {failed} failed")
    add("")
    add("Selected first nonzero Walsh moments:")
    add("  m    binary     r    integral x^r w_m(x) dx")
    for m in (1, 2, 3, 5, 6, 7, 15, 23, 31):
        r = binary_weight(m)
        add(f"  {m:<4d} {format(m, 'b'):<10s} {r:<4d} {exact_walsh_moment(m,r)}")
    add("")

    add("3. Walsh finite-product transform")
    add("-" * 72)
    z = mp.mpc("3.7", "0.4")
    max_residual = mp.mpf(0)
    for m in range(16):
        max_residual = max(max_residual, abs(walsh_fourier_product(m, z)-walsh_fourier_direct(m,z)))
    add(f"max residual m=0,...,15 at z=3.7+0.4i: {mpfmt(max_residual, 8)}")
    add("")

    add("4. Symmetry selection rule for Walsh coefficients")
    add("-" * 72)
    coefficients = walsh_coefficients(7)
    max_odd = max(abs(coefficients[m]) for m in range(1 << 7) if binary_weight(m) % 2 == 1)
    max_even = max(abs(coefficients[m]) for m in range(1 << 7) if binary_weight(m) % 2 == 0 and m != 0)
    add(f"max |a_m|, odd Hamming weight  (should be 0): {mpfmt(max_odd, 8)}")
    add(f"max |a_m|, nonzero even weight             : {mpfmt(max_even, 18)}")
    add(f"Hadamard Parseval residual, level 7         : {mpfmt(check_hadamard_parseval(7), 8)}")
    add("")

    add("5. Transform convergence")
    add("-" * 72)
    sample_t = [mp.mpf("0.7"), mp.mpf("3.1"), mp.mpf("7.3"), mp.mpf("11.2")]
    add("level   max uniform-cell error   max atomic error   max beta-mixture error   max Walsh error")
    for level in range(2, SETTINGS.maximum_dyadic_level + 1):
        uniform_error = max(abs(uniform_cell_phi(level,t)-phi(t)) for t in sample_t)
        atomic_error = max(abs(atomic_midpoint_phi(level,t)-phi(t)) for t in sample_t)
        beta_error = max(abs(beta_mixture_phi(level,t)-phi(t)) for t in sample_t)
        walsh_error = max(abs(mp.e**(1j*t)*walsh_transform_approx(level,2*t)-phi(t)) for t in sample_t)
        add(
            f"{level:>3d}     {mpfmt(uniform_error,10):>20s}"
            f" {mpfmt(atomic_error,10):>18s} {mpfmt(beta_error,10):>23s}"
            f" {mpfmt(walsh_error,10):>17s}"
        )
    add("")

    add("6. Haar energy and all-orders continuum expansion")
    add("-" * 72)
    norm1 = derivative_l2_norm(1)
    norm2 = derivative_l2_norm(2)
    norm3 = derivative_l2_norm(3)
    add(f"||p'||_2^2                   = {mpfmt(norm1, 24)}")
    add(f"||p''||_2^2                  = {mpfmt(norm2, 24)}")
    add(f"||p'''||_2^2                 = {mpfmt(norm3, 24)}")
    add(" n        E_n                 16*4^n E_n          rel.error(3-term)")
    for n in range(2, SETTINGS.maximum_dyadic_level + 1):
        energy = haar_energy(n)
        scaled = 16 * mp.power(4,n) * energy
        asymptotic = haar_energy_asymptotic(n,3)
        relative = abs(energy-asymptotic)/energy
        add(f"{n:>2d}  {mpfmt(energy,14):>18s}  {mpfmt(scaled,16):>20s}  {mpfmt(relative,8):>16s}")
    add("")

    add("7. Low-level rational-structure samples (high-precision decimals)")
    add("-" * 72)
    for level in range(1,5):
        c = haar_coefficients(level)
        d = schauder_coefficients(level)
        add(f"level {level}: Haar c_{{n,k}} = " + ", ".join(mpfmt(x,12) for x in c))
        add(f"         Schauder d_{{n,k}} = " + ", ".join(mpfmt(x,12) for x in d))
    add("")

    return "\n".join(lines) + "\n"


def produce_plots() -> None:
    """Create two compact figures used by the report."""

    levels = np.arange(2, SETTINGS.maximum_dyadic_level + 1)
    sample_t = [mp.mpf("0.7"), mp.mpf("3.1"), mp.mpf("7.3"), mp.mpf("11.2")]
    uniform_errors = []
    atomic_errors = []
    beta_errors = []
    walsh_errors = []
    for level in levels:
        uniform_errors.append(float(max(abs(uniform_cell_phi(int(level),t)-phi(t)) for t in sample_t)))
        atomic_errors.append(float(max(abs(atomic_midpoint_phi(int(level),t)-phi(t)) for t in sample_t)))
        beta_errors.append(float(max(abs(beta_mixture_phi(int(level),t)-phi(t)) for t in sample_t)))
        walsh_errors.append(float(max(abs(mp.e**(1j*t)*walsh_transform_approx(int(level),2*t)-phi(t)) for t in sample_t)))

    plt.figure(figsize=(7.2,4.6))
    plt.semilogy(levels, uniform_errors, marker="o", label="uniform-cell")
    plt.semilogy(levels, atomic_errors, marker="s", label="midpoint atomic")
    plt.semilogy(levels, beta_errors, marker="^", label="beta mixture")
    plt.semilogy(levels, walsh_errors, marker="d", label="Walsh/Hadamard")
    plt.xlabel("dyadic level N")
    plt.ylabel("maximum error at four frequencies")
    plt.title("Convergence of four finite transform representations")
    plt.grid(True, which="both", linewidth=0.4)
    plt.legend()
    plt.tight_layout()
    plt.savefig(ROOT / "multiresolution_convergence.pdf")
    plt.savefig(ROOT / "multiresolution_convergence.png", dpi=180)
    plt.close()

    norm1 = float(derivative_l2_norm(1))
    scaled = [float(16 * mp.power(4,int(n)) * haar_energy(int(n))) for n in levels]
    three_term_scaled = [float(16 * mp.power(4,int(n)) * haar_energy_asymptotic(int(n),3)) for n in levels]
    plt.figure(figsize=(7.2,4.6))
    plt.plot(levels, scaled, marker="o", label=r"$16\,4^n E_n$")
    plt.plot(levels, three_term_scaled, marker="s", label="three-term expansion")
    plt.axhline(norm1, linestyle="--", label=r"$\|p'\|_2^2$")
    plt.xlabel("Haar scale n")
    plt.ylabel("scaled energy")
    plt.title("Haar detail energy and its continuum limit")
    plt.grid(True, linewidth=0.4)
    plt.legend()
    plt.tight_layout()
    plt.savefig(ROOT / "haar_energy_asymptotics.pdf")
    plt.savefig(ROOT / "haar_energy_asymptotics.png", dpi=180)
    plt.close()


def main() -> None:
    text = produce_results()
    RESULTS_PATH.write_text(text, encoding="utf-8")
    produce_plots()
    print(text)


if __name__ == "__main__":
    main()
