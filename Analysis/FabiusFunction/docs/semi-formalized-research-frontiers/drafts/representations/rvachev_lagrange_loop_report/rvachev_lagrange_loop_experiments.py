#!/usr/bin/env python3
"""Numerical and exact-algebra checks for the Rvachev/Lagrange loop report.

The script checks the degree-2 pure-shift representation on [-1,1]

    ell_j(x) = (1/m) sum_{|k|<2m} (M(D)^(-1) ell_j)(k/m) up(x-k/m),

with m=2^d=4.  Polynomial/deconvolution coefficients are computed exactly
with fractions.  Values of Rvachev's up-function are evaluated independently
from its Fourier inversion formula

    up(x) = 2 int_0^infty Phi(xi) cos(2*pi*xi*x) dxi,
    Phi(xi) = product_{r>=0} sinc(pi*xi/2^r).

The integral and product are truncated only for the numerical validation; the
identity itself is exact and is proved in the accompanying LaTeX report from
the repository's Strang--Fix/Appell synthesis theorem.

Dependencies: numpy, scipy.  No network access is needed.
"""

from __future__ import annotations

import math
from fractions import Fraction
from functools import lru_cache

import numpy as np
from scipy.integrate import quad


def sinc_pi(x: float) -> float:
    """sin(pi*x)/(pi*x), with its removable value at zero."""
    if x == 0.0:
        return 1.0
    return math.sin(math.pi * x) / (math.pi * x)


def up_hat(xi: float, factors: int = 50) -> float:
    """Truncated infinite sinc product for the Fourier transform of up."""
    p = 1.0
    y = xi
    for _ in range(factors):
        p *= sinc_pi(y)
        y *= 0.5
    return p


@lru_cache(maxsize=None)
def up_value_rounded(x_rounded: float, cutoff: int = 40) -> float:
    """Fourier-inversion evaluation of up at a cached rounded argument.

    The integral is split into unit intervals.  The product decays rapidly,
    and cutoff=40 is ample for the degree-2 checks below (about 1e-9 error).
    """
    x = x_rounded
    if abs(x) >= 1.0:
        # At |x|>1 the exact value is zero; at |x|=1 endpoint flatness gives 0.
        return 0.0

    def integrand(xi: float) -> float:
        return up_hat(xi) * math.cos(2.0 * math.pi * xi * x)

    total = 0.0
    for n in range(cutoff):
        val, _err = quad(
            integrand,
            float(n),
            float(n + 1),
            epsabs=1e-12,
            epsrel=1e-12,
            limit=100,
        )
        total += val
    return 2.0 * total


def up_value(x: float) -> float:
    """Cached wrapper; rounding merges numerically identical dyadic arguments."""
    return up_value_rounded(round(float(x), 14))


def ell_degree2(j: int, x: Fraction | float):
    """Lagrange cardinals for nodes -1, 0, 1."""
    if j == 0:
        return x * (x - 1) / 2
    if j == 1:
        return 1 - x * x
    if j == 2:
        return x * (x + 1) / 2
    raise ValueError("j must be 0, 1, or 2")


def deconvolved_ell_degree2(j: int, x: Fraction) -> Fraction:
    """Apply M(D)^(-1)=1-D^2/18 on degree <=2 polynomials exactly."""
    if j == 0:
        # ell=(x^2-x)/2, ell''=1
        return (x * x - x) / 2 - Fraction(1, 18)
    if j == 1:
        # ell=1-x^2, ell''=-2
        return 1 - x * x + Fraction(1, 9)
    if j == 2:
        # ell=(x^2+x)/2, ell''=1
        return (x * x + x) / 2 - Fraction(1, 18)
    raise ValueError("j must be 0, 1, or 2")


def analysis_matrix_degree2() -> tuple[np.ndarray, list[int]]:
    """Exact-formula analysis matrix A, returned numerically.

    c_k = (1/m) (M(D)^(-1) p)(k/m), m=4, |k|<8.
    Thus A has 15 rows (shift coefficients) and 3 columns (nodal data).
    """
    m = 4
    ks = list(range(-2 * m + 1, 2 * m))  # -7,...,7; boundary-touch atoms omitted
    A = np.zeros((len(ks), 3), dtype=float)
    for row, k in enumerate(ks):
        x = Fraction(k, m)
        for j in range(3):
            A[row, j] = float(deconvolved_ell_degree2(j, x) / m)
    return A, ks


def synthesis_matrix_degree2(ks: list[int]) -> np.ndarray:
    """Nodal synthesis matrix S_ik=up(tau_i-k/4), tau=(-1,0,1)."""
    nodes = (-1.0, 0.0, 1.0)
    m = 4
    S = np.zeros((3, len(ks)), dtype=float)
    for i, tau in enumerate(nodes):
        for col, k in enumerate(ks):
            S[i, col] = up_value(tau - k / m)
    return S


def synthesize_cardinal(j: int, x: float, A: np.ndarray, ks: list[int]) -> float:
    """Evaluate the j-th synthesized Lagrange cardinal at x."""
    return sum(A[row, j] * up_value(x - k / 4.0) for row, k in enumerate(ks))


def main() -> None:
    A, ks = analysis_matrix_degree2()
    S = synthesis_matrix_degree2(ks)

    print("Degree-2 nodes: -1, 0, 1")
    print("m=4, retained shifts k/4 with k=-7,...,7 (15 atoms)")
    print()

    # Perfect reconstruction at the nodes: S A = I_3.
    SA = S @ A
    print("S @ A =")
    print(np.array2string(SA, precision=12, suppress_small=True))
    print("||S A - I||_inf =", np.linalg.norm(SA - np.eye(3), ord=np.inf))
    print()

    # The coefficient-space closure Pi=A S is an idempotent rank-3 projector.
    Pi = A @ S
    print("||Pi^2-Pi||_inf =", np.linalg.norm(Pi @ Pi - Pi, ord=np.inf))
    eig = np.linalg.eigvals(Pi)
    eig_sorted = sorted(eig.real, reverse=True)
    print("eigenvalues(Pi), real parts =")
    print(np.array2string(np.array(eig_sorted), precision=10, suppress_small=True))
    print()

    # Validate the whole cardinal functions on a dense grid.
    grid = np.linspace(-1.0, 1.0, 65)
    for j in range(3):
        errors = []
        for x in grid:
            got = synthesize_cardinal(j, float(x), A, ks)
            want = float(ell_degree2(j, float(x)))
            errors.append(abs(got - want))
        print(f"max grid error for ell_{j}: {max(errors):.3e}")

    print()
    print("Selected exact shift coefficients for the central cardinal ell_1=1-x^2:")
    for k in ks:
        x = Fraction(k, 4)
        c = deconvolved_ell_degree2(1, x) / 4
        print(f"  k={k:2d}, center={str(x):>5s}, c={c}")


if __name__ == "__main__":
    main()
