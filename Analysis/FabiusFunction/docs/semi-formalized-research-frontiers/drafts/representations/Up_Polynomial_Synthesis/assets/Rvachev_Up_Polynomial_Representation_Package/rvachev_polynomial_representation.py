#!/usr/bin/env python3
"""Exact polynomial representation by shifted/scaled Rvachev up-functions.

This script accompanies the report
    Exact Polynomial Synthesis by Finite Rvachev Up-Function Dictionaries.

It implements the exact algebra developed there.  The central task is:

    Given a polynomial P(t) of degree <= d and an integer J >= 1, construct
    rational numbers b_0,...,b_{J+d} such that, on 0 <= t <= J,

        P(t) = (1/M) * sum_{r=0}^{J+d} b_r
                    up((t - (M-d-1+r))/M),       M = 2**d.

Only J+d+1 atoms are used.  For J=1 the count is d+2; the report proves that
no fixed dictionary of fewer nontrivial affine up-atoms can span all degree-d
polynomials on an interval.  The implementation is output-sensitive: it never
constructs the naive 2**(d+1) active coefficients.

The exact symbolic routines use SymPy rationals.  Numerical verification uses
an independent inverse-Fourier evaluator for up.  The numerical evaluator is
for experiments only; all coefficient identities are exact.

Fourier convention:
    f_hat(xi) = integral f(x) exp(-2*pi*i*x*xi) dx.
Then
    up_hat(xi) = product_{j>=0} sinc(pi*xi/2**j),
where sinc(y)=sin(y)/y.

Usage examples
--------------
    python rvachev_polynomial_representation.py --examples
    python rvachev_polynomial_representation.py --degree 4 --poly "3*t**4-2*t+7"
    python rvachev_polynomial_representation.py --determinants 12
    python rvachev_polynomial_representation.py --verify 4

The code is deliberately verbose and heavily commented so that every finite
algebraic step can be audited or ported to a proof assistant.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, List, Sequence, Tuple

import mpmath as mp
import numpy as np
import sympy as sp


# Global symbolic variables used by the public API.
t = sp.Symbol("t")
z = sp.Symbol("z")


@dataclass(frozen=True)
class SparseRepresentation:
    """A common-scale finite up-function representation on [0,J].

    The represented identity is

        P(t) = sum_i coefficient_i * up((t-center_i)/M).

    Internally the theorem first produces b_i and a prefactor 1/M.  The
    ``coefficients`` field stores b_i/M, which is usually the most convenient
    form for display and numerical evaluation.
    """

    degree_parameter: int
    cells: int
    scale: int
    centers: Tuple[int, ...]
    coefficients: Tuple[sp.Rational, ...]

    def as_pairs(self) -> List[Tuple[int, sp.Rational]]:
        return list(zip(self.centers, self.coefficients))


def _as_poly(expr: sp.Expr | sp.Poly, variable: sp.Symbol = t) -> sp.Poly:
    """Convert an expression to an exact univariate polynomial."""

    poly = expr if isinstance(expr, sp.Poly) else sp.Poly(sp.expand(expr), variable)
    if poly.gens != (variable,):
        poly = sp.Poly(poly.as_expr(), variable)
    return poly


def rvachev_cumulant(order: int) -> sp.Rational:
    r"""Return kappa_{2*order} for the centered up-density.

    The moment generating function is

        M_u(z) = product_{j>=0} sinh(z/2^{j+1})/(z/2^{j+1}),

    and

        log M_u(z) = sum_{r>=1} kappa_{2r} z^{2r}/(2r)!,
        kappa_{2r} = B_{2r}/(2r*(1-4^{-r})).
    """

    if order < 1:
        raise ValueError("order must be a positive integer")
    r = sp.Integer(order)
    return sp.Rational(sp.bernoulli(2 * r), 1) / (
        2 * r * (1 - sp.Rational(1, 4) ** r)
    )


def reciprocal_mgf_series(max_degree: int, scale: int = 1) -> sp.Expr:
    r"""Return the Taylor polynomial of 1/M_u(scale*z) through max_degree.

    The return value is an ordinary power series in z.  Therefore, if

        R(z) = sum_n r_n z^n,

    then R(D)P means sum_n r_n P^{(n)}.
    """

    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")
    log_series = sp.Integer(0)
    for r in range(1, max_degree // 2 + 1):
        kappa = rvachev_cumulant(r)
        log_series -= kappa * (sp.Integer(scale) * z) ** (2 * r) / sp.factorial(2 * r)
    return sp.series(sp.exp(log_series), z, 0, max_degree + 1).removeO().expand()


def h_operator_series(d: int, max_degree: int | None = None) -> sp.Expr:
    r"""Return the truncated fast-synthesis operator H_d(z).

        H_d(z) = (z/(2*sinh(z/2)))^d / M_u(z).

    Direct products are avoided.  The logarithm has the Bernoulli expansion

        log H_d(z) = -sum_{m>=1} B_{2m}/(2m(2m)!)
                         * (d + 1/(1-4^{-m})) z^{2m}.

    Only degrees that can act nontrivially on the input polynomial are needed.
    """

    if d < 0:
        raise ValueError("d must be nonnegative")
    if max_degree is None:
        max_degree = d
    if max_degree < 0:
        raise ValueError("max_degree must be nonnegative")

    log_series = sp.Integer(0)
    for m in range(1, max_degree // 2 + 1):
        bern = sp.bernoulli(2 * m)
        factor = sp.Integer(d) + 1 / (1 - sp.Rational(1, 4) ** m)
        log_series -= bern * factor * z ** (2 * m) / (
            2 * m * sp.factorial(2 * m)
        )
    return sp.series(sp.exp(log_series), z, 0, max_degree + 1).removeO().expand()


def apply_differential_operator(
    series: sp.Expr, poly: sp.Expr | sp.Poly, variable: sp.Symbol = t
) -> sp.Poly:
    """Apply the ordinary series series(D) to a polynomial exactly."""

    p = _as_poly(poly, variable)
    degree = max(0, p.degree())
    result = sp.Integer(0)
    series_poly = sp.Poly(series, z)
    for (power,), coeff in series_poly.terms():
        if power <= degree:
            result += coeff * sp.diff(p.as_expr(), variable, power)
    return sp.Poly(sp.expand(result), variable)


def deconvolution_polynomial(
    poly: sp.Expr | sp.Poly, d: int | None = None, variable: sp.Symbol = t
) -> sp.Poly:
    r"""Compute Q=M_u(MD)^{-1}P, M=2^d.

    The global cardinal identity is

        P(t) = (1/M) sum_{k in Z} Q(k) up((t-k)/M).

    If d is omitted, d=degree(P).  Any larger d is also valid.
    """

    p = _as_poly(poly, variable)
    degree = p.degree()
    if degree < 0:
        degree = 0
    if d is None:
        d = degree
    if d < degree:
        raise ValueError("d must be at least the polynomial degree")
    M = 2**d
    inv_series = reciprocal_mgf_series(degree, scale=M)
    return apply_differential_operator(inv_series, p, variable)


def annihilator_coefficients(d: int, truncate: int | None = None) -> List[int]:
    r"""Coefficients of the dyadic alias annihilator A_d.

        A_d(X) = product_{m=1}^d (1+X+...+X^{2^m-1})
               = product_{ell=1}^d (X^{2^{ell-1}}+1)^{d-ell+1}.

    If ``truncate`` is supplied, only coefficients through that degree are
    produced.  A sliding-window convolution makes the truncated computation
    O(d*truncate), independent of 2^d.
    """

    if d < 0:
        raise ValueError("d must be nonnegative")
    full_degree = 2 ** (d + 1) - d - 2
    nmax = full_degree if truncate is None else min(int(truncate), full_degree)
    coeffs = [1] + [0] * nmax

    # Multiply successively by a block of 2^m ones.  For each output index k,
    # the new coefficient is a sliding sum of old coefficients.
    current_degree = 0
    for m in range(1, d + 1):
        width = 2**m
        new_degree = min(nmax, current_degree + width - 1)
        new = [0] * (nmax + 1)
        window = 0
        for k in range(new_degree + 1):
            if k <= current_degree:
                window += coeffs[k]
            out_index = k - width
            if 0 <= out_index <= current_degree:
                window -= coeffs[out_index]
            new[k] = window
        coeffs = new
        current_degree = new_degree
    return coeffs[: nmax + 1]


def annihilator_mass(d: int) -> int:
    """A_d(1)=2^{d(d+1)/2}."""

    if d < 0:
        raise ValueError("d must be nonnegative")
    return 2 ** (d * (d + 1) // 2)


def dense_active_coefficients(
    poly: sp.Expr | sp.Poly,
    d: int | None = None,
    cells: int = 1,
    variable: sp.Symbol = t,
) -> Tuple[List[int], List[sp.Rational]]:
    """Return the naive active coefficients q_k/M on [0,cells].

    Active centers are k=-M+1,...,cells+M-1.  The output is exact but has
    exponentially many entries when d is large; it is intended for auditing
    and small examples, not as the primary algorithm.
    """

    p = _as_poly(poly, variable)
    degree = max(0, p.degree())
    if d is None:
        d = degree
    if d < degree:
        raise ValueError("d must be at least degree(P)")
    if cells < 1:
        raise ValueError("cells must be a positive integer")
    M = 2**d
    Q = deconvolution_polynomial(p, d, variable)
    centers = list(range(-M + 1, cells + M))
    coeffs = [sp.Rational(Q.eval(k), M) for k in centers]
    return centers, coeffs


def pair_compressed_coefficients(
    poly: sp.Expr | sp.Poly, d: int | None = None, variable: sp.Symbol = t
) -> SparseRepresentation:
    r"""Return the M+1-atom pair-compressed representation on [0,1].

    It uses up((t-k)/M), k=0,...,M.  This is often less cancellation-prone
    than the d+2-atom endpoint basis, though it is not support-minimal.
    """

    p = _as_poly(poly, variable)
    degree = max(0, p.degree())
    if d is None:
        d = degree
    if d < degree:
        raise ValueError("d must be at least degree(P)")
    M = 2**d
    Q = deconvolution_polynomial(p, d, variable)
    q = {k: sp.Rational(Q.eval(k), 1) for k in range(-M + 1, M + 1)}
    S = sum(q[k] for k in range(-M + 1, 1))
    A: List[sp.Rational] = [sp.Rational(0)] * (M + 1)
    A[0] = S
    for r in range(1, M):
        A[r] = q[r] - q[r - M]
    A[M] = S + q[M] - q[0]
    # A_k multiplies psi_{M,k}=(1/M)up((t-k)/M).
    coeffs = tuple(sp.Rational(a, M) for a in A)
    return SparseRepresentation(d, 1, M, tuple(range(M + 1)), coeffs)


def sparse_coefficients_fast(
    poly: sp.Expr | sp.Poly,
    d: int | None = None,
    cells: int = 1,
    variable: sp.Symbol = t,
) -> SparseRepresentation:
    r"""Output-sensitive exact synthesis using J+d+1 atoms.

    Let M=2^d, A_1=A_d(1), and

        G(t) = H_d(D)P(t),
        H_d(z)=(z/(2sinh(z/2)))^d/M_u(z).

    Put g_r=A_1*G(r-d/2).  If a_j=[X^j]A_d(X), solve

        g_r = sum_{s=0}^r a_{r-s} b_s

    by forward substitution.  Then

        P(t)=(1/M) sum_{r=0}^{J+d} b_r
             up((t-(M-d-1+r))/M),    0<=t<=J.

    The routine computes only the needed low coefficients a_0,...,a_{J+d}.
    """

    p = _as_poly(poly, variable)
    degree = max(0, p.degree())
    if d is None:
        d = degree
    if d < degree:
        raise ValueError("d must be at least degree(P)")
    if cells < 1:
        raise ValueError("cells must be a positive integer")

    M = 2**d
    output_degree = cells + d
    hseries = h_operator_series(d, degree)
    G = apply_differential_operator(hseries, p, variable)
    mass = sp.Integer(annihilator_mass(d))
    a = annihilator_coefficients(d, truncate=output_degree)
    if len(a) < output_degree + 1:
        a.extend([0] * (output_degree + 1 - len(a)))

    g: List[sp.Rational] = []
    for r in range(output_degree + 1):
        point = sp.Rational(2 * r - d, 2)
        g.append(sp.Rational(mass * G.eval(point)))

    b: List[sp.Rational] = []
    for r in range(output_degree + 1):
        value = g[r]
        for s in range(r):
            value -= sp.Integer(a[r - s]) * b[s]
        b.append(sp.factor(value))  # a_0=1, so no division is needed.

    centers = tuple(M - d - 1 + r for r in range(output_degree + 1))
    coefficients = tuple(sp.Rational(value, M) for value in b)
    return SparseRepresentation(d, cells, M, centers, coefficients)


def sparse_coefficients_recurrence(
    poly: sp.Expr | sp.Poly,
    d: int | None = None,
    cells: int = 1,
    variable: sp.Symbol = t,
) -> SparseRepresentation:
    r"""Reference implementation of the full cyclotomic recurrence.

    This constructs all coefficients of A_d and is exponentially larger than
    ``sparse_coefficients_fast``.  It is useful as an independent exact check.
    """

    p = _as_poly(poly, variable)
    degree = max(0, p.degree())
    if d is None:
        d = degree
    if d < degree:
        raise ValueError("d must be at least degree(P)")
    if cells < 1:
        raise ValueError("cells must be a positive integer")

    M = 2**d
    A = annihilator_coefficients(d)
    R = len(A) - 1
    K = -M + 1
    last = cells + M - 1
    Q = deconvolution_polynomial(p, d, variable)
    q = {k: sp.Rational(Q.eval(k)) for k in range(K, last + 1)}

    # The null sequence n matches q on the first R indices.  A_d(E)n=0 then
    # determines all subsequent values uniquely because A_d is monic.
    nseq = {k: q[k] for k in range(K, K + R)}
    for k in range(K, last - R + 1):
        nseq[k + R] = -sum(sp.Integer(A[j]) * nseq[k + j] for j in range(R))

    first_sparse = K + R
    centers = tuple(range(first_sparse, last + 1))
    b = [sp.factor(q[k] - nseq[k]) for k in centers]
    coefficients = tuple(sp.Rational(value, M) for value in b)
    return SparseRepresentation(d, cells, M, centers, coefficients)


def polynomiality_certificate(
    active_coefficients: Sequence[sp.Expr], d: int
) -> sp.Expr:
    r"""Evaluate the one-scalar polynomiality certificate Lambda_d.

    ``active_coefficients`` are coefficients q_k of psi_{M,k}, not of raw up,
    in center order k=-M+1,...,M.  Thus the represented function is

        sum q_k * psi_{M,k}(t),  psi=(1/M)up((t-k)/M).

    The synthesis is a polynomial on [0,1] iff this exact scalar is zero:

        Lambda_d(q) = [A_d(E) Delta^{d+1} q]_{-M+1}.
    """

    if d < 0:
        raise ValueError("d must be nonnegative")
    M = 2**d
    expected = 2 * M
    if len(active_coefficients) != expected:
        raise ValueError(f"expected {expected} active coefficients")
    A = annihilator_coefficients(d)
    m = d + 1
    q = [sp.sympify(v) for v in active_coefficients]
    total = sp.Integer(0)
    for ell, aell in enumerate(A):
        for r in range(m + 1):
            total += (
                sp.Integer(aell)
                * (-1) ** (m - r)
                * sp.binomial(m, r)
                * q[ell + r]
            )
    return sp.factor(total)



def thue_morse_sign(n: int) -> int:
    """Return epsilon_n=(-1)^{binary digit sum of n}."""

    if n < 0:
        raise ValueError("n must be nonnegative")
    return -1 if n.bit_count() % 2 else 1


def polynomiality_certificate_thue_morse(
    active_coefficients: Sequence[sp.Expr], d: int
) -> sp.Expr:
    r"""Equivalent O(2^d) Thue--Morse form of Lambda_d.

    The factorization

        A_d(X)(X-1)^{d+1}
          = (-1)^{d+1}(1-X) product_{m=1}^d(1-X^{2^m})

    and the finite Prouhet product

        product_{m=1}^d(1-X^{2^m})
          = sum_{r=0}^{2^d-1} epsilon_r X^{2r}

    give the compact certificate

        Lambda_d(q)=(-1)^{d+1} sum_r epsilon_r(q_{2r}-q_{2r+1}),

    where q_0,...,q_{2M-1} are the active coefficients in increasing-center
    order.  This formula makes the Thue--Morse bridge completely explicit.
    """

    if d < 0:
        raise ValueError("d must be nonnegative")
    M = 2**d
    if len(active_coefficients) != 2 * M:
        raise ValueError(f"expected {2*M} active coefficients")
    q = [sp.sympify(v) for v in active_coefficients]
    value = sum(
        thue_morse_sign(r) * (q[2 * r] - q[2 * r + 1]) for r in range(M)
    )
    return sp.factor((-1) ** (d + 1) * value)

def _reduce_single_atom_to_endpoint(center: int, d: int) -> List[sp.Rational]:
    """Coordinates of one active atom in the d+2 endpoint basis."""

    M = 2**d
    K = -M + 1
    last = M
    if not K <= center <= last:
        raise ValueError("center is not active on [0,1]")
    A = annihilator_coefficients(d)
    R = len(A) - 1
    q = {k: sp.Integer(1 if k == center else 0) for k in range(K, last + 1)}
    nseq = {k: q[k] for k in range(K, K + R)}
    for k in range(K, last - R + 1):
        nseq[k + R] = -sum(sp.Integer(A[j]) * nseq[k + j] for j in range(R))
    return [sp.factor(q[k] - nseq[k]) for k in range(K + R, last + 1)]


def central_basis_determinant(d: int) -> sp.Integer:
    r"""Determinant for the conjectural central basis {0,...,d+1}.

    Columns are reduced to the proved endpoint basis
    {M-d-1,...,M}.  A nonzero determinant proves the central block is also a
    basis for that particular d.  The normalization is integral and canonical
    for the recurrence used in the report.
    """

    if d < 0:
        raise ValueError("d must be nonnegative")
    cols = [_reduce_single_atom_to_endpoint(k, d) for k in range(d + 2)]
    matrix = sp.Matrix.hstack(*(sp.Matrix(col) for col in cols))
    return sp.factor(matrix.det())


def up_hat(xi: mp.mpf, factors: int = 80) -> mp.mpf:
    """Numerically evaluate the infinite sinc product for up_hat.

    The omitted tail is extremely close to one.  Near a sinc zero, mpmath's
    sin(x)/x formula is used directly; exact integer zeros are returned exactly.
    """

    xi = mp.mpf(xi)
    if xi == 0:
        return mp.mpf(1)
    # Exact nonzero integer inputs are zeros of the product.
    if xi == mp.floor(xi) and xi != 0:
        return mp.mpf(0)
    value = mp.mpf(1)
    for j in range(factors):
        y = mp.pi * xi / (2**j)
        value *= mp.sin(y) / y
    return value


def up_value(
    x: mp.mpf,
    cutoff: int = 80,
    factors: int = 80,
    dps: int = 80,
) -> mp.mpf:
    r"""Independent inverse-Fourier evaluation of up(x).

        up(x)=2 integral_0^infinity up_hat(xi) cos(2*pi*x*xi) dxi.

    The integral is split into unit lobes.  The product decays faster than any
    power, so a moderate cutoff is adequate for low-degree verification.
    This is not the fastest way to evaluate up; it is intentionally independent
    of the synthesis identities being tested.
    """

    x = mp.mpf(x)
    if abs(x) >= 1:
        return mp.mpf(0)
    old_dps = mp.mp.dps
    mp.mp.dps = dps
    try:
        integrand = lambda xi: up_hat(xi, factors) * mp.cos(2 * mp.pi * x * xi)
        total = mp.mpf(0)
        for n in range(cutoff):
            total += mp.quad(integrand, [n, n + 1])
        return 2 * total
    finally:
        mp.mp.dps = old_dps



def up_values_fourier_fast(
    xs: Sequence[float],
    cutoff: int = 80,
    nodes_per_lobe: int = 48,
    factors: int = 55,
) -> np.ndarray:
    r"""Vectorized double-precision inverse-Fourier evaluator.

    A fixed Gauss--Legendre rule is applied separately on every unit lobe of
    [0,cutoff].  All requested x-values are evaluated in one matrix product.
    This is several orders of magnitude faster than repeated adaptive
    quadrature and is accurate enough to expose cancellation in the sparse
    formulas through moderate degrees.
    """

    xarr = np.asarray(list(xs), dtype=float)
    result = np.zeros_like(xarr)
    inside = np.abs(xarr) < 1.0
    if not np.any(inside):
        return result

    base_nodes, base_weights = np.polynomial.legendre.leggauss(nodes_per_lobe)
    # Map the Gauss nodes from [-1,1] into every interval [n,n+1].
    lobes = np.arange(cutoff, dtype=float)[:, None]
    xi = (lobes + 0.5 * (base_nodes[None, :] + 1.0)).reshape(-1)
    weights = np.tile(0.5 * base_weights, cutoff)

    hat = np.ones_like(xi)
    for j in range(factors):
        # np.sinc(y)=sin(pi*y)/(pi*y), exactly our factor at y=xi/2^j.
        hat *= np.sinc(xi / (2.0**j))

    phase = 2.0 * np.pi * xarr[inside, None] * xi[None, :]
    result[inside] = 2.0 * (np.cos(phase) @ (weights * hat))
    return result


def verify_monomial_fast(
    d: int,
    grid_points: int = 17,
    cutoff: int = 80,
    nodes_per_lobe: int = 48,
) -> float:
    """Fast independent Fourier-grid verification of t^d on [0,1]."""

    rep = sparse_coefficients_fast(t**d, d=d)
    grid = np.linspace(0.0, 1.0, grid_points)
    args: List[float] = []
    for xval in grid:
        for center in rep.centers:
            args.append((xval - center) / rep.scale)
    values = up_values_fourier_fast(
        args, cutoff=cutoff, nodes_per_lobe=nodes_per_lobe
    ).reshape(grid_points, len(rep.centers))
    coeffs = np.array([float(c) for c in rep.coefficients])
    approx = values @ coeffs
    return float(np.max(np.abs(approx - grid**d)))

def evaluate_sparse(rep: SparseRepresentation, x: mp.mpf, **up_kwargs: object) -> mp.mpf:
    """Evaluate a sparse representation numerically."""

    total = mp.mpf(0)
    for center, coeff in rep.as_pairs():
        arg = (mp.mpf(x) - center) / rep.scale
        total += mp.mpf(str(sp.N(coeff, 80))) * up_value(arg, **up_kwargs)
    return total


def verify_monomial(
    d: int,
    grid_points: int = 17,
    dps: int = 80,
    cutoff: int = 80,
) -> mp.mpf:
    """Return max grid error for t^d on [0,1]."""

    rep = sparse_coefficients_fast(t**d, d=d)
    mp.mp.dps = dps
    max_error = mp.mpf(0)
    for j in range(grid_points):
        x = mp.mpf(j) / (grid_points - 1)
        approx = evaluate_sparse(rep, x, cutoff=cutoff, dps=dps)
        max_error = max(max_error, abs(approx - x**d))
    return max_error


def _format_rational(x: sp.Expr) -> str:
    return str(sp.factor(x))


def print_examples(max_degree: int = 4) -> None:
    """Print exact sparse monomial formulas and consistency checks."""

    print("Exact endpoint-basis formulas on 0 <= t <= 1")
    print("P(t) = sum c_k up((t-k)/M)\n")
    for d in range(max_degree + 1):
        rep_fast = sparse_coefficients_fast(t**d, d=d)
        rep_slow = sparse_coefficients_recurrence(t**d, d=d)
        assert rep_fast == rep_slow
        print(f"d={d}, M={rep_fast.scale}")
        for center, coeff in rep_fast.as_pairs():
            print(f"  k={center:>3}: c={_format_rational(coeff)}")
        print()


def print_custom(poly_text: str, d: int | None, cells: int) -> None:
    expr = sp.sympify(poly_text, locals={"t": t})
    poly = _as_poly(expr, t)
    if d is None:
        d = max(0, poly.degree())
    rep = sparse_coefficients_fast(poly, d=d, cells=cells)
    print(f"P(t) = {sp.expand(poly.as_expr())}")
    print(f"degree parameter d={d}, cells J={cells}, M={rep.scale}")
    print("Identity on 0 <= t <= J:")
    for center, coeff in rep.as_pairs():
        print(f"  {_format_rational(coeff)} * up((t-({center}))/{rep.scale})")


def run_internal_exact_checks(max_degree: int = 8) -> None:
    """Cross-check the fast and recurrence algorithms on several polynomials."""

    for d in range(max_degree + 1):
        test_polys = [t**d, sum((j + 1) * t**j for j in range(d + 1))]

        # Check the one-cell theorem and the multi-cell extension.  The full
        # recurrence is algorithmically independent of the compressed H_d
        # construction, so equality is a strong exact cross-check.
        for cells in (1, 2, 3):
            for p in test_polys:
                fast = sparse_coefficients_fast(p, d=d, cells=cells)
                slow = sparse_coefficients_recurrence(p, d=d, cells=cells)
                if fast != slow:
                    raise AssertionError(
                        f"fast/slow mismatch at d={d}, J={cells}, P={p}"
                    )

        # The dense deconvolution sequence must have zero certificate.
        M = 2**d
        Q = deconvolution_polynomial(test_polys[-1], d=d)
        q_active = [Q.eval(k) for k in range(-M + 1, M + 1)]
        cert = polynomiality_certificate(q_active, d)
        cert_tm = polynomiality_certificate_thue_morse(q_active, d)
        if cert_tm != cert:
            raise AssertionError(f"certificate forms disagree at d={d}")
        if cert != 0:
            raise AssertionError(f"nonzero polynomiality certificate at d={d}: {cert}")

        # The degree-(d+1) coefficient sequence has the stated normalization.
        q_next = [sp.Integer(k) ** (d + 1) for k in range(-M + 1, M + 1)]
        expected = sp.Integer(annihilator_mass(d)) * sp.factorial(d + 1)
        cert_next = polynomiality_certificate(q_next, d)
        cert_next_tm = polynomiality_certificate_thue_morse(q_next, d)
        if cert_next_tm != cert_next:
            raise AssertionError(f"degree-next certificate forms disagree at d={d}")
        if cert_next != expected:
            raise AssertionError(
                f"certificate normalization mismatch at d={d}: {cert_next} != {expected}"
            )



def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--examples", action="store_true", help="print monomial formulas d=0,...,4")
    parser.add_argument("--degree", type=int, default=None, help="degree parameter d")
    parser.add_argument("--poly", type=str, default=None, help="SymPy polynomial in t")
    parser.add_argument("--cells", type=int, default=1, help="number J of normalized cells")
    parser.add_argument(
        "--determinants",
        type=int,
        metavar="D",
        help="print central-basis determinants for d=0,...,D",
    )
    parser.add_argument(
        "--verify",
        type=int,
        metavar="D",
        help="numerically verify the monomial t^D",
    )
    parser.add_argument(
        "--self-test",
        type=int,
        metavar="D",
        help="run exact fast/slow checks through degree D",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_arg_parser().parse_args(argv)
    did_work = False

    if args.examples:
        print_examples(4)
        did_work = True

    if args.poly is not None:
        print_custom(args.poly, args.degree, args.cells)
        did_work = True

    if args.determinants is not None:
        for d in range(args.determinants + 1):
            print(d, central_basis_determinant(d))
        did_work = True

    if args.verify is not None:
        error = verify_monomial_fast(args.verify)
        print(f"d={args.verify}, maximum grid error = {mp.nstr(error, 12)}")
        did_work = True

    if args.self_test is not None:
        run_internal_exact_checks(args.self_test)
        print(f"All exact checks passed through d={args.self_test}.")
        did_work = True

    if not did_work:
        print_examples(4)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
