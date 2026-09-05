#!/usr/bin/env python3
r"""Exact checks for the consolidated volume *Recurrence-Free Dyadic Values of
the Fabius and Rvachev Functions* (dyadic-up-extraction subgroup).

Standard library only, Python 3.10+; every comparison is an exact equality of
``fractions.Fraction`` values.  The verifier merges the three retired
verification programs of the absorbed articles and adds checks for the
constants and identities that the consolidation itself introduced.

Every evaluator below is a finite expression.  Enumerating compositions or
multiplicity vectors is not a recurrence for a Fabius value or a moment; the
only recursive object, ``oracle_coefficients``, is isolated and is used solely
as an independent cross-check.

Run:  python verify_recurrence_free_dyadic_values.py [--max-depth 8] [--json OUT]
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod
from pathlib import Path


# ----------------------------------------------------------------------------
# elementary pieces
# ----------------------------------------------------------------------------

def T(n: int) -> int:
    """Triangular number n(n+1)/2."""
    return n * (n + 1) // 2


def eps(k: int) -> int:
    """Thue--Morse sign, directly from the binary digits."""
    if k < 0:
        raise ValueError("Thue--Morse index must be nonnegative")
    return -1 if k.bit_count() % 2 else 1


def pow2(k: int) -> Q:
    return Q(2 ** k) if k >= 0 else Q(1, 2 ** (-k))


def compositions(k: int):
    """All ordered compositions of k into positive parts, by cut masks."""
    if k < 0:
        raise ValueError("k must be nonnegative")
    if k == 0:
        yield ()
        return
    for mask in range(1 << (k - 1)):
        cuts = [0] + [j for j in range(1, k) if mask & (1 << (j - 1))] + [k]
        yield tuple(b - a for a, b in zip(cuts, cuts[1:]))


@lru_cache(None)
def profiles(k: int) -> tuple[tuple[int, ...], ...]:
    """Multiplicity vectors (v_1,...,v_k) with sum j v_j = k."""
    if k == 0:
        return ((),)
    return tuple(v for v in product(*(range(k // j + 1) for j in range(1, k + 1)))
                 if sum(j * vj for j, vj in enumerate(v, 1)) == k)


@lru_cache(None)
def bernoulli(n: int) -> Q:
    """Finite double sum, convention B_1 = -1/2."""
    return sum((Q(sum((-1) ** v * comb(j, v) * v ** n for v in range(j + 1)), j + 1)
                for j in range(n + 1)), Q(0))


# ----------------------------------------------------------------------------
# cumulant coefficients and moment coefficients
# ----------------------------------------------------------------------------

@lru_cache(None)
def lam(r: int, b: int = 2) -> Q:
    """lambda_{r,b}: [t^{2r}] log M_b(t); b = 2 is the Fabius case."""
    if r < 1:
        raise ValueError("r must be positive")
    return Q((b - 1) ** (2 * r) * 2 ** (2 * r - 1), r * factorial(2 * r) * (b ** (2 * r) - 1)) * bernoulli(2 * r)


@lru_cache(None)
def lam_bernoulli_free(r: int) -> Q:
    """lambda_r by the Bernoulli-free formula
    (4^r-1)^{-1} sum_l (-1)^{l-1}/l sum_{s_1+..+s_l=r} prod 1/(2 s_i+1)!."""
    total = Q(0)
    for c in compositions(r):
        l = len(c)
        total += Q((-1) ** (l - 1), l) * prod((Q(1, factorial(2 * s + 1)) for s in c), start=Q(1))
    return total / (4 ** r - 1)


@lru_cache(None)
def beta_raw(r: int) -> Q:
    """beta_r: [z^{2r}] of log M_X(z) - z/2, raw (uncentred) cumulants."""
    return Q(1, 2 * r * factorial(2 * r) * (4 ** r - 1)) * bernoulli(2 * r)


@lru_cache(None)
def a_comp(k: int) -> Q:
    """a_k = [t^{2k}] M(t) from positive ordered compositions."""
    total = Q(0)
    for c in compositions(k):
        suffix, term = k, Q(1)
        for r in c:
            term /= factorial(2 * r + 1) * (4 ** suffix - 1)
            suffix -= r
        total += term
    return total


@lru_cache(None)
def a_part(k: int, inverse: bool = False) -> Q:
    """a_k (or e_k = [t^{2k}] 1/M when inverse) from Bernoulli multiplicity sums."""
    sign = -1 if inverse else 1
    return sum((prod(((sign * lam(r)) ** v / factorial(v) for r, v in enumerate(pr, 1)), start=Q(1))
                for pr in profiles(k)), Q(0))


@lru_cache(None)
def e_geometric(k: int) -> Q:
    """e_k by the finite reciprocal expansion of 1/(1+(M-1))."""
    if k == 0:
        return Q(1)
    total = Q(0)
    for c in compositions(k):
        total += (-1) ** len(c) * prod((a_comp(r) for r in c), start=Q(1))
    return total


@lru_cache(None)
def A_raw_comp(m: int, b: int = 2) -> Q:
    """A_m^{(b)} = E X_b^m / m! from positive compositions (base b)."""
    total = Q(0)
    for c in compositions(m):
        suffix, term = m, Q((b - 1) ** m)
        for r in c:
            term /= factorial(r + 1) * (b ** suffix - 1)
            suffix -= r
        total += term
    return total


@lru_cache(None)
def A_raw_part(m: int) -> Q:
    """A_m = E X^m/m! from the raw multiplicity-profile formula."""
    total = Q(0)
    for k0 in range(m + 1):
        rest = m - k0
        if rest % 2:
            continue
        j = rest // 2
        for pr in profiles(j):
            total += Q(1, 2 ** k0 * factorial(k0)) * prod(
                (beta_raw(r) ** v / factorial(v) for r, v in enumerate(pr, 1)), start=Q(1))
    return total


def phi(degree: int, v) -> Q:
    """Phi_r(v) = [t^r] e^{vt} M(t), compositions for the coefficients."""
    if degree < 0:
        return Q(0)
    v = Q(v)
    return sum((a_comp(k) * v ** (degree - 2 * k) / factorial(degree - 2 * k)
                for k in range(degree // 2 + 1)), Q(0))


# ----------------------------------------------------------------------------
# value formulas on the dyadic grid
# ----------------------------------------------------------------------------

def check_grid(m: int, n: int):
    if n < 0 or not 0 <= m <= 2 ** n:
        raise ValueError("require n >= 0 and 0 <= m <= 2^n")


def power_sum(A: int, N: int) -> int:
    """S_N(A) = sum_{h<A} eps_h (2A-2h-1)^N."""
    return sum(eps(h) * (2 * A - 2 * h - 1) ** N for h in range(A))


def fabius_master(m: int, n: int, partition: bool = False) -> Q:
    """Master formula with centred coefficients a_k."""
    check_grid(m, n)
    coeff = a_part if partition else a_comp
    return sum((coeff(k) * Q(power_sum(m, n - 2 * k), factorial(n - 2 * k))
                for k in range(n // 2 + 1)), Q(0)) / 2 ** T(n)


def fabius_master_raw(m: int, n: int) -> Q:
    """Master formula in raw form: 2^{-C(n,2)} sum_h eps_h sum_l A_l (m-h-1)^{n-l}/(n-l)!."""
    check_grid(m, n)
    total = Q(0)
    for h in range(m):
        total += eps(h) * sum((A_raw_comp(l) * Q((m - h - 1) ** (n - l), factorial(n - l))
                               for l in range(n + 1)), Q(0))
    return total / 2 ** (n * (n - 1) // 2)


def fabius_global_binary(a: int, n: int) -> Q:
    """Signed global F_gl(a/2^n) for every a >= 0 by the binary block formula."""
    if a < 0 or n < 0:
        raise ValueError("need a, n >= 0")
    total = Q(0)
    for i in range(n + 1):
        if not (a >> i) & 1:
            continue
        eta = eps(a >> (i + 1))
        K = (1 << i) + 2 * (a % (1 << i))
        inner = sum((a_comp(k) * 4 ** (i * k) * Q(K ** (n - i - 2 * k), factorial(n - i - 2 * k))
                     for k in range((n - i) // 2 + 1)), Q(0))
        total += eta * 2 ** T(i) * inner
    return total / 2 ** T(n)


def fabius_binary(m: int, n: int) -> Q:
    """Bounded value by blocks: sum_{j in J(m)} eta_j 2^{-T_{n-j}} Phi_{n-j}(A_j)."""
    check_grid(m, n)
    total = Q(0)
    for j in range(m.bit_length()):
        if m & (1 << j):
            eta = eps(m >> (j + 1))
            r = m % (1 << j)
            A = 1 + Q(2 * r, 1 << j)
            total += eta * pow2(-T(n - j)) * phi(n - j, A)
    return total


def fabius_telescope(m: int, n: int) -> Q:
    """Binary telescope with raw coefficients: sum_i (-1)^{i-1} 2^{-C(b_i,2)} P_i(s_i)."""
    check_grid(m, n)
    if m == 0 or m == 2 ** n:
        return Q(m, 2 ** n)
    bits = [b for b in range(1, n + 1) if m & (1 << (n - b))]
    result = Q(0)
    for i, b in enumerate(bits):
        s = sum((Q(1, 2 ** v) for v in bits[i + 1:]), Q(0)) * 2 ** b
        poly = sum((A_raw_comp(b - k) * s ** k / factorial(k) for k in range(b + 1)), Q(0))
        result += (-1) ** i * poly / 2 ** (b * (b - 1) // 2)
    return result


def G(m: int, n: int, N: int) -> Q:
    """Centred prefix CDF G_N(m/2^n) = S_N(2^{N-n} m)/(2^{T_N} N!), N >= n >= 1."""
    check_grid(m, n)
    if N < max(n, 1):
        raise ValueError("need N >= max(n,1)")
    A = m << (N - n)
    return Q(power_sum(A, N), factorial(N) * 2 ** T(N))


def G_general(x: Q, N: int) -> Q:
    """G_N at any rational x, including knots."""
    if N < 1:
        raise ValueError("need N >= 1")
    x = Q(x)
    A = 2 ** (N + 1) * x - 1
    den, num = A.denominator, A.numerator
    B = sum(eps(h) * max(num - 2 * h * den, 0) ** N for h in range(2 ** N))
    return Q(B, den ** N * factorial(N) * 2 ** T(N))


def qpoch(q: Q, r: int) -> Q:
    return prod((1 - q ** j for j in range(1, r + 1)), start=Q(1))


def qbinom(d: int, j: int, q: Q) -> Q:
    return qpoch(q, d) / (qpoch(q, j) * qpoch(q, d - j))


def weight(d: int, j: int, q: Q = Q(1, 4)) -> Q:
    """w_{d,j}(q) = (-1)^{d-j} q^{T_{d-j}} / ((q;q)_j (q;q)_{d-j})."""
    if not 0 <= j <= d:
        raise ValueError("need 0 <= j <= d")
    return (-1) ** (d - j) * q ** T(d - j) / (qpoch(q, j) * qpoch(q, d - j))


def weight_product(d: int, j: int, q: Q) -> Q:
    return prod((Q(-q ** l, q ** j - q ** l) for l in range(d + 1) if l != j), start=Q(1))


def weight_integer(d: int, j: int) -> Q:
    """w_{d,j} at q = 1/4 in the integer-product form."""
    return Q((-1) ** (d - j) * 4 ** T(j),
             prod(4 ** r - 1 for r in range(1, j + 1)) * prod(4 ** r - 1 for r in range(1, d - j + 1)))


def fabius_quarter(m: int, n: int, R: int = 0) -> Q:
    """Quarter-base extraction from depths n+R, ..., n+R+d."""
    check_grid(m, n)
    if n == 0:
        return Q(m)
    d = n // 2
    return sum((weight(d, j) * G(m, n, n + R + j) for j in range(d + 1)), Q(0))


def fabius_arbitrary_depths(m: int, n: int, depths: list[int]) -> Q:
    check_grid(m, n)
    d = n // 2
    if len(depths) != d + 1 or len(set(depths)) != d + 1 or min(depths) < n:
        raise ValueError("need d+1 distinct depths >= n")
    z = [Q(1, 4 ** N) for N in depths]
    total = Q(0)
    for i, N in enumerate(depths):
        w = prod((z[l] / (z[l] - z[i]) for l in range(d + 1) if l != i), start=Q(1))
        total += w * G(m, n, N)
    return total


def fabius_derivative(m: int, n: int, r: int) -> Q:
    """F^{(r)}(m/2^n) by the differentiated master formula."""
    check_grid(m, n)
    if r < 0:
        raise ValueError("r must be nonnegative")
    if r > n:
        return Q(0)
    return pow2((n + 1) * r - T(n)) * sum((eps(h) * phi(n - r, 2 * m - 2 * h - 1) for h in range(m)), Q(0))


def global_value(x: Q) -> Q:
    """Signed global extension by the fold, for x >= 0."""
    x = Q(x)
    if x < 0:
        return Q(0)
    b = int(x // 2)
    t = x - 2 * b
    y = min(t, 2 - t)
    if y.denominator & (y.denominator - 1):
        raise ValueError("not dyadic")
    return eps(b) * fabius_master(y.numerator, y.denominator.bit_length() - 1)


def local_cell(m: int, n: int, N: int, h: Q) -> Q:
    """Exact shrinking-cell prediction for G_N(x+h), |h| <= 2^{-N-1}."""
    if N < n or n < 1 or abs(h) > pow2(-N - 1):
        raise ValueError("outside the exact local cell")
    return sum((a_part(k, inverse=True) * pow2(-2 * k * (N + 1)) * h ** j / factorial(j)
                * fabius_derivative(m, n, j + 2 * k)
                for k in range(n // 2 + 1) for j in range(n - 2 * k + 1)), Q(0))


def scale_polynomial(m: int, n: int) -> list[Q]:
    """Coefficients of Q_x(z) = sum_k e_k 4^{-k} F^{(2k)}(x) z^k."""
    return [a_part(k, inverse=True) * Q(1, 4 ** k) * fabius_derivative(m, n, 2 * k)
            for k in range(n // 2 + 1)]


# finite uniform prefixes -----------------------------------------------------

def a_prefix_multinomial(k: int, N: int) -> Q:
    """a_{k,N} = [t^{2k}] M_N(t) as a finite multinomial sum."""
    if N == 0:
        return Q(int(k == 0))
    total = Q(0)
    for rs in product(range(k + 1), repeat=N):
        if sum(rs) == k:
            total += prod((Q(1, 4 ** (i * r) * factorial(2 * r + 1)) for i, r in enumerate(rs, 1)), start=Q(1))
    return total


def a_prefix_power(k: int, N: int) -> Q:
    """a_{k,N} as one signed power sum."""
    if N == 0:
        return Q(int(k == 0))
    ex = 2 * k + N
    B = sum(eps(h) * (2 ** N - 1 - 2 * h) ** ex for h in range(2 ** N))
    return pow2(N * (N - 1) // 2 - N * ex) * Q(B, factorial(ex))


def a_recovered(k: int, N0: int = 0) -> Q:
    return sum((weight(k, j) * a_prefix_power(k, N0 + j) for j in range(k + 1)), Q(0))


def C_prefix(n: int, N: int, A) -> Q:
    """C_{n,N}(A) = E (A + Z_N)^n / n! as a finite multinomial sum."""
    A = Q(A)
    total = Q(0)
    for r0 in range(n + 1):
        rest = n - r0
        if rest % 2:
            continue
        k = rest // 2
        for rs in product(range(k + 1), repeat=N):
            if sum(rs) == k:
                total += A ** r0 / factorial(r0) * prod(
                    (Q(1, 4 ** (i * r) * factorial(2 * r + 1)) for i, r in enumerate(rs, 1)), start=Q(1))
    return total


def fabius_cube(m: int, n: int) -> Q:
    """Finite-cube formula: 2^{-T_n} sum_h eps_h sum_j w_{d,j} C_{n,j}(2m-2h-1)."""
    check_grid(m, n)
    d = n // 2
    total = Q(0)
    for h in range(m):
        total += eps(h) * sum((weight(d, j) * C_prefix(n, j, 2 * m - 2 * h - 1) for j in range(d + 1)), Q(0))
    return total / 2 ** T(n)


# determinant, denominators, rounding ------------------------------------------

def bareiss(mat) -> int:
    A = [list(r) for r in mat]
    n = len(A)
    if n == 0:
        return 1
    prev, sign = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = next((i for i in range(k + 1, n) if A[i][k]), None)
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        p = A[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                z = A[i][j] * p - A[i][k] * A[k][j]
                assert z % prev == 0
                A[i][j] = z // prev
            A[i][k] = 0
        prev = p
    return sign * A[-1][-1]


def bordered_matrix(m: int, n: int):
    d = n // 2
    t = [comb(n, 2 * j) * power_sum(m, n - 2 * j) for j in range(d + 1)]
    A = []
    for k in range(1, d + 1):
        A.append([(2 * k + 1) * (4 ** k - 1) if j == k else -comb(2 * k + 1, 2 * j) if j < k else 0
                  for j in range(1, d + 1)] + [1])
    A.append([-t[j] for j in range(1, d + 1)] + [t[0]])
    return A


def D(n: int) -> int:
    d = n // 2
    return 2 ** T(n) * factorial(n) * prod((2 * k + 1) * (4 ** k - 1) for k in range(1, d + 1))


def D_composition(n: int) -> int:
    d = n // 2
    return 2 ** T(n) * factorial(n + d) * prod(4 ** j - 1 for j in range(1, d + 1))


def fabius_determinant(m: int, n: int) -> Q:
    check_grid(m, n)
    return Q(bareiss(bordered_matrix(m, n)), D(n))


def fabius_rounded(m: int, n: int) -> Q:
    check_grid(m, n)
    if n == 0:
        return Q(m)
    Dn = D(n)
    N = max(n, Dn.bit_length() + 1)
    y = Dn * G(m, n, N) + Q(1, 2)
    return Q(y.numerator // y.denominator, Dn)


# half base with general shift -------------------------------------------------

def shifted_cdf(m: int, n: int, N: int, alpha: Q) -> Q:
    M = m * 2 ** (N - n)
    return sum((eps(k) * (Q(M - k) - alpha) ** N for k in range(M)), Q(0)) / (factorial(N) * 2 ** (N * (N - 1) // 2))


def fabius_half(m: int, n: int, alpha: Q = Q(1, 2)) -> Q:
    if n == 0:
        return Q(m)
    return sum((weight(n, j, Q(1, 2)) * shifted_cdf(m, n, n + j, alpha) for j in range(n + 1)), Q(0))


def fabius_half_closed(m: int, n: int, alpha: Q) -> Q:
    """The displayed half-base closed form with shift alpha."""
    if n == 0:
        return Q(m)
    q = Q(1, 2)
    total = Q(0)
    for j in range(n + 1):
        inner = sum((eps(k) * (k - 2 ** j * m + alpha) ** (n + j) for k in range(2 ** j * m)), Q(0))
        total += qbinom(n, j, q) / (2 ** (j * (j - 1)) * factorial(n + j)) * inner
    return total / (2 ** (n * n) * qpoch(q, n))


# Rvachev values -------------------------------------------------------------

def up_value(x: Q) -> Q:
    x = Q(x)
    if abs(x) >= 1:
        return Q(0)
    y = 1 - abs(x)
    return fabius_master(y.numerator, y.denominator.bit_length() - 1)


def u_density(a: int, n: int, N: int) -> Q:
    """u_N(a/2^n), density of Z_N; N > n >= 0, |a| < 2^n."""
    if not N > n >= 0:
        raise ValueError("need N > n >= 0")
    if abs(a) >= 2 ** n:
        return Q(0)
    A = 2 ** N + a * 2 ** (N - n)
    return Q(sum(eps(k) * (A - 1 - 2 * k) ** (N - 1) for k in range(A // 2)),
             factorial(N - 1) * 2 ** (N * (N - 1) // 2))


def u_density_general(x: Q, N: int) -> Q:
    if N < 2:
        raise ValueError("need N >= 2")
    x = Q(x)
    A = 2 ** N * (x + 1) - 1
    den, num = A.denominator, A.numerator
    B = sum(eps(h) * max(num - 2 * h * den, 0) ** (N - 1) for h in range(2 ** N))
    return Q(B, den ** (N - 1) * factorial(N - 1) * 2 ** (N * (N - 1) // 2))


def up_quarter(a: int, n: int, R: int = 0) -> Q:
    d = n // 2
    return sum((weight(d, j) * u_density(a, n, n + 1 + R + j) for j in range(d + 1)), Q(0))


def up_derivative(a: int, n: int, r: int) -> Q:
    """up^{(r)}(a/2^n) = 2^{T_r} F_gl(2^r (x+1)), |a| < 2^n."""
    x = Q(a, 2 ** n)
    if abs(x) >= 1:
        return Q(0)
    return 2 ** T(r) * global_value(2 ** r * (x + 1))


# integer bases --------------------------------------------------------------

def base_cdf(b: int, m: int, n: int, N: int) -> Q:
    """Centred base-b prefix CDF G_{b,N}(m/b^n) by the Boolean cube sum."""
    M = m * b ** (N - n)
    num = 0
    for bits in product((0, 1), repeat=N):
        v = 2 * M - 1 - 2 * (b - 1) * sum(bit * b ** j for j, bit in enumerate(bits))
        if v > 0:
            num += (-1) ** sum(bits) * v ** N
    return Q(num, 2 ** N * (b - 1) ** N * b ** (N * (N - 1) // 2) * factorial(N))


def base_cdf_general(b: int, x: Q, N: int) -> Q:
    x = Q(x)
    total = Q(0)
    for mask in range(2 ** N):
        shift = sum((Q(b - 1, b ** j) for j in range(1, N + 1) if mask & (1 << (j - 1))), Q(0))
        t = max(x - Q(1, 2 * b ** N) - shift, Q(0))
        total += eps(mask) * t ** N
    return total * Q(b ** T(N), (b - 1) ** N * factorial(N))


def base_arithmetic(b: int, m: int, n: int) -> Q:
    """F_b(m/b^n) by the finite base-b master formula with raw coefficients."""
    if n == 0:
        return Q(m)
    total = Q(0)
    for bits in product((0, 1), repeat=n):
        delta = m - (b - 1) * sum(v * b ** j for j, v in enumerate(bits))
        if delta >= 1:
            total += (-1) ** sum(bits) * sum(
                (A_raw_comp(l, b) * Q((delta - 1) ** (n - l), factorial(n - l)) for l in range(n + 1)), Q(0))
    return total / ((b - 1) ** n * b ** (n * (n - 1) // 2))


def base_quarter(b: int, m: int, n: int, R: int = 0) -> Q:
    if n == 0:
        return Q(m)
    d = n // 2
    return sum((weight(d, j, Q(1, b * b)) * base_cdf(b, m, n, n + R + j) for j in range(d + 1)), Q(0))


# the isolated oracle ------------------------------------------------------------

def oracle_coefficients(kmax: int) -> list[Q]:
    """Triangular moment recurrence: independent check ONLY."""
    out = [Q(1)]
    for k in range(1, kmax + 1):
        out.append(sum((out[j] / factorial(2 * (k - j) + 1) for j in range(k)), Q(0)) / (4 ** k - 1))
    return out


# ----------------------------------------------------------------------------
# the checks
# ----------------------------------------------------------------------------

def verify(max_depth: int = 8) -> dict:
    if not 1 <= max_depth <= 11:
        raise ValueError("choose 1 <= max-depth <= 11")
    c: dict = {}

    # coefficients ---------------------------------------------------------
    oracle = oracle_coefficients(12)
    for k in range(13):
        assert a_comp(k) == a_part(k) == oracle[k]
    for k in range(9):
        assert a_recovered(k) == a_recovered(k, 2) == oracle[k]
        assert a_prefix_multinomial(k, min(k, 4)) == a_prefix_power(k, min(k, 4))
        assert e_geometric(k) == a_part(k, inverse=True)
        assert (-1) ** k * a_part(k, inverse=True) > 0
        assert sum((a_part(j) * a_part(k - j, inverse=True) for j in range(k + 1)), Q(0)) == int(k == 0)
    for r in range(1, 9):
        assert lam(r) == lam_bernoulli_free(r)
        assert lam(r) == 4 ** r * beta_raw(r)
    for m in range(9):
        assert A_raw_comp(m) == A_raw_part(m)
        # raw versus centred: A_m = [z^m] e^{z/2} M(z/2)
        assert A_raw_comp(m) == sum((Q(1, 2 ** m) * a_comp(k) / factorial(m - 2 * k)
                                     for k in range(m // 2 + 1)), Q(0))
    c["coefficient_checks"] = 13 + 9 + 8 + 9

    printed = {
        "a": ["1", "1/18", "19/16200", "583/42865200", "132809/1311675120000"],
        "c": ["1", "1/9", "19/675", "583/59535", "132809/32531625"],
        "lambda": ["1/18", "-1/2700", "1/178605", "-1/9639000", "1/478533825"],
        "e": ["1", "-1/18", "31/16200", "-2347/42865200", "1904369/1311675120000"],
        "beta_raw": ["1/72", "-1/43200", "1/11430720", "-1/2467584000"],
    }
    assert [str(a_comp(k)) for k in range(5)] == printed["a"]
    assert [str(a_comp(k) * factorial(2 * k)) for k in range(5)] == printed["c"]
    assert [str(lam(r)) for r in range(1, 6)] == printed["lambda"]
    assert [str(a_part(k, inverse=True)) for k in range(5)] == printed["e"]
    assert [str(beta_raw(r)) for r in range(1, 5)] == printed["beta_raw"]
    assert a_prefix_power(1, 1) == Q(1, 24) and Q(4, 3) * a_prefix_power(1, 1) == Q(1, 18)
    assert [str(A_raw_comp(m)) for m in range(1, 6)] == ["1/2", "5/36", "1/36", "143/32400", "19/32400"]

    # weights ---------------------------------------------------------------
    rows = {0: ["1"], 1: ["-1/3", "4/3"], 2: ["1/45", "-4/9", "64/45"],
            3: ["-1/2835", "4/135", "-64/135", "4096/2835"]}
    for d, row in rows.items():
        assert [str(weight(d, j)) for j in range(d + 1)] == row
    for d in range(9):
        for j in range(d + 1):
            assert weight(d, j) == weight_integer(d, j) == weight_product(d, j, Q(1, 4))
            assert weight(d, j) == (-1) ** (d - j) * Q(1, 4) ** T(d - j) / qpoch(Q(1, 4), d) * qbinom(d, j, Q(1, 4))
        for r in range(d + 1):
            assert sum((weight(d, j) * Q(1, 4) ** (j * r) for j in range(d + 1)), Q(0)) == int(r == 0)
        for q in (Q(1, 4), Q(1, 2), Q(1, 9)):
            assert sum((abs(weight(d, j, q)) for j in range(d + 1)), Q(0)) == prod(((1 + q ** r) / (1 - q ** r) for r in range(1, d + 1)), start=Q(1))
            # generating polynomial: sum_j w_{d,j} v^j = prod_r (v - q^r)/(1 - q^r)
            for v in (Q(2), Q(-1), Q(3, 7)):
                assert sum((weight(d, j, q) * v ** j for j in range(d + 1)), Q(0)) == prod(((v - q ** r) / (1 - q ** r) for r in range(1, d + 1)), start=Q(1))
    assert sum((abs(weight(6, j)) for j in range(7)), Q(0)) < 2
    c["weight_rows_checked"] = 9

    # grid: every formula family agrees ------------------------------------
    count = 0
    for n in range(max_depth + 1):
        Dn = D(n)
        Dc = D_composition(n)
        for m in range(2 ** n + 1):
            v = fabius_master(m, n)
            assert v == fabius_master(m, n, True) == fabius_master_raw(m, n)
            assert v == fabius_binary(m, n) == fabius_global_binary(m, n) == fabius_telescope(m, n)
            assert v == fabius_quarter(m, n) == fabius_determinant(m, n)
            if n <= 6:
                assert v == fabius_cube(m, n)
            assert v + fabius_master(2 ** n - m, n) == 1
            assert fabius_master(2 * m, n + 1) == v
            assert (Dn * v).denominator == 1 and (Dc * v).denominator == 1
            count += 1
        if n >= 1:
            for m in sorted({0, 1, (2 ** n) // 3, (2 ** n) // 2, 2 ** n - 1, 2 ** n}):
                for R in (1, 2):
                    assert fabius_quarter(m, n, R) == fabius_binary(m, n)
                d = n // 2
                assert fabius_arbitrary_depths(m, n, [n + 2 * j for j in range(d + 1)]) == fabius_binary(m, n)
                assert fabius_arbitrary_depths(m, n, [n + 3 + j for j in range(d + 1)]) == fabius_binary(m, n)
    c["grid_representations"] = count

    # signed extension beyond the unit interval -------------------------------
    count = 0
    for n in range(7):
        for a in range(3 * 2 ** n + 1):
            assert fabius_global_binary(a, n) == global_value(Q(a, 2 ** n))
            count += 1
    for b in range(6):
        assert global_value(Q(2 * b)) == 0 and global_value(Q(2 * b + 1)) == eps(b)
        # odd m: F_gl(m/2) = eps_{floor(m/4)}/2, here m = 2b+1
        assert global_value(Q(2 * b + 1, 2)) == Q(eps(b // 2), 2)
    c["global_extension_cases"] = count

    # exact local cell, scale polynomial, exact degree -------------------------
    count = 0
    for n in range(1, min(5, max_depth) + 1):
        for m in range(2 ** n + 1):
            for N in (n, n + 1, n + 2):
                for sh in (Q(-1), Q(-1, 2), Q(0), Q(1, 2), Q(1)):
                    h = sh * pow2(-N - 1)
                    assert G_general(Q(m, 2 ** n) + h, N) == local_cell(m, n, N, h)
                    count += 1
    for n in range(1, 7):
        for m in range(2 ** n + 1):
            poly = scale_polynomial(m, n)
            for N in (n, n + 1, n + 3):
                assert G(m, n, N) == sum((cf * Q(1, 4 ** (k * N)) for k, cf in enumerate(poly)), Q(0))
            if m % 2 == 1 and 0 < m < 2 ** n:
                assert poly[-1] != 0
    assert scale_polynomial(1, 2) == [Q(5, 72), Q(-1, 9)]
    assert scale_polynomial(1, 3) == [Q(1, 288), Q(-1, 18)]
    assert scale_polynomial(1, 4) == [Q(143, 2073600), Q(-5, 648), Q(248, 2025)]
    assert scale_polynomial(3, 4) == [Q(46657, 2073600), Q(-67, 648), Q(-248, 2025)]
    assert fabius_derivative(1, 2, 1) == 1 and fabius_derivative(1, 2, 2) == 8
    for r in range(3, 6):
        assert fabius_derivative(1, 2, r) == 0
    c["local_cell_cases"] = count

    # derivative formula against the dilation law --------------------------------
    count = 0
    for n in range(1, 6):
        for m in range(1, 2 ** n):
            for r in range(0, n + 2):
                pred = 2 ** T(r) * global_value(Q(m * 2 ** r, 2 ** n)) if r <= n else Q(0)
                assert fabius_derivative(m, n, r) == pred
                count += 1
    c["derivative_cases"] = count

    # rounding -------------------------------------------------------------------
    for n in range(1, 4):
        for m in range(2 ** n + 1):
            assert fabius_rounded(m, n) == fabius_binary(m, n)
    c["rounding_cases"] = sum(2 ** n + 1 for n in range(1, 4))

    # half base and general shift ------------------------------------------------
    count = 0
    for n in range(1, 6):
        for m in sorted({1, 2 ** n // 2, 2 ** n - 1}):
            for alpha in (Q(0), Q(1, 2), Q(1), Q(-2), Q(2, 3)):
                assert fabius_half(m, n, alpha) == fabius_master(m, n) == fabius_half_closed(m, n, alpha)
                count += 1
    c["half_base_shift_cases"] = count

    # Rvachev values, direct density extraction, derivatives ----------------------
    count = 0
    for n in range(6):
        for a in range(-2 ** n, 2 ** n + 1):
            x = Q(a, 2 ** n)
            assert up_quarter(a, n) == up_value(x) == up_quarter(a, n, 1)
            if abs(a) < 2 ** n and n >= 1:
                N = n + 1
                assert u_density(a, n, N) == G(2 ** n - abs(a), n, N - 1)
                if N >= 2:
                    assert u_density_general(x, N) == u_density(a, n, N)
            count += 1
    assert u_density(1, 2, 3) == Q(15, 16) and u_density(1, 2, 4) == Q(179, 192)
    assert up_value(Q(1, 4)) == Q(67, 72) and up_derivative(1, 2, 2) == -8
    for N in range(3, 8):
        assert u_density(1, 2, N) == Q(67, 72) + Q(4, 9) * Q(1, 4 ** N)
    # up^{(2j)} at a dyadic point enters the density law u_N = sum e_j 4^{-Nj} up^{(2j)}
    for n in range(1, 5):
        for a in range(-2 ** n + 1, 2 ** n):
            for N in (n + 1, n + 3):
                pred = sum((a_part(j, inverse=True) * Q(1, 4 ** (N * j)) * up_derivative(a, n, 2 * j)
                            for j in range(n // 2 + 1)), Q(0))
                assert u_density(a, n, N) == pred
    c["rvachev_cases"] = count

    # odd depth and reciprocal powers -----------------------------------------------
    for j in range(0, 5):
        n = 2 * j + 1
        assert fabius_master(1, n) == a_comp(j) * factorial(2 * j) / (2 * factorial(2 * j) * 2 ** (n * (n - 1) // 2))
    for n in range(0, 9):
        assert fabius_master(1, n) == A_raw_comp(n) / 2 ** (n * (n - 1) // 2)
    known = ["1", "1/2", "5/72", "1/288", "143/2073600", "19/33177600",
             "1153/561842749440", "583/179789679820800"]
    assert [str(fabius_master(1, n)) for n in range(8)] == known

    # integer bases -------------------------------------------------------------
    count = 0
    for b in (2, 3, 4, 5):
        for n in range(1, 4 if b <= 3 else 3):
            for m in range(b ** n + 1):
                v = base_quarter(b, m, n)
                assert v == base_arithmetic(b, m, n) == base_quarter(b, m, n, 1)
                assert v + base_quarter(b, b ** n - m, n) == 1
                if b == 2:
                    assert v == fabius_binary(m, n)
                count += 1
        for N in (1, 2):
            for m in range(b ** N + 1):
                assert base_cdf(b, m, N, N) == base_cdf_general(b, Q(m, b ** N), N)
    assert base_arithmetic(3, 1, 2) == Q(7, 576) and base_arithmetic(3, 1, 3) == Q(1, 6912)
    assert base_arithmetic(4, 1, 2) == Q(1, 240) and base_arithmetic(4, 1, 3) == Q(1, 51840)
    c["integer_base_cases"] = count

    # printed examples -----------------------------------------------------------
    examples = {
        "F(1/4)": "5/72", "F(3/8)": "73/288", "F(1/16)": "143/2073600",
        "F(3/16)": "46657/2073600", "F(5/16)": "305857/2073600", "F(7/16)": "777743/2073600",
        "F(1/32)": "19/33177600", "F(13/32)": "10393219/33177600",
        "F(21/64)": "482385079229/2809213747200",
        "F(37/128)": "4121049919811/35957935964160",
        "F(173/4096)": "1490588447599319294372326859976672988757/292214732887898713986916575925267070976000000",
        "F(1/1024)": "134926369/1246394851358539387238350848000",
    }
    for key, val in examples.items():
        num, den = key[2:-1].split("/")
        assert str(fabius_binary(int(num), int(den).bit_length() - 1)) == val, key
    assert G(1, 2, 2) == Q(1, 16) and G(1, 2, 3) == Q(13, 192)
    assert G(3, 3, 3) == Q(97, 384) and G(3, 3, 4) == Q(389, 1536)
    assert (G(1, 4, 4), G(1, 4, 5), G(1, 4, 6)) == (Q(1, 24576), Q(121, 1966080), Q(6331, 94371840))
    assert (G(5, 4, 4), G(5, 4, 5), G(5, 4, 6)) == (Q(1205, 8192), Q(289799, 1966080), Q(13917509, 94371840))
    assert Q(1, 45) * G(5, 4, 4) - Q(4, 9) * G(5, 4, 5) + Q(64, 45) * G(5, 4, 6) == Q(305857, 2073600)
    assert (G(1, 3, 3), G(1, 3, 4)) == (Q(1, 384), Q(5, 1536))
    # the three binary blocks of 21/64
    blocks = [pow2(-3) * phi(2, Q(13, 8)), -pow2(-10) * phi(4, Q(3, 2)), pow2(-21) * phi(6, 1)]
    assert [str(x) for x in blocks] == ["1585/9216", "-71179/265420800", "1153/561842749440"]
    assert sum(blocks, Q(0)) == Q(482385079229, 2809213747200)
    # telescope example 3/8 = 2^-2 + 2^-3
    assert Q(1, 2) * (A_raw_comp(2) + Q(1, 2) * A_raw_comp(1) + Q(1, 8)) - Q(1, 8) * A_raw_comp(3) == Q(73, 288)
    # determinant example n = 2, m = 1
    assert bordered_matrix(1, 2) == [[9, 1], [-1, 1]] and bareiss(bordered_matrix(1, 2)) == 10
    assert D(2) == 8 * 2 * 9
    # denominators
    assert [D(n) for n in range(6)] == [1, 2, 144, 3456, 16588800, 2654208000]

    c["status"] = "PASS"
    c["max_exhaustive_depth"] = max_depth
    c["arithmetic"] = "fractions.Fraction and Python integers; no floating point"
    c["printed_constants"] = printed
    c["examples"] = examples
    c["weight_norm_limits_float"] = {
        "q=1/4": float(prod(((1 + Q(1, 4) ** r) / (1 - Q(1, 4) ** r) for r in range(1, 40)), start=Q(1))),
        "q=1/2": float(prod(((1 + Q(1, 2) ** r) / (1 - Q(1, 2) ** r) for r in range(1, 80)), start=Q(1))),
    }
    return c


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-depth", type=int, default=8)
    ap.add_argument("--json", type=Path, help="optionally save the report")
    args = ap.parse_args()
    report = verify(args.max_depth)
    text = json.dumps(report, indent=2)
    print(text)
    if args.json:
        args.json.write_text(text + "\n", encoding="utf-8")
