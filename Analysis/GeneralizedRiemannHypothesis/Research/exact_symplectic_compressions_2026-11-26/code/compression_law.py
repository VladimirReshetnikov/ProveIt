"""Exact symplectic compression probabilities from finite-dimensional invariants.

All counting and probability functions use integers or fractions.Fraction.
The parameter q must be a prime power. These formulas require no field arithmetic.
For a matrix-based independent verifier, see verify_exhaustive.py.
"""

from fractions import Fraction
from functools import lru_cache
from math import prod


@lru_cache(None)
def gaussian(q, n, k):
    """Gaussian binomial coefficient; zero outside its natural range."""
    if n < 0 or k < 0 or k > n:
        return 0
    k = min(k, n - k)
    numerator = prod(q ** (n - i) - 1 for i in range(k))
    denominator = prod(q ** (k - i) - 1 for i in range(k))
    assert numerator % denominator == 0
    return numerator // denominator


@lru_cache(None)
def gl_order(q, j):
    return prod(q**j - q**i for i in range(j))


@lru_cache(None)
def embedding_count(q, N, k, s):
    """Injective maps of a prescribed rank-2s alternating k-space into 2N."""
    if min(N, k, s) < 0 or 2 * s > k or k - s > N:
        return 0
    pairs = prod((q ** (2 * N - 2 * i) - 1) * q ** (2 * N - 2 * i - 1)
                 for i in range(s))
    radical = prod(q ** (2 * (N - s) - i) - q**i
                   for i in range(k - 2 * s))
    return pairs * radical


@lru_cache(None)
def transverse_kernels(q, r, u, v, d):
    """d-subspaces of an r-space disjoint from fixed disjoint u/v-subspaces."""
    c = r - u - v
    if min(r, u, v, c, d) < 0 or d > r - max(u, v):
        return 0
    return sum(gaussian(q, u, j) * gaussian(q, v, j) * gl_order(q, j)
               * gaussian(q, c, d - j) * q ** ((d - j) * (u + v - j))
               for j in range(max(0, d - c), min(u, v, d) + 1))


def probability(q, N, a, b, f, h, s, u, v):
    """Probability of a specified matrix, given its joint-Gram invariants.

    rank(F)=2f, rank(H)=2h, rank(G_M)=2s; u/v are coordinate radical
    intersection dimensions. Only tuples arising from actual matrices are valid.
    """
    denominator = embedding_count(q, N, a, f) * embedding_count(q, N, b, h)
    if not denominator:
        raise ValueError('The prescribed source/target forms do not embed.')
    r = a + b - 2 * s
    numerator = sum(transverse_kernels(q, r, u, v, d)
                    * embedding_count(q, N, a + b - d, s)
                    for d in range(r - max(u, v) + 1))
    return Fraction(numerator, denominator)


def likelihood(q, N, a, b, f, h, s, u, v):
    return q ** (a * b) * probability(q, N, a, b, f, h, s, u, v)


def support(N, s, u, v):
    return s + max(u, v) <= N


def intersection_law(q, N, a, b, s, u, v):
    """Conditional law of the subspace intersection dimension, given a matrix."""
    r = a + b - 2 * s
    weights = {d: transverse_kernels(q, r, u, v, d)
               * embedding_count(q, N, a + b - d, s)
               for d in range(r - max(u, v) + 1)}
    total = sum(weights.values())
    if not total:
        raise ValueError('The conditioning matrix has probability zero.')
    return {d: Fraction(w, total) for d, w in weights.items() if w}


def first_correction(q, a, b, f, h, s, u, v):
    k = a + b
    if k == 0:
        return 0
    r = k - 2 * s
    S = lambda ell: (q ** (2 * ell) - 1) // (q * q - 1)
    lines = (q**r - q**u - q**v + 1) // (q - 1)
    return S(a - f) + S(b - h) - S(k - s) + q ** (k - 1) * lines


@lru_cache(None)
def even_product(q, h):
    return prod((1 - Fraction(1, q ** (2 * j)) for j in range(1, h + 1)),
                start=Fraction(1))


@lru_cache(None)
def odd_product(q, h):
    return prod((1 - Fraction(1, q ** (2 * j - 1)) for j in range(1, h + 1)),
                start=Fraction(1))


def boundary_normalizer(q, a, b):
    if a <= 0 or b <= 0 or a % 2 or b % 2:
        raise ValueError('a,b must be positive even integers.')
    return prod((1 - Fraction(1, q ** (2 * j))
                 for j in range(a // 2 + 1, (a + b) // 2 + 1)),
                start=Fraction(1))


def balanced_likelihood(q, a, b, ell):
    """Both forms nonsingular, ambient a+b, residual corank 2*ell."""
    if not 0 <= ell <= b // 2:
        raise ValueError('Invalid residual corank.')
    terms = sum(Fraction(gaussian(q, 2 * ell, d), q ** (d * (d + 1) // 2))
                / even_product(q, d - ell)
                for d in range(ell, 2 * ell + 1))
    return even_product(q, b // 2) * terms / boundary_normalizer(q, a, b)


def delta_interval(q, L=100):
    """Rigorous rational enclosure of O_infinity*(1-B_infinity)."""
    B = even_product(q, L)
    O = odd_product(q, L)
    even_tail_sum = Fraction(1, q ** (2 * L) * (q * q - 1))
    odd_tail_sum = Fraction(q, q ** (2 * L) * (q * q - 1))
    B_lower = B * (1 - even_tail_sum)
    O_lower = O * (1 - odd_tail_sum)
    return O_lower * (1 - B), O * (1 - B_lower)


def gram_tv_square_bound(q, a, b, L=100):
    """Rational upper bound for TV(Gram(iid a by b),uniform Alt_b)^2.

    Uses the rank count bound with B_infinity, and a rigorous lower bound
    for that product. Requires even a and a>=b.
    """
    if a % 2 or a < b:
        raise ValueError('Require even a and a>=b.')
    B_lower = even_product(q, L) * (1 - Fraction(1, q ** (2 * L) * (q*q - 1)))
    d = a - b
    series_bound = Fraction(1, q ** (2*d + 3)) / (1 - Fraction(1, q ** (2*d + 7)))
    return series_bound / (4 * B_lower)


def rank_tv_bound(q, a, b):
    lines = Fraction(q**b - 1, q - 1)
    return lines * (Fraction(1, q**a) + Fraction(q**b - 1, q ** (a+b) - 1))


if __name__ == '__main__':
    # Example: F=H=J_1 over F_3 in ambient dimension four.
    print('Residual nonsingular likelihood:', balanced_likelihood(3, 2, 2, 0))
    print('Residual singular likelihood:   ', balanced_likelihood(3, 2, 2, 1))
    print('Exact total variation:          ', Fraction(19, 270))
