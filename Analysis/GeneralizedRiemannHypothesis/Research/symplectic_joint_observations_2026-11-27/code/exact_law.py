#!/usr/bin/env python3
"""Exact symplectic cross-Gram laws and certified total-variation bounds.

Counting formulas accept any prime power q. Matrix rank routines accept prime
fields only; extension-field arithmetic is deliberately not emulated modulo q.
All reported probabilities and bounds are fractions, not simulations.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import prod


def qpower(q: int, exponent: int) -> Fraction:
    return Fraction(q ** exponent) if exponent >= 0 else Fraction(1, q ** -exponent)


@lru_cache(maxsize=None)
def gaussian(q: int, n: int, k: int) -> int:
    """Gaussian binomial coefficient, extended by zero outside 0 <= k <= n."""
    if n < 0 or k < 0 or k > n:
        return 0
    if k == 0 or k == n:
        return 1
    k = min(k, n-k)
    return gaussian(q, n-1, k) + q**(n-k)*gaussian(q, n-1, k-1)


@lru_cache(maxsize=None)
def symplectic_order(q: int, n: int) -> int:
    if n < 0:
        return 0
    return q**(n*n) * prod(q**(2*j)-1 for j in range(1, n+1))


@lru_cache(maxsize=None)
def embeddings(q: int, n: int, dimension: int, half_rank: int) -> int:
    """Number of isometric injections of one fixed alternating formed space."""
    a, s = dimension, half_rank
    if min(n, a, s) < 0 or 2*s > a or a-s > n:
        return 0
    # Cancel the symplectic-order ratio first: only s factors remain.
    pairs = q**(s*(2*n-s)) * prod(q**(2*j)-1 for j in range(n-s+1, n+1))
    radical = prod(q**(2*(n-s)-i)-q**i for i in range(a-2*s))
    return pairs * radical


@lru_cache(maxsize=None)
def avoiding_kernel_counts(q: int, r: int, intersections: tuple[int, ...]) -> tuple[int, ...]:
    """All kernel counts using a q-binomial product and O(r^2) arithmetic operations."""
    if min((r, *intersections), default=0) < 0 or sum(intersections) > r:
        raise ValueError('Invalid radical intersection dimensions')
    coeffs = [1]
    for t in intersections:
        for h in range(t):
            new = coeffs+[0]
            for j, coefficient in enumerate(coeffs):
                new[j+1] -= q**h * coefficient
            coeffs = new
    return tuple(sum(coeffs[j]*gaussian(q, r-j, ell-j)
                     for j in range(min(ell, len(coeffs)-1)+1))
                 for ell in range(r+1))


def avoiding_kernel_count(q: int, r: int, intersections: tuple[int, ...], ell: int) -> int:
    return avoiding_kernel_counts(q, r, intersections)[ell] if 0 <= ell <= r else 0


def probability_from_invariants(q: int, n: int, dimensions: tuple[int, ...],
                                half_ranks: tuple[int, ...], total_half_rank: int,
                                intersections: tuple[int, ...]) -> Fraction:
    """Probability of one particular cross-block observation with these invariants.

    The caller must supply invariants of an actual alternating block matrix.
    This is a point probability, not the probability of the entire rank stratum.
    """
    if not (len(dimensions) == len(half_ranks) == len(intersections)):
        raise ValueError('One rank and intersection dimension per block is required')
    denominator = prod(embeddings(q, n, d, s) for d, s in zip(dimensions, half_ranks))
    if denominator == 0:
        raise ValueError('An individual frame cannot fit in the ambient space')
    dimension = sum(dimensions)
    r = dimension-2*total_half_rank
    counts = avoiding_kernel_counts(q, r, intersections)
    numerator = sum(counts[ell]*embeddings(q, n, dimension-ell, total_half_rank)
                    for ell in range(r+1))
    return Fraction(numerator, denominator)


def nullity_moment(q: int, dimensions: tuple[int, ...],
                   half_ranks: tuple[int, ...] | None = None) -> Fraction:
    """Exact E_uniform(q ** nullity) with arbitrary fixed diagonal Gram forms."""
    if half_ranks is None:
        half_ranks = (0,) * len(dimensions)
    if len(dimensions) != len(half_ranks) or not dimensions:
        raise ValueError('A nonempty block list and one half-rank per block are required')
    if any(d < 1 or s < 0 or 2*s > d for d, s in zip(dimensions, half_ranks)):
        raise ValueError('Require d_i >= 1 and 0 <= 2s_i <= d_i')
    dimension = sum(dimensions)
    single = sum(q**d-1 for d in dimensions)
    mixed = (q**dimension-1-single) * qpower(q, 1-dimension)
    one = sum((q**(d-2*s)-1)*qpower(q, d-dimension)
              for d, s in zip(dimensions, half_ranks))
    return 1+mixed+one


def tv_bounds(q: int, n: int, dimensions: tuple[int, ...],
              half_ranks: tuple[int, ...] | None = None) -> dict:
    if half_ranks is None:
        half_ranks = (0,) * len(dimensions)
    if any(d-s > n for d, s in zip(dimensions, half_ranks)):
        raise ValueError('An individual frame cannot fit')
    moment = nullity_moment(q, dimensions, half_ranks)
    gap = sum(dimensions)-2*n
    lower = Fraction(0)
    upper = Fraction(1)
    if gap <= 0:
        upper = min(upper, moment*qpower(q, gap)/(q*q-1))
    else:
        lower = max(lower, 1-(moment-1)/(q**gap-1))
    return {'q': q, 'n': n, 'ambient_dimension': 2*n,
            'dimensions': list(dimensions), 'half_ranks': list(half_ranks),
            'total_dimension': sum(dimensions), 'gap': gap,
            'nullity_moment': str(moment), 'tv_lower': str(lower),
            'tv_upper': str(upper), 'tv_lower_decimal': float(lower),
            'tv_upper_decimal': float(upper)}


def prime_rank(matrix: list[list[int]], p: int) -> int:
    """Rank over F_p. p must be prime; this function does not handle F_(p^a)."""
    if p < 2 or any(p % a == 0 for a in range(2, int(p**0.5)+1)):
        raise ValueError('Matrix arithmetic requires prime p')
    a = [[v % p for v in row] for row in matrix]
    if not a:
        return 0
    rank, width = 0, len(a[0])
    if any(len(row) != width for row in a):
        raise ValueError('Ragged matrix')
    for col in range(width):
        pivot = next((j for j in range(rank, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], -1, p)
        a[rank] = [x*inv % p for x in a[rank]]
        for j in range(len(a)):
            if j != rank and a[j][col]:
                factor = a[j][col]
                a[j] = [(x-factor*y) % p for x, y in zip(a[j], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def matrix_probability(p: int, n: int, dimensions: tuple[int, ...],
                        gamma: list[list[int]]) -> dict:
    dimension = sum(dimensions)
    if len(gamma) != dimension or any(len(row) != dimension for row in gamma):
        raise ValueError('Gram matrix size does not match dimensions')
    if any(gamma[i][i] % p for i in range(dimension)) or any(
            (gamma[i][j]+gamma[j][i]) % p for i in range(dimension) for j in range(dimension)):
        raise ValueError('Gram matrix must be alternating, also in characteristic two')
    ranks, intersections, offset = [], [], 0
    for d in dimensions:
        cols = range(offset, offset+d)
        block = [[gamma[i][j] for j in cols] for i in cols]
        ranks.append(prime_rank(block, p)//2)
        intersections.append(d-prime_rank([[row[j] for j in cols] for row in gamma], p))
        offset += d
    half_rank = prime_rank(gamma, p)//2
    probability = probability_from_invariants(p, n, dimensions, tuple(ranks),
                                             half_rank, tuple(intersections))
    b = sum(dimensions[i]*dimensions[j] for i in range(len(dimensions))
            for j in range(i+1, len(dimensions)))
    return {'probability': str(probability), 'uniform_probability': str(Fraction(1, p**b)),
            'likelihood_ratio': str(probability*p**b), 'total_half_rank': half_rank,
            'individual_half_ranks': ranks, 'radical_intersections': intersections,
            'minimum_ambient_dimension': 2*(half_rank+max(intersections, default=0))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--q', type=int, default=2)
    parser.add_argument('--n', type=int, default=50)
    parser.add_argument('--dimensions', type=int, nargs='+', default=[40, 40, 40])
    parser.add_argument('--half-ranks', type=int, nargs='+')
    parser.add_argument('--matrix-json', help='Optional JSON file containing a full Gram matrix (prime q only)')
    args = parser.parse_args()
    dimensions = tuple(args.dimensions)
    if args.matrix_json:
        with open(args.matrix_json, encoding='utf-8') as handle:
            result = matrix_probability(args.q, args.n, dimensions, json.load(handle))
    else:
        result = tv_bounds(args.q, args.n, dimensions,
                           tuple(args.half_ranks) if args.half_ranks is not None else None)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
