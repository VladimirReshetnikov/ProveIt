#!/usr/bin/env python3
"""Exact symplectic-compression probabilities, using Python's standard library.

The mathematical counting formula is valid for every prime power q.  This
implementation represents field elements by integers modulo q and therefore
accepts PRIME q only for matrix operations.  Scalar product/count functions
also make sense at prime powers; no extension-field arithmetic is claimed.

Conventions: V has dimension 2*m.  S is the alternating Gram matrix of the
fixed target b-frame; H is that of the source a-frame; C is the prescribed
b-by-a matrix of pairings (target vector, moving source vector).  All returns
are exact integers or fractions.Fraction.  Empty frames are supported.

Run: python3 compression_law.py --output example_results.json
"""

from fractions import Fraction
from math import prod, isqrt
import argparse
import json


def is_prime(q):
    return isinstance(q, int) and q >= 2 and all(q % p for p in range(2, isqrt(q) + 1))


def require_prime(q):
    if not is_prime(q):
        raise ValueError("Matrix arithmetic here requires a prime q; the theorem allows prime powers.")


def qbin(n, k, q):
    """Gaussian binomial, with zero outside 0 <= k <= n."""
    if n < 0 or k < 0 or k > n:
        return 0
    if q < 2:
        raise ValueError("q must be at least 2")
    k = min(k, n - k)
    numerator = prod(q ** (n - i) - 1 for i in range(k))
    denominator = prod(q ** (k - i) - 1 for i in range(k))
    return numerator // denominator


def symplectic_order(m, q):
    if m < 0:
        return 0
    return q ** (m * m) * prod(q ** (2 * j) - 1 for j in range(1, m + 1))


def general_linear_order(n, q):
    if n < 0:
        return 0
    return prod(q ** n - q ** i for i in range(n))


def frame_count(m, d, r, q):
    """E_m(d,r): injective d-frames with fixed alternating Gram rank 2r."""
    z = d - 2 * r
    if min(m, d, r, z) < 0 or d - r > m:
        return 0
    return (q ** (2 * m * r - r * r + z * (z - 1) // 2)
            * prod(q ** (2 * j) - 1 for j in range(m - d + r + 1, m + 1)))


def transverse_count(z, p, t, k, q):
    """k-subspaces of F_q^z disjoint from fixed disjoint p- and t-spaces.

    Positive-term formula, obtained by choosing a graph over a complement
    of the first distinguished subspace.  Swapping p and t gives the same
    answer, although the displayed summation is not syntactically symmetric.
    """
    if min(z, p, t) < 0 or p + t > z:
        raise ValueError("Need 0 <= p,t and p+t <= z")
    if k < 0 or k > z - max(p, t):
        return 0
    free = z - p - t
    result = 0
    for j in range(min(k, p, t) + 1):
        coefficient = qbin(t, j, q) * qbin(free, k - j, q)
        if coefficient:
            result += (coefficient * q ** ((p + t - j) * (k - j))
                       * prod(q ** p - q ** i for i in range(j)))
    return result


def rank_mod(matrix, q):
    """Rank over F_q for PRIME q.  Input is not modified."""
    require_prime(q)
    if not matrix:
        return 0
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("Ragged matrix")
    work = [[entry % q for entry in row] for row in matrix]
    pivot_row = 0
    for column in range(width):
        pivot = next((i for i in range(pivot_row, len(work)) if work[i][column]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        inverse = pow(work[pivot_row][column], -1, q)
        work[pivot_row] = [(entry * inverse) % q for entry in work[pivot_row]]
        for i in range(pivot_row + 1, len(work)):
            coefficient = work[i][column]
            if coefficient:
                work[i] = [(x - coefficient * y) % q
                           for x, y in zip(work[i], work[pivot_row])]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return pivot_row


def validate_alternating(matrix, q):
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Gram matrices must be square")
    if any(matrix[i][i] % q for i in range(n)):
        raise ValueError("Alternating matrices must have zero diagonal, also in characteristic two")
    if any((matrix[i][j] + matrix[j][i]) % q for i in range(n) for j in range(n)):
        raise ValueError("Gram matrix is not alternating")


def compression_invariants(q, S, H, C):
    """Return (a,b,s,h,r,z,p,t) invariants used by the main theorem."""
    require_prime(q)
    validate_alternating(S, q)
    validate_alternating(H, q)
    b, a = len(S), len(H)
    if len(C) != b or any(len(row) != a for row in C):
        raise ValueError("C must be b-by-a, with S b-by-b and H a-by-a")
    gram = [list(S[i]) + list(C[i]) for i in range(b)]
    gram += [[-C[j][i] for j in range(b)] + list(H[i]) for i in range(a)]
    s, h = rank_mod(S, q) // 2, rank_mod(H, q) // 2
    r = rank_mod(gram, q) // 2
    z = a + b - 2 * r
    # p=dim(rad S intersect ker C^T), t=dim(rad H intersect ker C).
    p = b - rank_mod(list(S) + [[C[j][i] for j in range(b)] for i in range(a)], q)
    t = a - rank_mod(list(H) + list(C), q)
    return {"a": a, "b": b, "s": s, "h": h, "r": r, "z": z, "p": p, "t": t}


def compression_probability(q, m, S, H, C):
    """Probability of the exact cross-pairing matrix C."""
    inv = compression_invariants(q, S, H, C)
    a, b, s, h, r, z, p, t = (inv[key] for key in ("a", "b", "s", "h", "r", "z", "p", "t"))
    denominator = frame_count(m, b, s, q) * frame_count(m, a, h, q)
    if denominator == 0:
        raise ValueError("One prescribed frame cannot embed in the ambient symplectic space")
    numerator = sum(transverse_count(z, p, t, k, q)
                    * frame_count(m, a + b - k, r, q)
                    for k in range(z + 1))
    return Fraction(numerator, denominator)


def compression_likelihood(q, m, S, H, C):
    """Density relative to the uniform law on all b-by-a matrices."""
    return compression_probability(q, m, S, H, C) * q ** (len(S) * len(H))


def compression_supported(q, m, S, H, C):
    """Sharp support criterion; requires both prescribed frames to embed."""
    inv = compression_invariants(q, S, H, C)
    if not frame_count(m, inv["a"], inv["h"], q) or not frame_count(m, inv["b"], inv["s"], q):
        raise ValueError("One prescribed frame cannot embed in the ambient symplectic space")
    return inv["r"] + max(inv["p"], inv["t"]) <= m


def plane_distances(q, s, c):
    """Exact full and rank-only TV for a symplectic plane projected to 2s coordinates.

    Ambient dimension is 2(s+c); the target is nondegenerate.  s>=1,c>=0.
    This scalar formula is valid for every prime power q (no field arithmetic).
    """
    if q < 2 or s < 1 or c < 0:
        raise ValueError("Need q>=2, s>=1, c>=0")
    x, y = Fraction(1, q ** (2 * s)), Fraction(1, q ** (2 * c))
    denominator = 1 - x * y
    likelihood_pairing_one = (1 + (q - 1) * y) / denominator
    likelihood_other = (1 - y) / denominator
    uniform_pairing_one = (1 - x) / q
    uniform_rank_deficiency = (q + 1) * x - q * x * x
    full_tv = uniform_pairing_one * (likelihood_pairing_one - 1)
    rank_tv = uniform_rank_deficiency * (1 - likelihood_other)
    limiting_full_tv = Fraction(q - 1, q ** (2 * c + 1))
    return {"q": q, "s": s, "c": c,
            "likelihood_pairing_one": likelihood_pairing_one,
            "likelihood_other": likelihood_other,
            "uniform_pairing_one": uniform_pairing_one,
            "uniform_rank_deficiency": uniform_rank_deficiency,
            "full_tv": full_tv, "rank_tv": rank_tv,
            "limiting_full_tv": limiting_full_tv}


def alternating_form_count(q, a, r):
    """Number of a-by-a alternating matrices of rank 2r."""
    if r < 0 or 2 * r > a:
        return 0
    return qbin(a, 2 * r, q) * (general_linear_order(2 * r, q) // symplectic_order(r, q))


def gram_map_count(q, c, a, r):
    """Number of all 2c-by-a matrices with one prescribed Gram matrix of rank 2r.

    The maps need not be injective.  This scalar formula allows prime powers.
    """
    if min(c, a, r) < 0 or 2 * r > a:
        return 0
    return sum(qbin(a - 2 * r, k, q) * frame_count(c, a - k, r, q)
               for k in range(a - 2 * r + 1))


def gram_boundary_law(q, a, c):
    """Rank-stratified exact law of Y^T J_c Y for uniform Y in Mat(2c,a)."""
    if q < 2 or min(a, c) < 0:
        raise ValueError("Need q>=2, a>=0 and c>=0")
    D = a * (a - 1) // 2
    uniform_per_matrix = Fraction(1, q ** D)
    result = []
    for r in range(a // 2 + 1):
        count = alternating_form_count(q, a, r)
        number_of_maps = gram_map_count(q, c, a, r)
        probability = Fraction(number_of_maps, q ** (2 * c * a))
        result.append({"rank": 2 * r, "form_count": count,
                       "map_count_per_form": number_of_maps,
                       "probability_per_form": probability,
                       "uniform_probability_per_form": uniform_per_matrix,
                       "likelihood": probability / uniform_per_matrix,
                       "tv_contribution": Fraction(count, 2) * abs(probability - uniform_per_matrix)})
    return result


def gram_boundary_delta(q, a, c):
    """Delta_q(a,c): TV of the alternating Gram law from the uniform form law."""
    return sum((row["tv_contribution"] for row in gram_boundary_law(q, a, c)), Fraction())


def json_ready(value):
    if isinstance(value, Fraction):
        return {"exact": str(value), "decimal": float(value)}
    if isinstance(value, dict):
        return {key: json_ready(entry) for key, entry in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_ready(entry) for entry in value]
    return value


def examples():
    J = [[0, 1], [-1, 0]]
    choices = {"determinant_one": [[1, 0], [0, 1]],
               "determinant_two": [[1, 0], [0, 2]],
               "rank_one": [[1, 0], [0, 0]],
               "zero": [[0, 0], [0, 0]]}
    determinant_examples = {
        name: {"matrix": C, "probability": compression_probability(3, 2, J, J, C),
               "likelihood": compression_likelihood(3, 2, J, J, C),
               "invariants": compression_invariants(3, J, J, C)}
        for name, C in choices.items()}
    return {"implementation_field_scope": "matrix operations: prime q only; scalar counts: prime powers",
            "symplectic_plane_examples": [plane_distances(q, s, c)
                for q, s, c in [(2, 1, 1), (2, 4, 1), (2, 10, 1),
                                (2, 20, 1), (3, 1, 1), (3, 10, 1), (2, 10, 0)]],
            "same_rank_different_likelihood_q3": determinant_examples,
            "boundary_constants_q2": [
                {"q": 2, "source_dimension": a, "complement_half_dimension": c,
                 "delta": gram_boundary_delta(2, a, c),
                 "rank_strata": gram_boundary_law(2, a, c)}
                for a in (2, 3, 4) for c in (0, 1, 2, 3)]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="write reproducible exact sample results to this JSON file")
    args = parser.parse_args()
    result = json.dumps(json_ready(examples()), indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(result)
    else:
        print(result, end="")
