#!/usr/bin/env python3
"""Exact finite-field rank certificates for two crossing flattenings.

Standard-library implementation. This is a local compiler/checker, not a SAT
solver and not a proof of improved asymptotic ranks for Anthropic's pieces.
Run this file directly to execute its deterministic checks and write results.
"""

from __future__ import annotations

from itertools import product
import json
from pathlib import Path
import random


def is_prime(p: int) -> bool:
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    q = 3
    while q * q <= p:
        if p % q == 0:
            return False
        q += 2
    return True


def matmul(a: list[list[int]], b: list[list[int]], p: int,
           zero_columns: int | None = None) -> list[list[int]]:
    width = len(b[0]) if b else zero_columns
    if width is None:
        raise ValueError("The width of an empty right factor is required")
    if any(len(row) != len(b) for row in a):
        raise ValueError("Incompatible factors")
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) % p
             for j in range(width)] for i in range(len(a))]


def rref(a: list[list[int]], p: int) -> tuple[list[list[int]], list[int]]:
    if not is_prime(p):
        raise ValueError("The modulus must be prime")
    if not a:
        return [], []
    columns = len(a[0])
    if any(len(row) != columns for row in a):
        raise ValueError("Ragged matrix")
    b = [[x % p for x in row] for row in a]
    pivots: list[int] = []
    top = 0
    for j in range(columns):
        pivot = next((i for i in range(top, len(b)) if b[i][j]), None)
        if pivot is None:
            continue
        b[top], b[pivot] = b[pivot], b[top]
        inv = pow(b[top][j], -1, p)
        b[top] = [(x * inv) % p for x in b[top]]
        for i in range(len(b)):
            if i != top and b[i][j]:
                q = b[i][j]
                b[i] = [(x - q * y) % p
                        for x, y in zip(b[i], b[top])]
        pivots.append(j)
        top += 1
        if top == len(b):
            break
    return b, pivots


def factor_mod(a: list[list[int]], p: int) -> dict:
    reduced, pivots = rref(a, p)
    columns = len(a[0]) if a else 0
    left = [[row[j] % p for j in pivots] for row in a]
    right = reduced[:len(pivots)]
    # Independent product check, including the zero-rank case.
    rebuilt = matmul(left, right, p, zero_columns=columns)
    if rebuilt != [[x % p for x in row] for row in a]:
        raise ArithmeticError("A proposed rank factorization is incorrect")
    # The selected columns of RREF form an identity, proving independence.
    for i, row in enumerate(right):
        if [row[j] for j in pivots] != [int(i == j) for j in range(len(pivots))]:
            raise ArithmeticError("Pivot columns do not certify independence")
    return {"rank": len(pivots), "bits": (len(pivots) - 1).bit_length()
            if pivots else 0, "left": left, "right": right,
            "pivot_columns": pivots, "columns": columns, "prime": p}


def flatten(piece: dict[tuple[int, int, int, int], int], n: int,
            orientation: str) -> list[list[int]]:
    result = [[0] * (n * n) for _ in range(n * n)]
    for x, y, u, v in product(range(n), repeat=4):
        if orientation == "row":
            i, j = x * n + y, u * n + v
        elif orientation == "column":
            i, j = x * n + u, y * n + v
        else:
            raise ValueError("Unknown orientation")
        result[i][j] = piece.get((x, y, u, v), 0)
    return result


def crt_nonnegative(residues: list[int], primes: list[int]) -> tuple[int, int]:
    if len(residues) != len(primes) or len(set(primes)) != len(primes):
        raise ValueError("CRT requires equally many residues and distinct primes")
    x, modulus = 0, 1
    for residue, p in zip(residues, primes):
        if not is_prime(p):
            raise ValueError("CRT modulus is not prime")
        x += modulus * (((residue - x) * pow(modulus, -1, p)) % p)
        modulus *= p
    return x, modulus


def crt_signed(residues: list[int], primes: list[int], exponent: int) -> int:
    """Recover Z with |Z| <= 2^exponent; require modulus > 2^(exponent+1)."""
    if exponent < 0:
        raise ValueError("A nonnegative height exponent is required")
    x, modulus = crt_nonnegative(residues, primes)
    if modulus <= 1 << (exponent + 1):
        raise ValueError("The CRT modulus does not certify signed reconstruction")
    if 2 * x > modulus:
        x -= modulus
    if abs(x) > 1 << exponent:
        raise ValueError("Residues are inconsistent with the supplied height bound")
    return x


def compile_crossing_pieces(pieces: list[dict], n: int, d: int, p: int) -> list[dict]:
    if not is_prime(p) or d % p == 0:
        raise ValueError("The crossing normalizer must be invertible in a prime field")
    certificates = []
    for piece in pieces:
        row = factor_mod(flatten(piece, n, "row"), p)
        column = factor_mod(flatten(piece, n, "column"), p)
        certificates.append({"row": row, "column": column,
                             "combined_bits": row["bits"] + column["bits"]})
    for key in product(range(n), repeat=4):
        x, y, u, v = key
        expected = d * int(x == v and y == u)
        if (sum(piece.get(key, 0) for piece in pieces) - expected) % p:
            raise ArithmeticError("The pieces do not sum to the normalized crossing")
    return certificates


def run_checks() -> dict:
    rng = random.Random(20261027)
    matrix_cases = 0
    for p in [2, 3, 5, 17, 257]:
        for m, n in product(range(1, 8), repeat=2):
            for intended_rank in range(min(m, n) + 1):
                a = [[rng.randrange(p) for _ in range(intended_rank)] for _ in range(m)]
                b = [[rng.randrange(p) for _ in range(n)] for _ in range(intended_rank)]
                matrix = matmul(a, b, p, zero_columns=n)
                certificate = factor_mod(matrix, p)
                if certificate["rank"] > intended_rank:
                    raise ArithmeticError("Rank exceeds the exhibited factorization")
                matrix_cases += 1

    # An exact crossing decomposition with low individual ranks but exponentially
    # many pieces. This intentionally does NOT meet Definition 7's piece-count
    # requirement. It checks both flattenings and guards against omitting that
    # hypothesis from a claimed rank-based exponent improvement.
    crossing_results = []
    for n in [2, 4, 8]:
        pieces = [{(a, y, y, a): 1 for y in range(n)} for a in range(n)]
        for p in [3, 5, 17]:
            certificates = compile_crossing_pieces(pieces, n, 1, p)
            ranks = [(c["row"]["rank"], c["column"]["rank"])
                     for c in certificates]
            if ranks != [(n, n)] * n:
                raise ArithmeticError("Matrix-unit crossing ranks are incorrect")
            crossing_results.append({"lambda": n.bit_length() - 1,
                                     "prime": p, "pieces": n,
                                     "row_rank": n, "column_rank": n,
                                     "combined_bits": certificates[0]["combined_bits"]})

    rejected = 0
    for modulus in [4, 6, 9]:
        try:
            factor_mod([[1, 2], [2, 4]], modulus)
        except ValueError:
            rejected += 1
        else:
            raise ArithmeticError("Composite modulus was accepted")
    try:
        compile_crossing_pieces([{(0, 0, 0, 0): 2}], 1, 2, 2)
    except ValueError:
        rejected += 1
    else:
        raise ArithmeticError("A zero normalizer was accepted")

    # Rank can drop at one prime. This example guards against replacing a
    # uniform-many-primes CRT premise by one favorable prime experiment.
    special = [[1, 0], [0, 3]]
    rank_drops = {str(p): factor_mod(special, p)["rank"] for p in [2, 3, 5, 7]}
    if rank_drops != {"2": 2, "3": 1, "5": 2, "7": 2}:
        raise ArithmeticError("The exceptional-prime control failed")

    primes = [5, 7, 11, 13]
    crt_cases = 0
    for x in range(2049):
        rebuilt, modulus = crt_nonnegative([x % p for p in primes], primes)
        if rebuilt != x or modulus <= 2048:
            raise ArithmeticError("CRT reconstruction failed")
        crt_cases += 1

    signed_crt_cases = 0
    for x in range(-2048, 2049):
        rebuilt = crt_signed([x % p for p in primes], primes, 11)
        if rebuilt != x:
            raise ArithmeticError("Signed CRT reconstruction failed")
        signed_crt_cases += 1

    # Signed integer network values must be recovered BEFORE the original
    # Appendix D reductions modulo 2^nu. Odd-prime congruences alone do not
    # preserve a truncated identity that was proved only modulo 2^nu.
    network_cases = 0
    network_primes = [101, 103, 107, 109]
    for vertices in range(2, 7):
        edges = [(v, v + 1) for v in range(vertices - 1)]
        incidence = [[j for j, e in enumerate(edges) if v in e]
                     for v in range(vertices)]
        for _ in range(10):
            tables = [[rng.randrange(-7, 8) for _ in range(1 << len(ports))]
                      for ports in incidence]
            value = 0
            for assignment in product([0, 1], repeat=len(edges)):
                term = 1
                for ports, table in zip(incidence, tables):
                    index = sum(assignment[e] << j for j, e in enumerate(ports))
                    term *= table[index]
                value += term
            height = len(edges) + 3 * vertices  # D + sum_v B_v; |W_v| < 2^3.
            rebuilt = crt_signed([value % p for p in network_primes],
                                 network_primes, height)
            if rebuilt != value:
                raise ArithmeticError("Signed integer network bridge failed")
            for precision in [1, 3, 5, 9]:
                if rebuilt % (1 << precision) != value % (1 << precision):
                    raise ArithmeticError("The subsequent two-adic reduction failed")
            network_cases += 1

    # Explicit witness that the least nonnegative odd-CRT lift cannot simply
    # be reduced modulo a power of two when the integer network value is signed.
    negative_value = -31  # (-3)*7 + 5*(-2), a two-vertex one-wire network.
    odd_primes = [5, 7, 11]
    wrong_lift, odd_modulus = crt_nonnegative([negative_value % p for p in odd_primes],
                                            odd_primes)
    signed_value = crt_signed([negative_value % p for p in odd_primes], odd_primes, 7)
    if wrong_lift % 32 == negative_value % 32 or signed_value != negative_value:
        raise ArithmeticError("The signed/two-adic negative control failed")

    return {
        "status": "PASS",
        "matrix_factorization_cases": matrix_cases,
        "crossing_cases": crossing_results,
        "invalid_input_rejections": rejected,
        "exceptional_prime_ranks": rank_drops,
        "crt_reconstruction_cases": crt_cases,
        "signed_crt_reconstruction_cases": signed_crt_cases,
        "signed_integer_network_cases": network_cases,
        "two_adic_bridge_negative_control": {
            "network_value": negative_value, "odd_modulus": odd_modulus,
            "nonnegative_lift": wrong_lift, "wrong_mod_32": wrong_lift % 32,
            "correct_mod_32": signed_value % 32,
        },
        "claim_scope": "Finite-field rank compiler and CRT only; no new rank theorem or SAT solver",
        "negative_control": "Matrix-unit pieces have 2^lambda pieces and fail the polynomial-piece premise",
    }


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run_checks()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
