#!/usr/bin/env python3
"""Exact verification for the A168362 modulo-four theorem.

This script uses only the Python standard library.  It performs four checks:

1. direct truncated composition of F(x)=sum_{k>=0} x^(2^k) modulo 4;
2. comparison with the closed bitwise classification of the diagonal;
3. comparison with the exact two-bit formula for every small iterate/exponent;
4. generation of the residue sets R_s, the exceptional indices, and the
   convergent constant kappa from the article.

The direct composition is intentionally independent of the carry-transform
proof: it uses dense polynomial squaring in Z/4Z.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable

PUBLISHED_TERMS = [
    1,
    2,
    6,
    34,
    280,
    3010,
    39984,
    634040,
    11704548,
    246799212,
    5856139256,
    154509170816,
    4488522398568,
    142395677932872,
    4899139202191216,
    181714457372434436,
    7228856213182113768,
    307047663830976178304,
    13869994589640136690336,
    663976989978171594869350,
    33579260181092227231600048,
]


def square_poly(poly: list[int], degree: int, modulus: int | None) -> list[int]:
    """Return poly(x)^2 through x^degree, optionally modulo modulus."""
    out = [0] * (degree + 1)
    nonzero = [(i, c) for i, c in enumerate(poly) if c]
    for p, (i, a) in enumerate(nonzero):
        if 2 * i <= degree:
            out[2 * i] += a * a
        for j, b in nonzero[p + 1 :]:
            if i + j > degree:
                break
            out[i + j] += 2 * a * b
    if modulus is not None:
        out = [c % modulus for c in out]
    return out


def lacunary_compose(poly: list[int], degree: int, modulus: int | None) -> list[int]:
    """Compute F(poly)=poly+poly^2+poly^4+... through x^degree."""
    out = poly.copy()
    power = poly
    min_degree = next((i for i, c in enumerate(poly) if c), degree + 1)
    while 2 * min_degree <= degree:
        power = square_poly(power, degree, modulus)
        min_degree *= 2
        if modulus is None:
            for i, c in enumerate(power):
                out[i] += c
        else:
            for i, c in enumerate(power):
                out[i] = (out[i] + c) % modulus
    return out


def direct_iterates_mod4(limit: int) -> tuple[list[int], list[list[int]]]:
    """Return diagonal residues and all rows G_m modulo 4, m<=limit."""
    g = [0] * (limit + 1)
    g[1] = 1
    diagonal: list[int] = []
    rows: list[list[int]] = [g.copy()]
    for m in range(1, limit + 1):
        g = lacunary_compose(g, limit, 4)
        rows.append(g.copy())
        diagonal.append(g[m])
    return diagonal, rows


def exact_initial_terms(limit: int) -> list[int]:
    """Direct integer composition for a small initial range."""
    g = [0] * (limit + 1)
    g[1] = 1
    values: list[int] = []
    for m in range(1, limit + 1):
        g = lacunary_compose(g, limit, None)
        values.append(g[m])
    return values


def residue_set(s: int) -> set[int]:
    """Compute R_s by the symmetric-difference construction in the paper."""
    if s < 1:
        raise ValueError("s must be positive")
    modulus = 1 << s
    mask = modulus - 1
    parity: set[int] = {0}
    for i in range(s + 1):
        one_bits = [j for j in range(s) if (i >> j) & 1]
        required = mask ^ i
        for selector in range(1 << len(one_bits)):
            y = required
            for position, bit in enumerate(one_bits):
                if (selector >> position) & 1:
                    y |= 1 << bit
            d = (y - i) & mask
            if d in parity:
                parity.remove(d)
            else:
                parity.add(d)
    return parity


def theorem_diagonal_residue(n: int) -> int:
    """Closed classification of a(n) modulo 4."""
    if n == 1:
        return 1
    if n in {2, 3, 4, 6}:
        return 2
    if n.bit_count() != 2:
        return 0
    s = (n & -n).bit_length() - 1
    r = n.bit_length() - 1
    if r < 3 or s < 1:
        return 0
    d = r - s
    return 2 if d % (1 << s) in residue_set(s) else 0


def disjoint_count_parity(n: int, mask: int) -> int:
    """Parity of #{0<=t<=n : t & mask = 0}, using the first-difference rule."""
    if n < 0:
        return 0
    answer = int((n & mask) == 0)  # the tight word t=n
    for j in range(n.bit_length()):
        if not ((n >> j) & 1):
            continue
        higher_disjoint = ((n >> (j + 1)) & (mask >> (j + 1))) == 0
        lower_mask = (1 << j) - 1
        no_free_lower_bit = (mask & lower_mask) == lower_mask
        if higher_disjoint and no_free_lower_bit:
            answer ^= 1
    return answer


def exact_two_bit_q(iterate: int, r: int, s: int) -> int:
    """Return [x^(2^r+2^s)]G_iterate / 2 modulo 2."""
    d = r - s
    q = 0
    for i in range(s + 1):
        q ^= disjoint_count_parity(iterate - 2, i | (i + d))
    return q


def exceptional_indices(limit: int) -> list[int]:
    """Generate all n<=limit with a(n)=2 (mod 4) from the theorem."""
    values = {n for n in (2, 3, 4, 6) if n <= limit}
    max_r = max(0, limit.bit_length() - 1)
    for s in range(1, max_r + 1):
        residues = residue_set(s)
        for r in range(max(3, s + 1), max_r + 1):
            n = (1 << r) + (1 << s)
            if n > limit:
                break
            if (r - s) % (1 << s) in residues:
                values.add(n)
    return sorted(values)


def kappa_data(cutoff: int) -> tuple[Fraction, Fraction]:
    """Partial sum and rigorous tail bound for kappa."""
    partial = sum(
        (Fraction(len(residue_set(s)), 1 << s) for s in range(1, cutoff + 1)),
        Fraction(),
    )
    # |R_s| <= 1 + (s+1)(s+2)/2.  Summing this bound for s>cutoff gives
    # (cutoff^2 + 7*cutoff + 16)/2^(cutoff+1).
    tail = Fraction(cutoff * cutoff + 7 * cutoff + 16, 1 << (cutoff + 1))
    return partial, tail


def sha256_lines(lines: Iterable[str]) -> str:
    digest = hashlib.sha256()
    for line in lines:
        digest.update(line.encode("utf-8"))
    return digest.hexdigest()


def verify(limit: int) -> dict[str, object]:
    diagonal, rows = direct_iterates_mod4(limit)
    diagonal_mismatches = [
        (n, diagonal[n - 1], theorem_diagonal_residue(n))
        for n in range(1, limit + 1)
        if diagonal[n - 1] != theorem_diagonal_residue(n)
    ]

    support_mismatches: list[tuple[int, int, int]] = []
    parity_mismatches: list[tuple[int, int, int, int]] = []
    two_bit_mismatches: list[tuple[int, int, int, int]] = []
    for m in range(1, limit + 1):
        row = rows[m]
        for n in range(1, limit + 1):
            coefficient = row[n]
            if n.bit_count() >= 3 and coefficient != 0:
                support_mismatches.append((m, n, coefficient))
            if n & (n - 1):
                expected_parity = 0
            else:
                r = n.bit_length() - 1
                expected_parity = math.comb(m + r - 1, r) & 1
            if (coefficient & 1) != expected_parity:
                parity_mismatches.append((m, n, coefficient & 1, expected_parity))
            if n.bit_count() == 2:
                s = (n & -n).bit_length() - 1
                r = n.bit_length() - 1
                expected_q = exact_two_bit_q(m, r, s)
                observed_q = (coefficient // 2) & 1
                if observed_q != expected_q:
                    two_bit_mismatches.append((m, n, observed_q, expected_q))

    exact_terms = exact_initial_terms(len(PUBLISHED_TERMS))
    initial_match = exact_terms == PUBLISHED_TERMS

    cutoff = 64
    partial, tail = kappa_data(cutoff)
    exceptions = exceptional_indices(10_000_000)
    residue_rows = [(s, sorted(residue_set(s))) for s in range(1, 33)]

    checks = {
        "diagonal_mod4": not diagonal_mismatches,
        "full_array_weight_at_least_three": not support_mismatches,
        "full_array_parity": not parity_mismatches,
        "full_array_two_bit_formula": not two_bit_mismatches,
        "published_initial_terms": initial_match,
    }
    if not all(checks.values()):
        raise AssertionError(
            {
                "checks": checks,
                "diagonal_mismatches": diagonal_mismatches[:10],
                "support_mismatches": support_mismatches[:10],
                "parity_mismatches": parity_mismatches[:10],
                "two_bit_mismatches": two_bit_mismatches[:10],
            }
        )

    row_digest = sha256_lines(
        f"{m},{n},{rows[m][n]}\n"
        for m in range(1, limit + 1)
        for n in range(1, limit + 1)
    )
    return {
        "status": "PASS",
        "direct_mod4_limit": limit,
        "checks": checks,
        "direct_table_sha256": row_digest,
        "published_terms_checked": len(PUBLISHED_TERMS),
        "residue_set_sizes_s_1_to_32": [len(values) for _, values in residue_rows],
        "kappa_cutoff": cutoff,
        "kappa_partial_fraction": f"{partial.numerator}/{partial.denominator}",
        "kappa_partial_decimal": f"{float(partial):.18f}",
        "kappa_tail_bound_fraction": f"{tail.numerator}/{tail.denominator}",
        "kappa_tail_bound_decimal": f"{float(tail):.3e}",
        "exception_limit": 10_000_000,
        "exception_count": len(exceptions),
        "exceptions": exceptions,
    }


def write_outputs(root: Path, result: dict[str, object]) -> None:
    data_dir = root / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    (data_dir / "verification.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )

    with (data_dir / "residue_sets.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["s", "modulus", "cardinality", "residues"])
        for s in range(1, 65):
            values = sorted(residue_set(s))
            writer.writerow([s, 1 << s, len(values), " ".join(map(str, values))])

    exceptions = exceptional_indices(10_000_000)
    (data_dir / "exceptional_indices_to_10m.txt").write_text(
        "# n with a(n) == 2 (mod 4), according to the proved criterion\n"
        + "\n".join(map(str, exceptions))
        + "\n",
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--limit",
        type=int,
        default=256,
        help="direct-composition square size (default: 256)",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="artifact root where data/ is written",
    )
    args = parser.parse_args()
    if args.limit < len(PUBLISHED_TERMS):
        parser.error(f"--limit must be at least {len(PUBLISHED_TERMS)}")

    result = verify(args.limit)
    write_outputs(args.root, result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
