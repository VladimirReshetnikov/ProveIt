#!/usr/bin/env python3
"""Exact checks for the bounded-width power-set compression article.

The script uses only Python's standard library.  It verifies the recursive
symmetric-chain decomposition, the central-binomial tables, the self-indexed
thresholds, and the monotonicity identities quoted in the manuscript.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, log2, pi
from pathlib import Path
from typing import FrozenSet, Iterable, List

Subset = FrozenSet[int]
Chain = List[Subset]


def central_width(n: int) -> int:
    return comb(n, n // 2)


def compression_number(n: int, r: int) -> int:
    if n < 0 or r < 1:
        raise ValueError("require n >= 0 and r >= 1")
    return (central_width(n) + r - 1) // r


def defect(n: int) -> int:
    if n < 1:
        raise ValueError("require n >= 1")
    return (central_width(n) + n - 1) // n


def threshold(r: int) -> int:
    if r < 1:
        raise ValueError("require r >= 1")
    n = 0
    while central_width(n + 1) <= r * (n + 1):
        n += 1
    return n


def symmetric_chain_decomposition(n: int) -> List[Chain]:
    """Return the standard recursive SCD of the Boolean lattice B_n.

    From a symmetric chain C in B_{n-1}, make one chain by appending the new
    point to its top, and (when nonempty) a second chain by adjoining the new
    point to every member except the old top.
    """
    if n < 0:
        raise ValueError("require n >= 0")
    chains: List[Chain] = [[frozenset()]]
    for new_point in range(1, n + 1):
        next_chains: List[Chain] = []
        for chain in chains:
            next_chains.append(chain + [chain[-1] | {new_point}])
            if len(chain) >= 2:
                next_chains.append([a | {new_point} for a in chain[:-1]])
        chains = next_chains
    return chains


def verify_scd(n: int) -> tuple[int, int]:
    chains = symmetric_chain_decomposition(n)
    flattened = [a for c in chains for a in c]
    assert len(flattened) == 2**n
    assert len(set(flattened)) == 2**n
    assert len(chains) == central_width(n)
    universe = frozenset(range(1, n + 1))
    for chain in chains:
        assert chain
        assert all(a <= universe for a in chain)
        assert all(chain[i] < chain[i + 1] for i in range(len(chain) - 1))
        assert len(chain[0]) + len(chain[-1]) == n
        assert all(len(chain[i + 1]) == len(chain[i]) + 1
                   for i in range(len(chain) - 1))
    return len(chains), len(flattened)


def verify_grouped_certificate(n: int, r: int) -> int:
    chains = symmetric_chain_decomposition(n)
    groups = [chains[i : i + r] for i in range(0, len(chains), r)]
    assert len(groups) == compression_number(n, r)
    # The supplied certificate is a partition into at most r chains per color.
    seen: set[Subset] = set()
    for group in groups:
        assert 1 <= len(group) <= r
        for chain in group:
            for a in chain:
                assert a not in seen
                seen.add(a)
    assert len(seen) == 2**n
    return len(groups)


def verify_monotonicity(limit: int = 300) -> None:
    ratios = [Fraction(central_width(n), n) for n in range(1, limit + 1)]
    assert all(ratios[i] <= ratios[i + 1] for i in range(len(ratios) - 1))
    defects = [defect(n) for n in range(1, limit + 1)]
    assert all(defects[i] <= defects[i + 1] for i in range(len(defects) - 1))


def format_scd_example(n: int) -> str:
    def show(a: Subset) -> str:
        return "{}" if not a else "{" + ",".join(map(str, sorted(a))) + "}"

    lines = []
    for i, chain in enumerate(symmetric_chain_decomposition(n), start=1):
        lines.append(f"C{i}: " + " < ".join(show(a) for a in chain))
    return "\n".join(lines)


def main() -> None:
    report: list[str] = []
    report.append("BOUNDED-WIDTH POWER-SET COMPRESSION: EXACT VERIFICATION\n")
    report.append("1. Recursive symmetric-chain decompositions")
    for n in range(0, 15):
        chains, elements = verify_scd(n)
        report.append(
            f"   n={n:2d}: chains={chains:6d} = C(n,floor(n/2)); "
            f"elements={elements:6d} = 2^n"
        )

    report.append("\n2. Grouped-chain upper certificates")
    for n in range(1, 11):
        for r in (1, 2, 3, 4, 5):
            q = verify_grouped_certificate(n, r)
            assert q == (central_width(n) + r - 1) // r
        report.append(f"   n={n:2d}: verified r=1,2,3,4,5")

    verify_monotonicity()
    report.append("\n3. Monotonicity")
    report.append("   W_n/n and ceil(W_n/n) are nondecreasing for 1 <= n <= 300.")
    report.append("   The manuscript also supplies the exact two-parity ratio proof.")

    report.append("\n4. Exact self-indexed defect table")
    report.append("   n                    W_n        delta(n)=ceil(W_n/n)")
    for n in range(1, 31):
        report.append(f"   {n:2d} {central_width(n):22d} {defect(n):12d}")

    report.append("\n5. Thresholds N(r)=max{n: W_n <= r n}")
    for r in list(range(1, 21)) + [32, 64, 128, 256, 512, 1024, 4096, 65536, 1048576]:
        report.append(f"   r={r:8d}: N(r)={threshold(r):2d}")

    report.append("\n6. Asymptotic diagnostic for r=2^k")
    report.append("   k   exact N    L+(3/2)log2 L+(1/2)log2(pi/2)    difference")
    for k in range(4, 25):
        r = 2**k
        L = float(k)
        approximation = L + 1.5 * log2(L) + 0.5 * log2(pi / 2.0)
        exact = threshold(r)
        report.append(
            f"   {k:2d} {exact:9d} {approximation:31.12f} "
            f"{exact - approximation:12.9f}"
        )

    report.append("\n7. Standard recursive SCD of B_4")
    report.append(format_scd_example(4))

    output = "\n".join(report) + "\n"
    path = Path(__file__).with_name("verification_report.txt")
    path.write_text(output, encoding="utf-8")
    print(output)
    print(f"Wrote {path}")


if __name__ == "__main__":
    main()
