#!/usr/bin/env python3
"""Finite algebra checks for the accompanying mathematical report.

These assertions test permutations, finite index identities, and rational
residue frequencies. They do NOT verify forcing, genericity, HOD, or any
large-cardinal consistency statement. Requires Python 3.9 or newer.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import gcd, lcm
from typing import Sequence


def power(p: Sequence[int], exponent: int) -> tuple[int, ...]:
    """Return p**exponent, representing a permutation by its value tuple."""
    n = len(p)
    if sorted(p) != list(range(n)):
        raise ValueError("Not a permutation of an initial interval")
    if exponent < 0:
        inverse = [0] * n
        for i, image in enumerate(p):
            inverse[image] = i
        return power(inverse, -exponent)
    result = tuple(range(n))
    base = tuple(p)
    while exponent:
        if exponent & 1:
            result = tuple(base[result[i]] for i in range(n))
        base = tuple(base[base[i]] for i in range(n))
        exponent >>= 1
    return result


def root_permutation(g: Sequence[int], levels: int) -> tuple[int, ...]:
    """Encode (i,a) as i*levels+a and form the root used in the proof."""
    if levels < 1:
        raise ValueError("The number of levels must be positive")
    if sorted(g) != list(range(len(g))):
        raise ValueError("g must be a permutation")
    return tuple(
        i * levels + a + 1 if a + 1 < levels else g[i] * levels
        for i in range(len(g)) for a in range(levels)
    )


def root_checks() -> int:
    count = 0
    for m in range(1, 7):
        for g in permutations(range(m)):
            for h in range(1, 7):
                levels = lcm(*range(1, h + 1))
                tau = root_permutation(g, levels)
                got = power(tau, levels)
                expected = tuple(g[i] * levels + a
                                 for i in range(m) for a in range(levels))
                assert got == expected, (m, g, h)
                count += 1
    return count


def finite_family_exponent_checks() -> int:
    count = 0
    for h in range(1, 9):
        exponent = lcm(*range(1, h + 1))
        for p in permutations(range(h)):
            assert power(p, exponent) == tuple(range(h))
            count += 1
    return count


def deletion_checks() -> int:
    count = 0
    length = 30
    c = [1000 * (n + 1) for n in range(length)]
    for m in range(1, 5):
        for g in permutations(range(m)):
            for h in range(1, 5):
                levels = lcm(*range(1, h + 1))
                tau = root_permutation(g, levels)
                n_tags = len(tau)
                assert n_tags < 1000  # the simulated blocks are disjoint
                inverse_powers = [power(tau, -n) for n in range(length)]
                for k in (0, 1, 5, 20):
                    d = c[:k] + c[k + 1:]
                    for e in range(n_tags):
                        for n in range(k, len(d)):
                            lhs = d[n] + inverse_powers[n][e]
                            rhs = c[n + 1] + inverse_powers[n + 1][tau[e]]
                            assert lhs == rhs, (m, g, h, k, e, n)
                            count += 1
    return count


def selector_checks() -> int:
    count = 0
    for n in range(2, 13):
        cycle = tuple((i + 1) % n for i in range(n))
        for r in range(1, n):
            for subset in combinations(range(n), r):
                image = {cycle[i] for i in subset}
                assert image != set(subset)
                count += 1
    return count


def s3_checks() -> int:
    """Natural three labels plus two labels with the sign action."""
    fixed_sets = []
    for g in permutations(range(3)):
        odd = sum(g[i] > g[j] for i in range(3)
                  for j in range(i + 1, 3)) % 2
        action = tuple(g) + ((4, 3) if odd else (3, 4))
        fixed = {i for i in range(5) if action[i] == i}
        assert fixed
        fixed_sets.append(fixed)
    assert not set.intersection(*fixed_sets)
    return len(fixed_sets)


def residue_checks() -> int:
    count = 0
    for d in range(1, 13):
        for n in range(1, 21):
            period = n // gcd(d, n)
            for r in range(d):
                residues = [-(d * j + r) % n for j in range(period)]
                for cell in range(n):
                    got = Fraction(residues.count(cell), period)
                    expected = (Fraction(gcd(d, n), n)
                                if (cell + r) % gcd(d, n) == 0
                                else Fraction(0))
                    assert got == expected, (d, n, r, cell)
                    count += 1
    return count


def main() -> None:
    checks = [
        ("Permutation-root cases (all m<=6, h<=6)", root_checks),
        ("Finite-family exponent cases (all h<=8)", finite_family_exponent_checks),
        ("Individual deletion-index equalities", deletion_checks),
        ("Proper subsets moved by a full cycle (n<=12)", selector_checks),
        ("S3 elementwise-fixed-point checks", s3_checks),
        ("Exact periodic-ray residue frequencies", residue_checks),
    ]
    print("FINITE ALGEBRA CHECKS FOR CARDINALS5")
    print("Python standard library; deterministic exhaustive finite tests.\n")
    for name, check in checks:
        cases = check()
        print(f"PASS  {name}: {cases:,}")
    print("\nAll assertions passed.")
    print("Scope: finite algebra and finite rational-frequency identities only.")
    print("Not a verification of forcing, genericity, HOD, or consistency proofs.")


if __name__ == "__main__":
    main()
