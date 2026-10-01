#!/usr/bin/env python3
"""Exact finite certificates for Arithmetic Rigidity off Resonance.

Standard-library only. This program checks encoded arithmetic data; it does
not decide nonresonance of arbitrary real numbers or verify analytic proofs.
Run: python3 code/verify.py --output results/verification.rerun.json
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations_with_replacement, product
import json
from math import comb, gcd, lcm
from pathlib import Path
from typing import Iterable


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def positive_int(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{name} must be a positive integer")


def nonnegative_int(value: int, name: str) -> None:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def valuation(n: int, p: int) -> int:
    positive_int(n, "n")
    positive_int(p, "p")
    if p == 1:
        raise ValueError("valuation base must exceed one")
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


@dataclass(frozen=True)
class Atom:
    """Width q**level / denominator in a nonresonant source."""
    level: int
    denominator: int

    def __post_init__(self) -> None:
        nonnegative_int(self.level, "level")
        positive_int(self.denominator, "denominator")


def nonresonant_certificate(atoms: Iterable[Atom]) -> dict:
    atoms = list(atoms)
    first: dict[int, tuple[int, Atom]] = {}
    for i, atom in enumerate(atoms):
        if atom.level in first:
            j, other = first[atom.level]
            return {"accepted": False, "kind": "double_zero", "indices": [j, i],
                    "source_level": atom.level,
                    "zero_multiplier": lcm(atom.denominator, other.denominator)}
        first[atom.level] = (i, atom)
    return {"accepted": True, "assignments": [
        {"factor": i, "source_level": a.level, "digit_count": a.denominator}
        for i, a in enumerate(atoms)]}


@dataclass(frozen=True)
class Stream:
    """Widths q**(start + step*j)/(denominator*digit_ratio**j)."""
    start: int
    denominator: int
    step: int
    digit_ratio: int

    def __post_init__(self) -> None:
        nonnegative_int(self.start, "start")
        for field in ("denominator", "step", "digit_ratio"):
            positive_int(getattr(self, field), field)


def first_intersection(a: int, m: int, b: int, n: int) -> int | None:
    """First common element of a+m*N and b+n*N, using exact CRT."""
    nonnegative_int(a, "a")
    nonnegative_int(b, "b")
    positive_int(m, "m")
    positive_int(n, "n")
    g = gcd(m, n)
    if (b - a) % g:
        return None
    modulus = n // g
    j = 0 if modulus == 1 else ((b - a) // g * pow(m // g, -1, modulus)) % modulus
    x = a + m * j
    period = lcm(m, n)
    lower = max(a, b)
    if x < lower:
        x += ((lower - x + period - 1) // period) * period
    return x


def stream_certificate(streams: Iterable[Stream]) -> dict:
    streams = list(streams)
    for i, s in enumerate(streams):
        for j in range(i):
            t = streams[j]
            k = first_intersection(s.start, s.step, t.start, t.step)
            if k is not None:
                u = (k - s.start) // s.step
                v = (k - t.start) // t.step
                return {"accepted": False, "kind": "progression_collision",
                        "streams": [j, i], "source_level": k,
                        "terms": [v, u]}
    density = sum((Fraction(1, s.step) for s in streams), Fraction(0))
    return {"accepted": True, "occupied_density": str(density)}


@dataclass(frozen=True)
class ResonantAtom:
    """Width q**residue / denominator, q=p**(-e/h)."""
    residue: int
    denominator: int

    def __post_init__(self) -> None:
        nonnegative_int(self.residue, "residue")
        positive_int(self.denominator, "denominator")


def resonant_certificate(p: int, e: int, h: int,
                         atoms: Iterable[ResonantAtom]) -> dict:
    """Colored prime-adic Hall certificate with an explicit zero on rejection."""
    for name, value in (("p", p), ("e", e), ("h", h)):
        positive_int(value, name)
    if not is_prime(p):
        raise ValueError("p must be prime")
    if gcd(e, h) != 1:
        raise ValueError("e/h must be reduced")
    atoms = list(atoms)
    channels: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
    for i, atom in enumerate(atoms):
        if atom.residue >= h:
            raise ValueError("residue is outside 0,...,h-1")
        channels[atom.residue].append((valuation(atom.denominator, p) // e,
                                       i, atom.denominator))
    assignments = []
    for residue, channel in sorted(channels.items()):
        channel.sort()
        for rank, (deadline, index, denominator) in enumerate(channel):
            if deadline < rank:
                prefix = channel[:rank + 1]
                multiple = lcm(*(row[2] for row in prefix))
                order = valuation(multiple, p) // e + 1
                require(order < len(prefix), "invalid rejection multiplicities")
                return {"accepted": False, "kind": "hall_violation",
                        "residue": residue, "deadline": deadline,
                        "factor_indices": [row[1] for row in prefix],
                        "zero_multiplier": multiple, "source_zero_order": order,
                        "factor_zero_order_at_least": len(prefix)}
            divisor = p ** (e * rank)
            require(denominator % divisor == 0, "invalid positive assignment")
            assignments.append({"factor": index, "source_level": residue + h * rank,
                                "digit_count": denominator // divisor})
    return {"accepted": True, "assignments": sorted(assignments, key=lambda d: d["factor"])}


def brute_matching(deadlines: tuple[int, ...]) -> bool:
    """Independent exponential backtracking, used only on tiny test families."""
    def visit(i: int, used: frozenset[int]) -> bool:
        if i == len(deadlines):
            return True
        return any(visit(i + 1, used | {slot})
                   for slot in range(deadlines[i] + 1) if slot not in used)
    return visit(0, frozenset())


def uniform_moment(k: int) -> Fraction:
    return Fraction(0) if k % 2 else Fraction(1, (2 ** k) * (k + 1))


def split_moment(n: int, k: int) -> Fraction:
    digit = [Fraction(2 * j - n + 1, 2 * n) for j in range(n)]
    return sum((Fraction(comb(k, r)) * uniform_moment(r) / n ** r
                * sum((x ** (k-r) for x in digit), Fraction(0)) / n
                for r in range(k+1)), Fraction(0))


def run_tests() -> dict:
    counts: dict[str, int] = defaultdict(int)
    # Exact digit identity, including odd moments and the degenerate n=1 case.
    for n in range(1, 41):
        for k in range(15):
            require(split_moment(n, k) == uniform_moment(k), "digit moment mismatch")
            counts["uniform_digit_moment_identities"] += 1
    # Direct symbolic zero collisions versus the distinct-level certificate.
    choices = [Atom(k, n) for k in range(4) for n in range(1, 6)]
    for length in range(5):
        for atoms in combinations_with_replacement(choices, length):
            cert = nonresonant_certificate(atoms)
            expected = len({a.level for a in atoms}) == length
            require(cert["accepted"] == expected, "simple-zero criterion mismatch")
            if not expected:
                i, j = cert["indices"]
                z = cert["zero_multiplier"]
                require(z % atoms[i].denominator == z % atoms[j].denominator == 0,
                        "double-zero witness is not common")
            counts["nonresonant_families"] += 1
    # CRT criterion against literal enumeration over one full common period.
    progressions = list(product(range(9), range(1, 10)))
    for (a, m), (b, n) in product(progressions, repeat=2):
        got = first_intersection(a, m, b, n)
        limit = max(a, b) + lcm(m, n)
        common = [x for x in range(max(a, b), limit + 1)
                  if (x-a) % m == 0 and (x-b) % n == 0]
        expected = common[0] if common else None
        require(got == expected, "CRT earliest intersection mismatch")
        counts["crt_pairs"] += 1
    for triple in combinations_with_replacement(progressions, 3):
        streams = [Stream(a, 1, m, 1) for a, m in triple]
        cert = stream_certificate(streams)
        if cert["accepted"]:
            require(Fraction(cert["occupied_density"]) <= 1,
                    "disjoint progressions violate density bound")
        counts["three_stream_families"] += 1
    # Prime-power channel theorem versus a completely separate matching search.
    for p, e in product((2, 3, 5), (1, 2, 3)):
        for length in range(5):
            for ns in combinations_with_replacement(range(1, 17), length):
                atoms = [ResonantAtom(0, n) for n in ns]
                cert = resonant_certificate(p, e, 1, atoms)
                expected = brute_matching(tuple(valuation(n, p) // e for n in ns))
                require(cert["accepted"] == expected, "Hall/matching mismatch")
                counts["prime_power_families"] += 1
    # Independence of rational-equivalence channels, with reduced e/h.
    choices = [ResonantAtom(r, n) for r in range(3) for n in (1, 2, 4, 8)]
    for length in range(5):
        for atoms in combinations_with_replacement(choices, length):
            cert = resonant_certificate(2, 2, 3, atoms)
            expected = all(brute_matching(tuple(valuation(a.denominator, 2)//2
                                                for a in atoms if a.residue == r))
                           for r in range(3))
            require(cert["accepted"] == expected, "colored Hall mismatch")
            counts["colored_resonant_families"] += 1
    # Exact finite orbits of cross-geometric candidates using rational p-exponents.
    # If c=p^-g, rho=p^-f/ell, then c*rho^j=p^-(g+f*j/ell).
    for e, h in product(range(1, 6), range(1, 7)):
        if gcd(e, h) != 1:
            continue
        for ell in range(1, h+1):
            if h % ell:
                continue
            for f in range(1, 9):
                if gcd(f, ell) != 1:
                    continue
                for g in range(4):
                    residues, exponents = [], []
                    for j in range(ell):
                        exponent = Fraction(g) + Fraction(f*j, ell)
                        possible = [(r, exponent - Fraction(e*r, h))
                                    for r in range(h)
                                    if (exponent - Fraction(e*r, h)).denominator == 1]
                        require(len(possible) == 1, "orbit residue is not unique")
                        r, diff = possible[0]
                        residues.append(r)
                        exponents.append(diff.numerator)
                    require(len(set(residues)) == ell, "minimal orbit repeats a channel")
                    expected = min(exponents) >= 0 and f >= e
                    # Independent verification over enough returns to expose f<e.
                    returns = max(12, max(exponents, default=0) + 2)
                    direct = all(exponents[j] >= 0 and
                                 all(exponents[j] + f*k >= e*k for k in range(returns))
                                 for j in range(ell))
                    require(direct == expected, "finite-orbit cross-law mismatch")
                    counts["resonant_geometric_orbits"] += 1
    # Deliberate invalid inputs must be rejected, not silently normalized.
    invalid = [lambda: Atom(-1, 2), lambda: Atom(0, 0),
               lambda: Stream(0, 1, 0, 1),
               lambda: resonant_certificate(4, 1, 1, []),
               lambda: resonant_certificate(2, 2, 2, []),
               lambda: resonant_certificate(2, 1, 2, [ResonantAtom(2, 1)])]
    for fn in invalid:
        try:
            fn()
        except ValueError:
            counts["invalid_input_checks"] += 1
        else:
            raise AssertionError("invalid input was accepted")
    examples = {
        "generic_even_odd": stream_certificate([Stream(0, 1, 2, 1), Stream(1, 1, 2, 1)]),
        "generic_density_not_sufficient": stream_certificate([Stream(0, 1, 2, 1), Stream(0, 7, 3, 2)]),
        "resonant_base4_rejection": resonant_certificate(2, 2, 3,
                                    [ResonantAtom(0, 2), ResonantAtom(0, 3)]),
        "resonant_base4_acceptance": resonant_certificate(2, 2, 3,
                                    [ResonantAtom(0, 4), ResonantAtom(0, 3)]),
        "dyadic_rational_pair": resonant_certificate(2, 1, 1,
                                    [ResonantAtom(0, 2), ResonantAtom(0, 3)]),
        "fifth_root_geometric_orbit": [[0, 2], [3, 1], [1, 4], [4, 2], [2, 8]],
    }
    return {"status": "PASS", "arithmetic": "exact integers and fractions",
            "scope": "finite certificate tests, not formal verification of analytic theorems",
            "counts": dict(sorted(counts.items())), "total_checks": sum(counts.values()),
            "examples": examples}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.rerun.json"))
    args = parser.parse_args()
    receipt = run_tests()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="\n") as out:
        json.dump(receipt, out, indent=2, sort_keys=True)
        out.write("\n")
    print(json.dumps({"status": receipt["status"], "counts": receipt["counts"],
                      "total_checks": receipt["total_checks"]}, indent=2))


if __name__ == "__main__":
    main()
