#!/usr/bin/env python3
"""Exact finite checks for Maximal_Width_Uniformization.tex.

These checks do not verify elementary embeddings, reflection, or consistency.
They verify the finite-edit arithmetic used in the paper on infinite sets of
natural numbers represented exactly as finite modifications of the even numbers.
No external dependencies; Python 3.10 or later.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Iterable


@dataclass(frozen=True)
class EvenModification:
    """The symmetric difference of {0, 2, 4, ...} and a finite toggle set."""

    toggles: frozenset[int] = frozenset()

    def __post_init__(self) -> None:
        if not isinstance(self.toggles, frozenset):
            raise TypeError("toggles must be a frozenset")
        if any(type(x) is not int or x < 0 for x in self.toggles):
            raise ValueError("toggle positions must be nonnegative integers")

    def contains(self, n: int) -> bool:
        return n >= 0 and ((n % 2 == 0) != (n in self.toggles))

    def prefix(self, length: int) -> tuple[int, ...]:
        if length < 0:
            raise ValueError("length must be nonnegative")
        values: list[int] = []
        n = 0
        while len(values) < length:
            if self.contains(n):
                values.append(n)
            n += 1
        return tuple(values)

    def difference(self, other: EvenModification) -> frozenset[int]:
        """Return the complete, finite difference: self minus other."""
        return frozenset(n for n in self.toggles ^ other.toggles if self.contains(n))

    def delete(self, values: Iterable[int]) -> EvenModification:
        removed = frozenset(values)
        if any(not self.contains(n) for n in removed):
            raise ValueError("all deleted values must belong to the set")
        return EvenModification(self.toggles ^ removed)


def charge(a: EvenModification, b: EvenModification) -> int:
    """chi_a(b) = insertions into a minus deletions from a."""
    return len(b.difference(a)) - len(a.difference(b))


def subsets(values: tuple[int, ...]) -> Iterable[frozenset[int]]:
    for size in range(len(values) + 1):
        for chosen in combinations(values, size):
            yield frozenset(chosen)


def require(condition: bool, message: str) -> None:
    # Unlike assert, this remains active when Python runs with -O.
    if not condition:
        raise AssertionError(message)


def main() -> None:
    sets = [EvenModification(u) for u in subsets(tuple(range(6)))]
    n_sets = len(sets)
    matrix = [[charge(a, b) for b in sets] for a in sets]
    counts: dict[str, int] = {}

    antisymmetry = 0
    cocycles = 0
    for i in range(n_sets):
        for j in range(n_sets):
            require(matrix[i][j] == -matrix[j][i], "antisymmetry failed")
            antisymmetry += 1
            for k in range(n_sets):
                require(matrix[i][k] == matrix[i][j] + matrix[j][k],
                        "finite-edit cocycle failed")
                cocycles += 1
    counts["charge antisymmetry identities"] = antisymmetry
    counts["charge cocycle identities"] = cocycles

    # For a fixed nonempty finite family B, compare its spectrum at every pair
    # of reference representatives. All sets here belong to one =* class.
    family_indices = tuple(range(0, n_sets, 3))
    base_changes = 0
    for i in range(n_sets):
        spectrum_i = {matrix[i][k] for k in family_indices}
        for j in range(n_sets):
            spectrum_j = {matrix[j][k] for k in family_indices}
            require(spectrum_j == {r - matrix[i][j] for r in spectrum_i},
                    "spectrum base-change law failed")
            base_changes += 1
    counts["spectrum base-change identities"] = base_changes

    deletions = 0
    tails = 0
    for i, a in enumerate(sets):
        first_three = a.prefix(3)
        for u in subsets(first_three):
            smaller = a.delete(u)
            for j, b in enumerate(sets):
                require(charge(smaller, b) == matrix[i][j] + len(u),
                        "reference deletion law failed")
                deletions += 1
        tail = a.delete((first_three[0],))
        require({charge(tail, sets[k]) for k in family_indices}
                == {matrix[i][k] + 1 for k in family_indices},
                "tail spectrum translation failed")
        tails += 1
    counts["reference deletion identities"] = deletions
    counts["tail spectrum translation identities"] = tails

    phase_partitions = 0
    for a in sets:
        tail = a.delete((a.prefix(1)[0],))
        for r in range(-6, 7):
            new_phase = {k for k in family_indices if charge(tail, sets[k]) == r}
            old_phase = {k for k in family_indices if charge(a, sets[k]) == r - 1}
            require(new_phase == old_phase, "reference-tail phase shift sign failed")
            phase_partitions += 1
    counts["reference-tail phase partition identities"] = phase_partitions


    prefixes = [a.prefix(32) for a in sets]
    coordinate_checks = 0
    for i, a in enumerate(sets):
        for j, b in enumerate(sets):
            r = len(a.difference(b))
            for n in range(24):
                require(prefixes[j][n] <= prefixes[i][n + r],
                        "deletion-budget coordinate inequality failed")
                coordinate_checks += 1
    counts["deletion-budget coordinate inequalities"] = coordinate_checks

    base = EvenModification()
    for r in range(-20, 21):
        toggles = (frozenset(2 * i for i in range(-r)) if r < 0 else
                   frozenset(2 * i + 1 for i in range(r)))
        require(charge(base, EvenModification(toggles)) == r,
                "prescribed integer charge construction failed")
    counts["prescribed integer charges (-20 through 20)"] = 41

    # Finite cyclic analogue only: invariance under +1 forces a subset to be
    # empty or the entire cycle. The paper's Z result is proved, not simulated.
    cyclic_checks = 0
    for modulus in range(2, 13):
        universe = frozenset(range(modulus))
        for subset in subsets(tuple(range(modulus))):
            translated = frozenset((r + 1) % modulus for r in subset)
            if subset == translated:
                require(not subset or subset == universe,
                        "cyclic translation saturation failed")
            cyclic_checks += 1
    counts["finite cyclic subset checks (moduli 2 through 12)"] = cyclic_checks

    print("FINITE-COMBINATORICS CHECKS: PASS")
    print("Representation: exact finite modifications of the infinite even set.")
    print(f"Reference sets: {n_sets}; toggle positions: 0 through 5.")
    for label, count in counts.items():
        print(f"  {label}: {count:,}")
    print(f"Total checks: {sum(counts.values()):,}")
    print("Scope: finite-edit arithmetic only. No large-cardinal theorem,")
    print("elementary embedding, reflection argument, or consistency claim")
    print("has been machine-verified by this script.")


if __name__ == "__main__":
    main()
