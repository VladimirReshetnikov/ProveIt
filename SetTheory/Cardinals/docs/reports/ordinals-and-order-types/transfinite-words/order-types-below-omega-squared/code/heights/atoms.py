#!/usr/bin/env python3
"""Canonical bounded-height indecomposable transfinite words.

Python 3.9+, standard library only. No finite truncation of an ordinal is used.
The mathematical specification and proof are in the accompanying article.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Iterator, Optional, Sequence, Tuple


def popcount(mask: int) -> int:
    return bin(mask).count("1")


def indices(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class FinitePoset:
    """A finite poset, given by its reflexive order matrix."""
    labels: Tuple[str, ...]
    relation: Tuple[Tuple[bool, ...], ...]

    def __post_init__(self) -> None:
        n = len(self.labels)
        if len(set(self.labels)) != n:
            raise ValueError("Labels must be distinct.")
        if len(self.relation) != n or any(len(row) != n for row in self.relation):
            raise ValueError("The order matrix must be square and match the labels.")
        for i in range(n):
            if not self.relation[i][i]:
                raise ValueError("The order must be reflexive.")
            for j in range(n):
                if i != j and self.relation[i][j] and self.relation[j][i]:
                    raise ValueError("The order must be antisymmetric.")
                if self.relation[i][j]:
                    for k in range(n):
                        if self.relation[j][k] and not self.relation[i][k]:
                            raise ValueError("The order must be transitive.")

    @classmethod
    def chain(cls, n: int) -> FinitePoset:
        if n < 0:
            raise ValueError("Alphabet size must be nonnegative.")
        return cls(tuple(map(str, range(n))),
                   tuple(tuple(i <= j for j in range(n)) for i in range(n)))

    @classmethod
    def antichain(cls, n: int) -> FinitePoset:
        if n < 0:
            raise ValueError("Alphabet size must be nonnegative.")
        return cls(tuple(map(str, range(n))),
                   tuple(tuple(i == j for j in range(n)) for i in range(n)))


@dataclass(frozen=True)
class Atom:
    height: int
    letter: Optional[int] = None
    children: Tuple[int, ...] = ()


class AtomPoset:
    """A_{<k}(P), initially k=1. Atom identifiers stay stable as k increases."""

    def __init__(self, alphabet: FinitePoset) -> None:
        self.alphabet = alphabet
        self.atoms = [Atom(0, i) for i in range(len(alphabet.labels))]
        self.k = 1
        self._order_cache = {}

    def le(self, i: int, j: int) -> bool:
        key = (i, j)
        if key in self._order_cache:
            return self._order_cache[key]
        x, y = self.atoms[i], self.atoms[j]
        if x.letter is not None:
            if y.letter is not None:
                ans = self.alphabet.relation[x.letter][y.letter]
            else:
                ans = any(self.le(i, b) for b in y.children)
        elif y.letter is not None:
            ans = False
        else:
            ans = all(any(self.le(a, b) for b in y.children) for a in x.children)
        self._order_cache[key] = ans
        return ans

    def matrix(self) -> Tuple[Tuple[bool, ...], ...]:
        n = len(self.atoms)
        return tuple(tuple(self.le(i, j) for j in range(n)) for i in range(n))

    def _comparability_masks(self) -> list[int]:
        n = len(self.atoms)
        return [sum(1 << j for j in range(n) if self.le(i, j) or self.le(j, i))
                for i in range(n)]

    def antichains(self) -> Iterator[Tuple[int, ...]]:
        """Enumerate all antichains, including empty, exactly once."""
        masks = self._comparability_masks()

        def visit(mask: int, chosen: Tuple[int, ...]) -> Iterator[Tuple[int, ...]]:
            if not mask:
                yield chosen
                return
            bit = mask & -mask
            i = bit.bit_length() - 1
            yield from visit(mask ^ bit, chosen)
            yield from visit(mask & ~masks[i], chosen + (i,))

        yield from visit((1 << len(self.atoms)) - 1, ())

    def count_ideals(self) -> int:
        """Count via independent sets of the comparability graph."""
        masks = self._comparability_masks()

        @lru_cache(None)
        def count(mask: int) -> int:
            if not mask:
                return 1
            i = max(indices(mask), key=lambda j: popcount(mask & masks[j]))
            return count(mask & ~(1 << i)) + count(mask & ~masks[i])

        return count((1 << len(self.atoms)) - 1)

    def count_ideals_direct(self) -> int:
        """Independent algorithm: split ideals by inclusion of an element.

        Excluding x removes its upset; including x fixes its downset.
        This algorithm does not enumerate or count antichains.
        """
        n = len(self.atoms)
        down = [sum(1 << j for j in range(n) if self.le(j, i)) for i in range(n)]
        up = [sum(1 << j for j in range(n) if self.le(i, j)) for i in range(n)]

        @lru_cache(None)
        def count(mask: int) -> int:
            if not mask:
                return 1
            i = max(indices(mask), key=lambda j:
                    (min(popcount(mask & down[j]), popcount(mask & up[j])),
                     popcount(mask & (down[j] | up[j]))))
            return count(mask & ~up[i]) + count(mask & ~down[i])

        return count((1 << n) - 1)

    def extend(self, cap: int = 5000) -> None:
        """Append exactly the atoms of height k, and increment k.

        The preflight cardinality cap prevents accidentally materializing a
        tower-sized object. Counting itself can still be exponential.
        """
        next_count = len(self.alphabet.labels) + self.count_ideals() - 1
        if next_count > cap:
            raise ValueError(f"Next atom poset has {next_count} elements; cap={cap}.")
        children = [s for s in self.antichains()
                    if s and max(self.atoms[i].height for i in s) == self.k - 1]
        self.atoms.extend(Atom(self.k, None, s) for s in children)
        self.k += 1
        if len(self.atoms) != next_count:
            raise AssertionError("Canonical enumeration and ideal recurrence disagree.")

    def expression(self, i: int) -> str:
        a = self.atoms[i]
        if a.letter is not None:
            return self.alphabet.labels[a.letter]
        return "Omega{" + ",".join(self.expression(j) for j in a.children) + "}"

    def export(self) -> dict:
        return {
            "k": self.k,
            "alphabet": {"labels": self.alphabet.labels,
                         "relation": self.alphabet.relation},
            "atoms": [{"id": i, "height": a.height, "letter": a.letter,
                       "children": a.children, "expression": self.expression(i)}
                      for i, a in enumerate(self.atoms)],
            "relation": self.matrix(),
        }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--kind", choices=("chain", "antichain"), default="antichain")
    p.add_argument("--size", type=int, default=2)
    p.add_argument("--k", type=int, default=3)
    p.add_argument("--poset-json", type=Path,
                   help="JSON with labels and a full reflexive relation matrix.")
    p.add_argument("--cap", type=int, default=5000)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    if args.k < 1:
        p.error("k must be positive")
    if args.poset_json:
        obj = json.loads(args.poset_json.read_text(encoding="utf-8"))
        base = FinitePoset(tuple(obj["labels"]),
                           tuple(tuple(bool(x) for x in row) for row in obj["relation"]))
    else:
        base = getattr(FinitePoset, args.kind)(args.size)
    atoms = AtomPoset(base)
    for _ in range(1, args.k):
        atoms.extend(args.cap)
    result = atoms.export()
    result["N_k"] = len(atoms.atoms)
    result["J"] = atoms.count_ideals()
    result["J_independent"] = atoms.count_ideals_direct()
    if result["J"] != result["J_independent"]:
        raise AssertionError("Independent ideal counts disagree.")
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
