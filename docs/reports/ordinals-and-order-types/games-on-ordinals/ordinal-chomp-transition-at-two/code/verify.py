#!/usr/bin/env python3
"""Verify a finite certificate for a low-Grundy spectral gap.

Python 3.10+, standard library only. Values 0,1,2 are exact; 3 denotes >=3.
The recurrence, its initialization, and the repeated COMPLETE state are checked.
No assertion depends on a bounded search being representative of later cases.
"""
from __future__ import annotations

import argparse
import json
from functools import lru_cache
from math import gcd
from pathlib import Path
from typing import Iterable


class Semigroup:
    def __init__(self, generators: Iterable[int]):
        self.generators = tuple(sorted(set(generators)))
        if not self.generators or any(n <= 0 for n in self.generators):
            raise ValueError("Generators must be positive integers.")
        if gcd(*self.generators) != 1:
            raise ValueError("A numerical semigroup needs coprime generators.")
        m = self.generators[0]
        membership = [True]
        run = 1
        n = 1
        # m consecutive members imply that every later integer is a member.
        while run < m:
            member = any(n >= a and membership[n-a] for a in self.generators)
            membership.append(member)
            run = run + 1 if member else 0
            n += 1
        self.gaps = tuple(i for i, member in enumerate(membership) if not member)
        if not self.gaps:
            raise ValueError("This checker handles nonempty gap sets only.")
        self.F = self.gaps[-1]
        self.gapset = frozenset(self.gaps)
        self.full = (1 << len(self.gaps)) - 1
        self.patterns = tuple(c for c in range(self.full + 1)
                              if self.is_gap_ideal(c))
        self.order = tuple(sorted(self.patterns, key=int.bit_count))
        self.cache = lru_cache(maxsize=None)(self._finite_value)

    def contains(self, n: int) -> bool:
        return n >= 0 and n not in self.gapset

    def decode(self, mask: int) -> frozenset[int]:
        return frozenset(g for i, g in enumerate(self.gaps) if mask >> i & 1)

    def encode(self, values: Iterable[int]) -> int:
        values = set(values)
        return sum(1 << i for i, g in enumerate(self.gaps) if g in values)

    def is_gap_ideal(self, mask: int) -> bool:
        chosen = self.decode(mask)
        return all(h in chosen for g in chosen for h in self.gaps
                   if self.contains(g-h))

    @staticmethod
    def mex_low(options: Iterable[int]) -> int:
        options = set(options)
        return next((g for g in range(3) if g not in options), 3)

    def _finite_value(self, position: tuple[int, ...]) -> int:
        return self.mex_low(self.cache(tuple(z for z in position
                                            if not self.contains(z-y)))
                            for y in position)

    def apery(self, b: int) -> tuple[int, ...]:
        if not self.contains(b):
            raise ValueError("The Apéry parameter must belong to S.")
        return tuple(n for n in range(b + self.F + 1)
                     if self.contains(n) and not self.contains(n-b))

    def finite_position(self, x: int, mask: int) -> tuple[int, ...]:
        return (tuple(n for n in range(x) if self.contains(n))
                + tuple(x + g for g in sorted(self.decode(mask))))

    def delta(self, d: int, mask: int) -> int:
        chosen = self.decode(mask)
        return self.encode(g for g in self.gaps if g < d or g-d in chosen)

    def cut(self, c: int, mask: int) -> int:
        return self.encode(g for g in self.decode(mask)
                           if not self.contains(g-c))

    def direct_row(self, x: int) -> dict[int, int]:
        return {c: self.cache(self.finite_position(x, c)) for c in self.patterns}

    def next_row(self, rows: dict[int, dict[int, int]], x: int,
                 far: set[int]) -> dict[int, int]:
        row = {}
        for mask in self.order:
            near = {rows[x-d][self.delta(d, mask)] for d in range(1, self.F+1)}
            tail = {row[self.cut(c, mask)] for c in self.decode(mask)}
            row[mask] = self.mex_low(far | near | tail)
        return row


def check(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    s = Semigroup(data["generators"])
    check(list(s.gaps) == data["gaps"], "Incorrect gap set.")
    check(list(s.patterns) == data["pattern_masks"], "Incorrect shape list.")
    start, end = data["row_start"], data["row_end"]
    left, right = data["state_repeat"]
    check(start == s.F+1 and end == right-1, "Incorrect row bounds.")
    check(left >= 2*s.F+1 and right > left, "Incorrect repeat bounds.")
    strings = data["rows"]
    check(len(strings) == end-start+1, "Wrong number of rows.")
    check(all(len(v) == len(s.patterns) and set(v) <= set("0123")
              for v in strings), "Bad row encoding.")
    certified = {x: dict(zip(s.patterns, map(int, strings[x-start])))
                 for x in range(start, end+1)}
    rows = {x: s.direct_row(x) for x in range(start, 2*s.F+1)}
    for x, row in rows.items():
        check(row == certified[x], f"Bad seed row {x}.")
    # These are ALL far moves at x=2F+1, including the move at 0.
    far = {s.cache(s.apery(y)) for y in range(s.F+1) if s.contains(y)} - {3}
    check(far == {0}, "The initial far spectrum is not {0}.")
    states = {}
    for x in range(2*s.F+1, end+2):
        states[x] = (tuple(sorted(far)),
                     tuple(tuple(rows[t][c] for c in s.patterns)
                           for t in range(x-s.F, x)))
        if x == end+1:
            break
        rows[x] = s.next_row(rows, x, far)
        check(rows[x] == certified[x], f"Bad recurrence row {x}.")
        outgoing_value = rows[x-s.F][s.full]
        if outgoing_value < 3:
            far.add(outgoing_value)
    check(states[left] == states[right], "The complete states do not repeat.")
    check(all(row[s.full] == 3 for row in rows.values()), "Low full-row value.")
    check(all(s.cache(s.apery(b)) == 3 for b in range(1, s.F+1)
              if s.contains(b)), "Low exceptional Apéry value.")
    check(s.apery(4) == tuple(data["apery_four"]), "Incorrect Apéry set at 4.")
    # The four-point diamond, including its playable bottom, has value 3.
    diamond = s.apery(4)
    check(len(diamond) == 4 and diamond[0] == 0, "Not a four-point remainder.")
    _, p, q, r = diamond
    check(not s.contains(q-p) and s.contains(r-p) and s.contains(r-q),
          "The remainder is not a diamond.")
    check(all(not s.contains(a-4) and not s.contains(4-a)
              for a in diamond[1:]), "The exceptional index is not detached.")
    check(all((s.contains(n) != s.contains(s.F-n)) for n in range(s.F+1)),
          "The semigroup is not symmetric.")
    print(f"PASS {s.generators}: gaps={s.gaps}; {len(s.patterns)} shapes")
    print(f"  {len(rows)} rows, {len(rows)*len(s.patterns)} entries; "
          f"state {left} = state {right}")
    print(f"  period {right-left} from row {left-s.F}; far spectrum {{0}}")
    print("  Every positive Apéry value is >=3; diamond value is 3.")
    return data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="*", type=Path)
    args = parser.parse_args()
    paths = args.certificates or sorted((Path(__file__).resolve().parents[1]
                                        / "certificates").glob("s4[0-9][0-9].json"))
    if not paths:
        parser.error("No certificates found.")
    for path in paths:
        verify(path)
    print("ALL FINITE CERTIFICATES VERIFIED.")


if __name__ == "__main__":
    main()
