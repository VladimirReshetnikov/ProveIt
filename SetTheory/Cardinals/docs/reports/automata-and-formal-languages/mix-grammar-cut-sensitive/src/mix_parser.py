#!/usr/bin/env python3
"""Exact cut-sensitive membership in Yuyama's canonical MIX tuple grammar.

Python 3.10+, standard library only. The article proves soundness, completeness,
and termination of the recurrence. This is not a proof-assistant formalization.

A tuple argument retains its component boundaries: ('a','accb','b') and
('aaccbb',) are different questions. Empty components may be omitted.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
from itertools import product
import json
from typing import Iterable

TupleWord = tuple[str, ...]
ALPHABET = 'abc'


def relabel(parts: TupleWord) -> TupleWord:
    """Canonicalize a global alphabet permutation by first occurrence."""
    mapping: dict[str, str] = {}
    result = []
    for part in parts:
        out = []
        for letter in part:
            if letter not in mapping:
                mapping[letter] = ALPHABET[len(mapping)]
            out.append(mapping[letter])
        result.append(''.join(out))
    return tuple(result)


def normalize(parts: TupleWord) -> TupleWord:
    """Remove empty slots and quotient by renaming and full reversal."""
    parts = tuple(part for part in parts if part)
    reverse = tuple(part[::-1] for part in parts[::-1])
    return min(relabel(parts), relabel(reverse))


class Parser:
    """Decide normalized A_r membership. Cache eviction affects speed only."""

    def __init__(self, r: int, cap: int | None = None) -> None:
        if not isinstance(r, int) or isinstance(r, bool) or r < 1:
            raise ValueError('Arity must be a positive integer.')
        if cap is not None and cap < 0:
            raise ValueError('Cache capacity must be nonnegative or None.')
        self.r = r
        self.f = lru_cache(maxsize=cap)(self._decide)

    def accepts(self, parts: Iterable[str]) -> bool:
        """Check a tuple; use accepts_word for a single word."""
        if isinstance(parts, str):
            raise TypeError('Pass a tuple of components, or use accepts_word.')
        parts = tuple(parts)
        if any(not isinstance(part, str) for part in parts):
            raise TypeError('Every component must be a string.')
        if any(letter not in ALPHABET for part in parts for letter in part):
            raise ValueError("The alphabet is exactly {'a', 'b', 'c'}.")
        return self._accept(parts)

    def accepts_word(self, word: str) -> bool:
        """Decide membership of a word in concat(A_r)."""
        return self.accepts((word,))

    def _accept(self, parts: TupleWord) -> bool:
        return self.f(normalize(parts))

    def _decide(self, parts: TupleWord) -> bool:
        if not parts:
            return True
        if len(parts) > self.r:
            return False
        word = ''.join(parts)
        n = len(word)
        if n % 3 or any(word.count(c) != n // 3 for c in ALPHABET):
            return False

        # Invert a wrap: remove one physical endpoint of each letter.
        # A one-letter component has only one physical endpoint, not two.
        endpoints: dict[str, list[tuple[int, int]]] = {c: [] for c in ALPHABET}
        for i, part in enumerate(parts):
            endpoints[part[0]].append((i, 0))
            if len(part) > 1:
                endpoints[part[-1]].append((i, len(part) - 1))
        for chosen in product(*(endpoints[c] for c in ALPHABET)):
            removed = [set() for _ in parts]
            for i, j in chosen:
                removed[i].add(j)
            child = tuple(''.join(c for j, c in enumerate(part)
                                  if j not in removed[i])
                          for i, part in enumerate(parts))
            if self._accept(child):
                return True

        # Invert a nonempty binary insertion. Each original component boundary
        # survives in the induced child tuples. Crucially, a prefix and suffix
        # exposed in the SAME component remain two separate outside components.
        starts: list[int] = []
        offset = 0
        for part in parts:
            starts.append(offset)
            offset += len(part)
        prefix = [(0, 0)]
        a = b = 0
        for c in word:
            a += (c == 'a') - (c == 'c')
            b += (c == 'b') - (c == 'c')
            prefix.append((a, b))
        for p in range(n):
            for q in range(p + 3, n + 1, 3):
                if q - p == n or prefix[p] != prefix[q]:
                    continue
                outside: list[str] = []
                inside: list[str] = []
                for part, start in zip(parts, starts):
                    lo = max(0, min(len(part), p - start))
                    hi = max(0, min(len(part), q - start))
                    if part[:lo]:
                        outside.append(part[:lo])
                    if part[lo:hi]:
                        inside.append(part[lo:hi])
                    if part[hi:]:
                        outside.append(part[hi:])
                if (len(outside) <= self.r and len(inside) <= self.r
                        and self._accept(tuple(inside))
                        and self._accept(tuple(outside))):
                    return True

        # Reverse one genuine merge. This is a backward search alternative,
        # NOT an assertion that accepted tuples are closed under splitting.
        if len(parts) < self.r:
            for i, part in enumerate(parts):
                for cut in range(1, len(part)):
                    finer = parts[:i] + (part[:cut], part[cut:]) + parts[i + 1:]
                    if self._accept(finer):
                        return True
        return False


def main() -> None:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('arity', type=int)
    cli.add_argument('components', nargs='*', help='No components means epsilon.')
    cli.add_argument('--cache-size', type=int, default=None)
    args = cli.parse_args()
    try:
        parser = Parser(args.arity, args.cache_size)
        result = parser.accepts(tuple(args.components))
    except (ValueError, TypeError) as exc:
        cli.error(str(exc))
    print(json.dumps({'arity': args.arity, 'components': args.components,
                      'accepted': result,
                      'cache': parser.f.cache_info()._asdict()}, indent=2))

if __name__ == '__main__':
    main()
