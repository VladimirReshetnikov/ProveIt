"""Validated, immutable word DAGs. No statement about a knot is inferred here.

Node 0 is the identity, ('t', g) is a signed generator, and ('c', a, b)
is concatenation. Children must have smaller ids. Presentations use equality
pairs (left_root, right_root), so either side can stay compressed.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable
import hashlib
import json


class LimitExceeded(RuntimeError):
    """An inconclusive resource interruption, never a negative algebraic answer."""


@dataclass(frozen=True)
class Presentation:
    rank: int
    rules: tuple
    relations: tuple[tuple[int, int], ...]
    meridian_generators: bool = False  # provenance declaration, NOT a proof
    label: str = "untrusted presentation"

    def __post_init__(self):
        if type(self.meridian_generators) is not bool:
            raise ValueError("meridian_generators must be a Boolean declaration")
        if type(self.rank) is not int or self.rank < 1:
            raise ValueError("rank must be a positive integer")
        if not self.rules or self.rules[0] is not None:
            raise ValueError("node zero must be None (the identity)")
        for i, rule in enumerate(self.rules[1:], 1):
            if not isinstance(rule, tuple) or not rule:
                raise ValueError("rules must be tuples")
            if rule[0] == 't' and len(rule) == 2:
                g = rule[1]
                if type(g) is not int or not 1 <= abs(g) <= self.rank:
                    raise ValueError("terminal is not a surviving generator")
            elif rule[0] == 'c' and len(rule) == 3:
                if any(type(j) is not int or not 0 <= j < i for j in rule[1:]):
                    raise ValueError("non-topological child id")
            else:
                raise ValueError("unknown rule")
        for pair in self.relations:
            if (not isinstance(pair, tuple) or len(pair) != 2 or
                    any(type(j) is not int or not 0 <= j < len(self.rules) for j in pair)):
                raise ValueError("invalid relation roots")

    def live(self) -> tuple[int, ...]:
        pending = [x for pair in self.relations for x in pair]
        seen = set()
        while pending:
            v = pending.pop()
            if v == 0 or v in seen:
                continue
            seen.add(v)
            rule = self.rules[v]
            if rule[0] == 'c':
                pending.extend(rule[1:])
        return tuple(sorted(seen))

    def products(self) -> tuple[int, ...]:
        return tuple(v for v in self.live() if self.rules[v][0] == 'c')

    def to_dict(self) -> dict:
        return dict(rank=self.rank, rules=self.rules, relations=self.relations,
                    meridian_generators=self.meridian_generators, label=self.label)

    @classmethod
    def from_dict(cls, obj: dict) -> Presentation:
        return cls(obj['rank'], tuple(None if r is None else tuple(r) for r in obj['rules']),
                   tuple(tuple(p) for p in obj['relations']),
                   obj.get('meridian_generators', False), obj.get('label', 'untrusted'))

    def digest(self) -> str:
        return hashlib.sha256(json.dumps(self.to_dict(), sort_keys=True,
                                         separators=(',', ':')).encode()).hexdigest()


class Arena:
    """Small compatible word builder; inverses are cached DAGs, never expanded."""
    def __init__(self):
        self.rules = [None]
        self._intern = {}
        self._inverse = {0: 0}

    def intern(self, rule):
        if rule not in self._intern:
            self._intern[rule] = len(self.rules)
            self.rules.append(rule)
        return self._intern[rule]

    def letter(self, g: int) -> int:
        if type(g) is not int or not g:
            raise ValueError("nonzero integer letter required")
        return self.intern(('t', g))

    def concat(self, a: int, b: int) -> int:
        if not a:
            return b
        if not b:
            return a
        return self.intern(('c', a, b))

    def word(self, letters: Iterable[int]) -> int:
        layer = [self.letter(g) for g in letters]
        while len(layer) > 1:
            layer = [self.concat(layer[i], layer[i + 1]) if i + 1 < len(layer)
                     else layer[i] for i in range(0, len(layer), 2)]
        return layer[0] if layer else 0

    def inverse(self, v: int) -> int:
        stack = [(v, False)]
        while stack:
            w, ready = stack.pop()
            if w in self._inverse:
                continue
            rule = self.rules[w]
            if rule[0] == 't':
                out = self.letter(-rule[1])
            elif ready:
                out = self.concat(self._inverse[rule[2]], self._inverse[rule[1]])
            else:
                stack.append((w, True))
                stack.extend((u, False) for u in rule[1:])
                continue
            self._inverse[w] = out
            self._inverse[out] = w
        return self._inverse[v]

    def power(self, v: int, e: int) -> int:
        if e < 0:
            v, e = self.inverse(v), -e
        out = 0
        while e:
            if e & 1:
                out = self.concat(out, v)
            e >>= 1
            if e:
                v = self.concat(v, v)
        return out

    def presentation(self, rank, pairs, *, meridians=False, label='untrusted'):
        return Presentation(rank, tuple(self.rules), tuple(pairs), meridians, label)


def from_words(rank: int, pairs, *, meridians=False, label='untrusted') -> Presentation:
    a = Arena()
    roots = [(a.word(u), a.word(v)) for u, v in pairs]
    return a.presentation(rank, roots, meridians=meridians, label=label)


def export_word_arena(arena, roots, surviving_generators, *,
                      meridians=False, label='untrusted export') -> Presentation:
    """Read the maintained WordArena.rules protocol; export only live nodes.

    The caller MUST replay its topology/presentation certificate separately.
    We deliberately do not mutate the arena or reset any upstream budget.
    ``roots`` are relator words equal to the identity.
    """
    old = arena.rules
    if not old or old[0] is not None:
        raise ValueError("WordArena identity-node protocol mismatch")
    roots = tuple(roots)
    survivors = tuple(sorted(surviving_generators))
    if (not survivors or len(set(survivors)) != len(survivors) or
            any(type(g) is not int or g <= 0 for g in survivors)):
        raise ValueError("surviving generators must be distinct positive integers")
    rename = {g: i + 1 for i, g in enumerate(survivors)}
    seen, pending = set(), list(roots)
    while pending:
        v = pending.pop()
        if type(v) is not int or not 0 <= v < len(old):
            raise ValueError("invalid arena root/child")
        if not v or v in seen:
            continue
        seen.add(v)
        rule = old[v]
        if not isinstance(rule, tuple):
            raise ValueError("unknown WordArena rule layout")
        if len(rule) == 3 and rule[0] == 'c':
            if any(type(u) is not int or not 0 <= u < v for u in rule[1:]):
                raise ValueError("invalid WordArena topological order")
            pending.extend(rule[1:])
        elif len(rule) == 2 and rule[0] == 't':
            if type(rule[1]) is not int or abs(rule[1]) not in rename:
                raise ValueError("eliminated or invalid terminal survives")
        else:
            raise ValueError("unknown WordArena rule layout")
    mapping, rules = {0: 0}, [None]
    for v in sorted(seen):
        rule = old[v]
        if rule[0] == 't':
            g = rule[1]
            out = ('t', rename[abs(g)] * (1 if g > 0 else -1))
        else:
            out = ('c', mapping[rule[1]], mapping[rule[2]])
        mapping[v] = len(rules)
        rules.append(out)
    return Presentation(len(survivors), tuple(rules), tuple((mapping[v], 0) for v in roots),
                        meridians, label)
