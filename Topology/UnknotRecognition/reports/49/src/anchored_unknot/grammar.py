"""Small exact binary word circuits. No reduction, hashing of word values, or expansion.

MIT-0. Concatenation interning is structural, not a word-equality oracle.
"""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import json
from typing import Iterable


class ResourceLimit(RuntimeError):
    pass


def strict_int(value: object, name: str = "integer") -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer, not {type(value).__name__}")
    return value


class Arena:
    def __init__(self, max_nodes: int = 2_000_000):
        self.rules: list[tuple] = [('e',)]
        self.lengths = [0]
        self._intern: dict[tuple, int] = {('e',): 0}
        self.max_nodes = max_nodes
        self.stats: dict[str, int] = {}

    def tick(self, n: int = 1) -> None:
        self.stats['work'] = self.stats.get('work', 0) + n

    def _add(self, rule: tuple, length: int) -> int:
        found = self._intern.get(rule)
        if found is not None:
            return found
        if len(self.rules) >= self.max_nodes:
            raise ResourceLimit("grammar-node limit")
        node = len(self.rules)
        self.rules.append(rule)
        self.lengths.append(length)
        self._intern[rule] = node
        return node

    def letter(self, x: int) -> int:
        strict_int(x)
        if not x:
            raise ValueError("zero is not a letter")
        return self._add(('t', x), 1)

    def concat(self, left: int, right: int) -> int:
        if left == 0:
            return right
        if right == 0:
            return left
        return self._add(('c', left, right), self.lengths[left] + self.lengths[right])

    def power(self, root: int, exponent: int) -> int:
        strict_int(exponent)
        if exponent < 0:
            raise ValueError("power takes a nonnegative exponent")
        result, base = 0, root
        while exponent:
            if exponent & 1:
                result = self.concat(result, base)
            exponent >>= 1
            if exponent:
                base = self.concat(base, base)
        return result

    def signed_power(self, generator: int, exponent: int) -> int:
        if not exponent:
            return 0
        return self.power(self.letter(generator if exponent > 0 else -generator), abs(exponent))

    def word(self, letters: Iterable[int]) -> int:
        root = 0
        for x in letters:
            root = self.concat(root, self.letter(x))
        return root

    def _reachable(self, roots: Iterable[int]) -> list[int]:
        seen = {0}
        pending = list(roots)
        while pending:
            v = pending.pop()
            if v in seen:
                continue
            seen.add(v)
            rule = self.rules[v]
            if rule[0] == 'c':
                pending.extend(rule[1:])
        return sorted(seen - {0})

    def expand(self, root: int, cap: int = 1_000_000) -> tuple[int, ...]:
        if self.lengths[root] > cap:
            raise ResourceLimit("literal expansion preflight")
        out, pending = [], [root]
        while pending:
            node = pending.pop()
            rule = self.rules[node]
            if rule[0] == 't':
                out.append(rule[1])
            elif rule[0] == 'c':
                pending.extend((rule[2], rule[1]))
        return tuple(out)


@dataclass(frozen=True)
class Source:
    generators: tuple[int, ...]
    rules: tuple[tuple, ...]
    roots: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.generators or any(type(g) is not int or g <= 0 for g in self.generators):
            raise ValueError("positive integer generators required")
        if tuple(sorted(set(self.generators))) != self.generators:
            raise ValueError("generators must be sorted and distinct")
        if not self.rules or self.rules[0] != ('e',):
            raise ValueError("rule zero must be empty")
        gs = set(self.generators)
        for i, rule in enumerate(self.rules[1:], 1):
            if len(rule) == 2 and rule[0] == 't':
                if type(rule[1]) is not int or abs(rule[1]) not in gs:
                    raise ValueError("unknown letter")
            elif len(rule) == 3 and rule[0] == 'c':
                if any(type(c) is not int or not 0 <= c < i for c in rule[1:]):
                    raise ValueError("circuit is not topologically ordered")
            else:
                raise ValueError("bad circuit rule")
        if any(type(v) is not int or not 0 <= v < len(self.rules) for v in self.roots):
            raise ValueError("invalid source root")

    @classmethod
    def from_arena(cls, arena: Arena, roots: Iterable[int], generators: Iterable[int]) -> 'Source':
        roots = tuple(roots)
        mapping = {0: 0}
        rules = [('e',)]
        for old in arena._reachable(roots):
            rule = arena.rules[old]
            mapping[old] = len(rules)
            rules.append(rule if rule[0] == 't' else ('c', mapping[rule[1]], mapping[rule[2]]))
        return cls(tuple(sorted(generators)), tuple(rules), tuple(mapping[v] for v in roots))

    def payload(self) -> dict:
        return {'generators': list(self.generators), 'rules': [list(x) for x in self.rules],
                'roots': list(self.roots)}

    @classmethod
    def from_payload(cls, payload: dict) -> 'Source':
        if type(payload) is not dict or set(payload) != {'generators', 'rules', 'roots'}:
            raise ValueError("invalid source schema")
        return cls(tuple(payload['generators']), tuple(tuple(x) for x in payload['rules']),
                   tuple(payload['roots']))

    @property
    def digest(self) -> str:
        raw = json.dumps(self.payload(), separators=(',', ':'), sort_keys=True).encode()
        return hashlib.sha256(raw).hexdigest()

    def lengths(self) -> list[int]:
        vals = [0]
        for rule in self.rules[1:]:
            vals.append(1 if rule[0] == 't' else vals[rule[1]] + vals[rule[2]])
        return vals

    @property
    def max_length(self) -> int:
        vals = self.lengths()
        return max([1] + [vals[v] for v in self.roots])

    def exponent_matrix(self) -> list[list[int]]:
        index = {g: i for i, g in enumerate(self.generators)}
        r = len(index)
        vals = [[0] * r]
        for rule in self.rules[1:]:
            if rule[0] == 't':
                v = [0] * r
                v[index[abs(rule[1])]] = 1 if rule[1] > 0 else -1
            else:
                v = [a + b for a, b in zip(vals[rule[1]], vals[rule[2]])]
            vals.append(v)
        return [vals[v] for v in self.roots]

    def materialize(self, images: dict[int, tuple[int, int]], dead: set[int],
                    arena: Arena | None = None) -> tuple[Arena, list[int]]:
        arena = arena if arena is not None else Arena()
        mapped = [0]
        powers = {}
        for rule in self.rules[1:]:
            if rule[0] == 't':
                x = rule[1]
                target, k = images[abs(x)]
                k = k if x > 0 else -k
                key = target, k
                if key not in powers:
                    powers[key] = arena.signed_power(target, k)
                mapped.append(powers[key])
            else:
                mapped.append(arena.concat(mapped[rule[1]], mapped[rule[2]]))
        roots = [0 if i in dead else mapped[v] for i, v in enumerate(self.roots)]
        return arena, roots
