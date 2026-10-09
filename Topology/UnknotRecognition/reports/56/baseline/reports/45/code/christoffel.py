"""Exact rank-two primitive-power queries on binary straight-line programs.

No knot verdict is returned by this module. A geometric producer and a checked
presentation trace must establish that a queried presentation is a knot group.
Only cyclically reduced roots are classified; normalization is a separate cost.
Node format matches fastunknot.WordArena: None, ('t', signed_letter), ('c', i, j).
This implementation supports letters +/-1 and +/-2.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from math import gcd
from typing import Callable, Sequence

Rule = tuple | None

class InputError(ValueError):
    """Malformed input or a violated algebraic precondition."""

class ResourceLimit(RuntimeError):
    """The query is inconclusive, never negative, on resource exhaustion."""

@dataclass(frozen=True)
class Limits:
    max_nodes: int = 200_000
    max_bits: int = 100_000

@dataclass(frozen=True)
class Meta:
    counts: tuple[int, int, int, int]
    first: int
    last: int
    reduced: bool
    length: int

    @property
    def exponents(self) -> tuple[int, int]:
        a, A, b, B = self.counts
        return a-A, b-B

    @property
    def coherent(self) -> bool:
        a, A, b, B = self.counts
        return not (a and A or b and B)

    @property
    def cyclic(self) -> bool:
        return self.reduced and (not self.length or self.first != -self.last)

@dataclass(frozen=True)
class PowerCertificate:
    root: int
    u: int
    v: int
    exponent: int
    width: int

    def json(self) -> dict:
        # Hex strings avoid Python's decimal-string digit limit.
        return dict(root=self.root, u=hex(self.u), v=hex(self.v),
                    exponent=hex(self.exponent), width=hex(self.width))

@dataclass(frozen=True)
class Answer:
    status: str
    reason: str
    certificate: PowerCertificate | None = None


def _integer(x: object) -> bool:
    return type(x) is int


def inspect(rules: Sequence[Rule], *, limits: Limits = Limits(),
            check: Callable[[], None] = lambda: None) -> list[Meta]:
    """Validate all supplied nodes; charge the entire supplied grammar."""
    if not rules or rules[0] is not None:
        raise InputError('node zero must be the empty word')
    if (not _integer(limits.max_nodes) or limits.max_nodes < 1 or
        not _integer(limits.max_bits) or limits.max_bits < 1):
        raise InputError('positive integer resource limits required')
    if len(rules) > limits.max_nodes:
        raise ResourceLimit('node limit')
    out = [Meta((0, 0, 0, 0), 0, 0, True, 0)]
    positions = {1: 0, -1: 1, 2: 2, -2: 3}
    for index in range(1, len(rules)):
        check()
        rule = rules[index]
        if not isinstance(rule, (tuple, list)):
            raise InputError('invalid node')
        if len(rule) == 2 and rule[0] == 't':
            x = rule[1]
            if not _integer(x) or x not in positions:
                raise InputError('rank-two signed letters required')
            c = [0]*4
            c[positions[x]] = 1
            item = Meta(tuple(c), x, x, True, 1)
        elif len(rule) == 3 and rule[0] == 'c':
            i, j = rule[1:]
            if not all(_integer(t) and 0 <= t < index for t in (i, j)):
                raise InputError('concatenations must point backwards')
            x, y = out[i], out[j]
            c = tuple(a+b for a, b in zip(x.counts, y.counts))
            good = x.reduced and y.reduced and (
                not x.length or not y.length or x.last != -y.first)
            item = Meta(c, x.first or y.first, y.last or x.last,
                        good, x.length+y.length)
        else:
            raise InputError('unknown node form')
        if item.length.bit_length() > limits.max_bits:
            raise ResourceLimit('expanded-length bit limit')
        out.append(item)
    check()
    return out


def profiles(rules: Sequence[Rule], weights: tuple[int, int], *,
             check: Callable[[], None] = lambda: None) -> list[tuple[int, int, int]]:
    """On validated rules return (total, minimum-prefix, maximum-prefix)."""
    out = [(0, 0, 0)]
    for rule in rules[1:]:
        check()
        if rule[0] == 't':
            x = rule[1]
            t = weights[abs(x)-1] * (1 if x > 0 else -1)
            out.append((t, min(0, t), max(0, t)))
        else:
            t, low, high = out[rule[1]]
            s, lo, hi = out[rule[2]]
            out.append((t+s, min(low, t+lo), max(high, t+hi)))
    check()
    return out


def classify(rules: Sequence[Rule], root: int, *, limits: Limits = Limits(),
             check: Callable[[], None] = lambda: None) -> Answer:
    meta = inspect(rules, limits=limits, check=check)
    if not _integer(root) or not 0 <= root < len(rules):
        raise InputError('invalid root')
    m = meta[root]
    if not m.cyclic:
        raise InputError('root must already be freely and cyclically reduced')
    if not m.length:
        return Answer('NOT_PRIMITIVE_POWER', 'empty word')
    if not m.coherent:
        return Answer('NOT_PRIMITIVE_POWER', 'a generator occurs with both signs')
    a, b = m.exponents
    d = gcd(abs(a), abs(b))
    u, v = a//d, b//d
    _, low, high = profiles(rules, (v, -u), check=check)[root]
    width = high-low
    if width != abs(u)+abs(v)-1:
        return Answer('NOT_PRIMITIVE_POWER', 'nonminimal primitive-slope width')
    cert = PowerCertificate(root, u, v, d, width)
    return Answer('PRIMITIVE_POWER', 'exact minimum-width certificate', cert)


def scan_aligned(rules: Sequence[Rule], roots: Sequence[int], *,
                 limits: Limits = Limits(),
                 check: Callable[[], None] = lambda: None) -> dict:
    """One shared profile pass for collinear nonzero exponent vectors.

    Returns algebraic evidence only. A zero-exponent nonempty word cannot be a
    primitive power. A noncollinear presentation is explicitly unsupported.
    Empty relators are retained in the returned indices but do not affect gcd.
    """
    meta = inspect(rules, limits=limits, check=check)
    if not all(_integer(r) and 0 <= r < len(rules) for r in roots):
        raise InputError('invalid roots')
    if any(not meta[r].cyclic for r in roots):
        raise InputError('all roots must be cyclically reduced')
    ray = None
    for r in roots:
        check()
        a, b = meta[r].exponents
        d = gcd(abs(a), abs(b))
        if d:
            u, v = a//d, b//d
            if u < 0 or u == 0 and v < 0:
                u, v = -u, -v
            ray = (u, v)
            break
    if ray is None:
        return dict(status='NO_NONZERO_EXPONENT_VECTOR', certificates=[], all_powers=False)
    u, v = ray
    if any(v*meta[r].exponents[0] != u*meta[r].exponents[1] for r in roots):
        return dict(status='NONCOLLINEAR', certificates=[], all_powers=False)
    prof = profiles(rules, (v, -u), check=check)
    certs = []
    nonempty = 0
    all_powers = True
    exponent_gcd = 0
    for slot, r in enumerate(roots):
        check()
        m = meta[r]
        if not m.length:
            continue
        nonempty += 1
        a, b = m.exponents
        d = gcd(abs(a), abs(b))
        width = prof[r][2]-prof[r][1]
        if d and m.coherent and width == abs(u)+abs(v)-1:
            c = PowerCertificate(r, a//d, b//d, d, width)
            certs.append((slot, c))
            exponent_gcd = gcd(exponent_gcd, d)
        else:
            all_powers = False
    return dict(status='ALIGNED', ray=ray, certificates=certs,
                all_powers=all_powers and bool(nonempty), exponent_gcd=exponent_gcd,
                profile_passes=1)


def aligned_group_type(rules: Sequence[Rule], roots: Sequence[int]) -> dict:
    """Exact on the supported family: F2, Z, or C_g * Z. Otherwise unsupported."""
    result = scan_aligned(rules, roots)
    metadata = inspect(rules)
    if all(not metadata[r].length for r in roots):
        return dict(status='CLASSIFIED', group='F2')
    if not result.get('all_powers'):
        return dict(status='UNSUPPORTED')
    g = result['exponent_gcd']
    return dict(status='CLASSIFIED', group='Z' if g == 1 else 'C_g * Z', g=g)


class Arena:
    """Small reference producer; it does not implement compressed cancellation."""
    def __init__(self):
        self.rules: list[Rule] = [None]
        self.lengths = [0]
        self._intern: dict[tuple, int] = {}

    def _put(self, rule: tuple, length: int) -> int:
        if rule not in self._intern:
            self._intern[rule] = len(self.rules)
            self.rules.append(rule)
            self.lengths.append(length)
        return self._intern[rule]

    def letter(self, x: int) -> int:
        if not _integer(x) or x not in (1, -1, 2, -2):
            raise InputError('invalid letter')
        return self._put(('t', x), 1)

    def concat(self, i: int, j: int) -> int:
        if not i: return j
        if not j: return i
        return self._put(('c', i, j), self.lengths[i]+self.lengths[j])

    def from_word(self, word: Sequence[int]) -> int:
        nodes = [self.letter(x) for x in word]
        while len(nodes) > 1:
            nodes = [self.concat(nodes[i], nodes[i+1]) if i+1 < len(nodes) else nodes[i]
                     for i in range(0, len(nodes), 2)]
        return nodes[0] if nodes else 0

    def power(self, node: int, n: int) -> int:
        if not _integer(n) or n < 0:
            raise InputError('nonnegative exponent required')
        out = 0
        while n:
            if n & 1: out = self.concat(out, node)
            n >>= 1
            if n: node = self.concat(node, node)
        return out

    def substitute(self, root: int, images: dict[int, int]) -> int:
        old_size = len(self.rules)
        done = [0]*old_size
        for i in range(1, old_size):
            r = self.rules[i]
            done[i] = images[r[1]] if r[0] == 't' else self.concat(done[r[1]], done[r[2]])
        return done[root]

    def expand(self, root: int, cap: int = 1_000_000) -> tuple[int, ...]:
        if self.lengths[root] > cap:
            raise ResourceLimit('literal expansion cap')
        out, stack = [], [root]
        while stack:
            i = stack.pop()
            if not i: continue
            r = self.rules[i]
            if r[0] == 't': out.append(r[1])
            else: stack.extend((r[2], r[1]))
        return tuple(out)


def christoffel_slp(p: int, q: int) -> tuple[Arena, int]:
    """Euclidean Nielsen construction, O(log(p+q)) binary grammar nodes.

    Positive images are built in the original alphabet while Euclidean slope
    descent proceeds. This avoids repeatedly substituting the entire grammar.
    """
    if not all(_integer(t) and t >= 0 for t in (p, q)) or gcd(p, q) != 1:
        raise InputError('coprime nonnegative slope required')
    arena = Arena()
    a, b = arena.letter(1), arena.letter(2)
    while p and q:
        if p >= q:
            k, p = divmod(p, q)
            b = arena.concat(arena.power(a, k), b)
        else:
            k, q = divmod(q, p)
            a = arena.concat(a, arena.power(b, k))
    return arena, a if p else b


def fibonacci_slp(steps: int) -> tuple[Arena, int]:
    """Iterated positive Nielsen pair: U'=UV,V'=U. Every root is primitive."""
    if not _integer(steps) or steps < 0:
        raise InputError('nonnegative step count')
    arena = Arena()
    u, v = arena.letter(1), arena.letter(2)
    for _ in range(steps):
        u, v = arena.concat(u, v), u
    return arena, u
