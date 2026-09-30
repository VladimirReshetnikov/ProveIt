#!/usr/bin/env python3
"""Exact order-free seeded-aTAM compiler; standard-library Python 3.10+.

The output represents P(w) = sum(row(w)**2 for row in rows).
Every row is affine with integer coefficients. Variables range over N.
The tile palette and finite domain are parameters of the *compiler*, not
arithmetic input variables of a fixed-arity universal polynomial.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable
import json

Point = tuple[int, int]
DIRS: tuple[Point, ...] = ((0, 1), (1, 0), (0, -1), (-1, 0))

@dataclass(frozen=True)
class Affine:
    coefficients: dict[int, int]
    constant: int = 0

    @staticmethod
    def lift(value: int | 'Affine') -> 'Affine':
        return value if isinstance(value, Affine) else Affine({}, value)

    def __add__(self, other: int | 'Affine') -> 'Affine':
        other = self.lift(other)
        d = dict(self.coefficients)
        for i, c in other.coefficients.items():
            d[i] = d.get(i, 0) + c
            if not d[i]:
                del d[i]
        return Affine(d, self.constant + other.constant)

    __radd__ = __add__

    def __neg__(self) -> 'Affine':
        return Affine({i: -c for i, c in self.coefficients.items()}, -self.constant)

    def __sub__(self, other: int | 'Affine') -> 'Affine':
        return self + (-self.lift(other))

    def __rsub__(self, other: int | 'Affine') -> 'Affine':
        return self.lift(other) + (-self)

    def __mul__(self, k: int) -> 'Affine':
        if not isinstance(k, int):
            raise TypeError('Affine rows permit multiplication by integers only')
        return Affine({i: k*c for i, c in self.coefficients.items() if k*c},
                      k*self.constant)

    __rmul__ = __mul__

    def evaluate(self, values: list[int]) -> int:
        return self.constant + sum(c*values[i] for i, c in self.coefficients.items())

    def json(self) -> dict:
        return {'constant': self.constant,
                'terms': [[i, c] for i, c in sorted(self.coefficients.items())]}

@dataclass
class TileSystem:
    # Palette entries are (north, east, south, west); tile IDs begin at one.
    tiles: tuple[tuple[str, str, str, str], ...]
    strengths: dict[str, int]
    temperature: int
    seed: dict[Point, int]

    def __post_init__(self) -> None:
        if self.temperature < 1:
            raise ValueError('Temperature must be positive')
        if not self.tiles or not self.seed:
            raise ValueError('This implementation requires a nonempty palette and seed')
        if any(type(g) is not int or g < 0 for g in self.strengths.values()):
            raise ValueError('Glue strengths must be nonnegative integers')
        if any(a < 1 or a > len(self.tiles) for a in self.seed.values()):
            raise ValueError('Invalid seed tile ID')
        if any(g and g not in self.strengths for t in self.tiles for g in t):
            raise ValueError('Unknown glue label')

    def glue(self, u: Point, b: int, v: Point, a: int) -> int:
        if not a or not b:
            return 0
        displacement = (v[0]-u[0], v[1]-u[1])
        if displacement not in DIRS:
            return 0
        side = DIRS.index(displacement)
        g = self.tiles[b-1][side]
        h = self.tiles[a-1][(side+2) % 4]
        return min(self.strengths.get(g, 0), self.temperature) if g == h else 0

    def support(self, state: dict[Point, int], v: Point, a: int) -> int:
        return sum(self.glue((v[0]+dx, v[1]+dy),
                             state.get((v[0]+dx, v[1]+dy), 0), v, a)
                   for dx, dy in DIRS)


def canonical_ranks(system: TileSystem, domain: tuple[Point, ...],
                    labels: tuple[int, ...]) -> dict[Point, int] | None:
    """Parallel closure, independent of arithmetic compiler."""
    target = dict(zip(domain, labels))
    if any(target.get(v) != a for v, a in system.seed.items()):
        return None
    if any(a < 0 or a > len(system.tiles) for a in labels):
        return None
    reached = dict(system.seed)
    ranks = {v: 0 for v in domain}
    for step in range(1, len(domain)+1):
        batch = {v: a for v, a in target.items() if a and v not in reached
                 and system.support(reached, v, a) >= system.temperature}
        if not batch:
            break
        reached.update(batch)
        ranks.update({v: step for v in batch})
    return ranks if len(reached) == sum(a != 0 for a in labels) else None


def sequential_states(system: TileSystem, domain: tuple[Point, ...]) -> set[tuple[int, ...]]:
    """Independent asynchronous enumeration, confined to the given domain."""
    start = tuple(system.seed.get(v, 0) for v in domain)
    found = {start}
    frontier = [start]
    while frontier:
        labels = frontier.pop()
        state = dict(zip(domain, labels))
        for i, v in enumerate(domain):
            if labels[i]:
                continue
            for a in range(1, len(system.tiles)+1):
                if system.support(state, v, a) >= system.temperature:
                    nxt = labels[:i] + (a,) + labels[i+1:]
                    if nxt not in found:
                        found.add(nxt)
                        frontier.append(nxt)
    return found


def halo(domain: Iterable[Point]) -> tuple[Point, ...]:
    d = set(domain)
    return tuple(sorted({(x+dx, y+dy) for x, y in d for dx, dy in DIRS} - d))


def terminal(system: TileSystem, domain: tuple[Point, ...], labels: tuple[int, ...]) -> bool:
    """Whole-grid terminality, including interior blanks and exterior halo."""
    state = dict(zip(domain, labels))
    return all(system.support(state, v, a) < system.temperature
               for v in tuple(domain) + halo(domain) if not state.get(v, 0)
               for a in range(1, len(system.tiles)+1))


class Compiler:
    def __init__(self, system: TileSystem, domain: Iterable[Point],
                 require_terminal: bool = False):
        self.system = system
        self.domain = tuple(sorted(set(domain)))
        if not set(system.seed) <= set(self.domain):
            raise ValueError('The domain must contain the seed')
        self.require_terminal = require_terminal
        self.names: list[str] = []
        self.recipes: list[Callable] = []
        self.rows: list[Affine] = []
        self.row_names: list[str] = []
        self._build()

    def new(self, name: str, recipe: Callable) -> Affine:
        index = len(self.names)
        if name in self.names:
            raise ValueError(f'Duplicate variable: {name}')
        self.names.append(name)
        self.recipes.append(recipe)
        return Affine({index: 1})

    def derived(self, name: str, expr: Affine) -> Affine:
        return self.new(name, lambda labels, ranks, w, expr=expr: expr.evaluate(w))

    def eq(self, name: str, left: int | Affine, right: int | Affine) -> None:
        self.rows.append(Affine.lift(left) - Affine.lift(right))
        self.row_names.append(name)

    def compare(self, name: str, x: Affine, y: Affine, M: int) -> Affine:
        c = self.new(name, lambda labels, ranks, w, x=x, y=y:
                     int(x.evaluate(w) < y.evaluate(w)))
        bar = self.derived(name+'.bar', 1-c)
        p = self.derived(name+'.p', y + M*bar - x - 1)
        r = self.derived(name+'.r', x + M*c - y)
        self.eq(name+'.boolean', c+bar, 1)
        self.eq(name+'.true', x+1+p, y+M*bar)
        self.eq(name+'.false', y+r, x+M*c)
        return c

    def conjunction(self, name: str, args: tuple[Affine, ...]) -> Affine:
        z = self.new(name, lambda labels, ranks, w, args=args:
                     int(all(a.evaluate(w) == 1 for a in args)))
        for i, a in enumerate(args):
            p = self.derived(f'{name}.p{i}', a-z)
            self.eq(f'{name}.upper{i}', z+p, a)
        r = self.derived(name+'.r', z+len(args)-1-sum(args))
        self.eq(name+'.lower', z+len(args)-1, sum(args)+r)
        return z

    def _build(self) -> None:
        S, D = self.system, self.domain
        N, q, tau = len(D), len(S.tiles), S.temperature
        seed = set(S.seed)
        nonseed = tuple(v for v in D if v not in seed)
        e: dict[tuple[Point, int], Affine] = {}
        t: dict[Point, Affine] = {}
        delta: dict[Point, Affine] = {}
        for v in D:
            for a in range(q+1):
                e[v, a] = self.new(f'e[{v},{a}]',
                                  lambda labels, ranks, w, v=v, a=a: int(labels[v] == a))
            self.eq(f'label[{v}]', sum(e[v, a] for a in range(q+1)), 1)
            if v in seed:
                self.eq(f'seed[{v}]', e[v, S.seed[v]], 1)
            delta[v] = 1-e[v, 0]
        for v in D:
            t[v] = self.new(f't[{v}]', lambda labels, ranks, w, v=v: ranks[v])
            u = self.derived(f'u[{v}]', N*delta[v]-t[v])
            self.eq(f'rank.upper[{v}]', t[v]+u, N*delta[v])
            if v in seed:
                self.eq(f'rank.seed[{v}]', t[v], 0)
            else:
                h = self.derived(f'h[{v}]', t[v]-delta[v])
                self.eq(f'rank.lower[{v}]', t[v], delta[v]+h)
        edges = [(u, v) for v in nonseed for u in D
                 if abs(u[0]-v[0])+abs(u[1]-v[1]) == 1]
        triples = [(u, v, b, a, S.glue(u, b, v, a))
                   for u, v in edges for b in range(1, q+1) for a in range(1, q+1)
                   if S.glue(u, b, v, a)]
        cut = {(u, v, j): self.compare(f'cut[{u},{v},{j}]', t[u]+j, t[v], N+2)
               for u, v in edges for j in (0, 1)}
        A = {v: Affine({}) for v in nonseed}
        B = {v: Affine({}) for v in nonseed}
        for u, v, b, a, g in triples:
            for j in (0, 1):
                z = self.conjunction(f'bond[{u},{v},{b},{a},{j}]',
                                     (e[u, b], e[v, a], cut[u, v, j]))
                (A if j == 0 else B)[v] += g*z
        for v in nonseed:
            lo = self.derived(f'activation.lo[{v}]', A[v]-tau*delta[v])
            hi = self.derived(f'activation.hi[{v}]', (tau-1)*delta[v]-B[v])
            self.eq(f'activation.enabled[{v}]', A[v], tau*delta[v]+lo)
            self.eq(f'activation.earliest[{v}]', B[v]+hi, (tau-1)*delta[v])
        J, K, s = len(triples), len(edges), len(seed)
        base_m = N*(q+6)-3*s+8*K+10*J
        base_l = 5*N-s+6*K+8*J
        assert (len(self.names), len(self.rows)) == (base_m, base_l)
        H = halo(D)
        if self.require_terminal:
            hypothetical = {(v, a): Affine({}) for v in nonseed for a in range(1, q+1)}
            for u, v, b, a, g in triples:
                z = self.conjunction(f'vacant[{u},{v},{b},{a}]', (e[v, 0], e[u, b]))
                hypothetical[v, a] += g*z
            for v in nonseed:
                for a in range(1, q+1):
                    total = hypothetical[v, a]
                    eta = self.derived(f'terminal[{v},{a}].slack', (tau-1)*e[v, 0]-total)
                    self.eq(f'terminal[{v},{a}]', total+eta, (tau-1)*e[v, 0])
            for v in H:
                for a in range(1, q+1):
                    total = sum((S.glue(u, b, v, a)*e[u, b]
                                 for u in D for b in range(1, q+1)), Affine({}))
                    eta = self.derived(f'halo[{v},{a}].slack', tau-1-total)
                    self.eq(f'halo[{v},{a}]', total+eta, tau-1)
            assert len(self.names) == base_m+4*J+q*(N-s+len(H))
            assert len(self.rows) == base_l+3*J+q*(N-s+len(H))
        self.counts = dict(N=N, q=q, s=s, K=K, J=J, halo=len(H),
                           variables=len(self.names), equations=len(self.rows))

    def witness(self, labels: tuple[int, ...]) -> list[int] | None:
        if len(labels) != len(self.domain):
            raise ValueError('Wrong label tuple length')
        ranks = canonical_ranks(self.system, self.domain, labels)
        if ranks is None:
            return None
        mapping = dict(zip(self.domain, labels))
        w: list[int] = []
        for recipe in self.recipes:
            value = recipe(mapping, ranks, w)
            if type(value) is not int or value < 0:
                return None
            w.append(value)
        if not self.check(w):
            raise AssertionError('Constructed witness fails source equations')
        return w

    def check(self, w: list[int]) -> bool:
        return (len(w) == len(self.names) and
                all(type(x) is int and x >= 0 for x in w) and
                all(row.evaluate(w) == 0 for row in self.rows))

    def export(self, path: str, labels: tuple[int, ...]) -> None:
        w = self.witness(labels)
        if w is None:
            raise ValueError('The requested assembly has no certificate')
        obj = {'format': 'affine-sos-v1', 'description': 'P=sum of squared affine rows',
               'domain': self.domain, 'palette': self.system.tiles,
               'strengths': self.system.strengths, 'temperature': self.system.temperature,
               'seed': [[v, a] for v, a in self.system.seed.items()],
               'terminal_required': self.require_terminal, 'counts': self.counts,
               'variables': self.names, 'rows': [r.json() for r in self.rows],
               'row_names': self.row_names, 'labels': labels, 'witness': w}
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(obj, f, indent=2)
            f.write('\n')


def verify_export(path: str) -> tuple[int, int]:
    """Stand-alone arithmetic verification; does not run the compiler."""
    with open(path, encoding='utf-8') as f:
        obj = json.load(f)
    if obj.get('format') != 'affine-sos-v1':
        raise ValueError('Unrecognized instance format')
    w = obj['witness']
    if len(w) != len(obj['variables']) or any(type(x) is not int or x < 0 for x in w):
        raise ValueError('Invalid natural witness')
    for index, row in enumerate(obj['rows']):
        value = row['constant'] + sum(c*w[i] for i, c in row['terms'])
        if value != 0:
            raise ValueError(f'Nonzero residual in row {index}: {value}')
    return len(w), len(obj['rows'])


def fixtures() -> dict[str, tuple[TileSystem, tuple[Point, ...]]]:
    diamond = TileSystem((('g', 'g', 'g', 'g'),), {'g': 1}, 1, {(0, 0): 1})
    square = ((0, 0), (0, 1), (1, 0), (1, 1))
    center = ('n', 'e', 's', 'w')
    arms = (('', '', 'n', ''), ('', '', '', 'e'), ('s', '', '', ''), ('', 'w', '', ''))
    cross = ((0, 0), (0, 1), (1, 0), (0, -1), (-1, 0))
    star = TileSystem((center,)+arms, {g: 1 for g in 'nesw'}, 1, {(0, 0): 1})
    alternative = TileSystem((center,)+arms+(arms[0],), {g: 1 for g in 'nesw'}, 1, {(0, 0): 1})
    cooperative = TileSystem((('n', 'e', '', ''), ('c', '', '', 'e'),
                              ('', 'd', 'n', ''), ('', '', 'c', 'd')),
                             {'n': 2, 'e': 2, 'c': 1, 'd': 1}, 2, {(0, 0): 1})
    return {'diamond': (diamond, square), 'capped_star': (star, cross),
            'alternative_star': (alternative, cross), 'cooperative_square': (cooperative, square)}
