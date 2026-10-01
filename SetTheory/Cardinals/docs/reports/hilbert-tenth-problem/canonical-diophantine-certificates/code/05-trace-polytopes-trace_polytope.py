#!/usr/bin/env python3
"""Exact, witness-preserving Petri-net trace certificates.

Python 3.10+, standard library only.  The emitted polynomial is represented
without expansion as a sum of squares of sparse residual polynomials.
All unknowns range over NONNEGATIVE INTEGERS.  No numerical solver is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
import json
from typing import Iterable, Mapping, Sequence

Monomial = tuple[str, ...]

@dataclass
class Poly:
    terms: dict[Monomial, int]

    def __post_init__(self):
        self.terms = {k: v for k, v in self.terms.items() if v}

    @staticmethod
    def cast(value: int | Poly) -> Poly:
        return value if isinstance(value, Poly) else Poly({(): value})

    @staticmethod
    def var(name: str) -> Poly:
        return Poly({(name,): 1})

    def __add__(self, other: int | Poly) -> Poly:
        out = self.terms.copy()
        for key, val in self.cast(other).terms.items():
            out[key] = out.get(key, 0) + val
        return Poly(out)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({key: -val for key, val in self.terms.items()})

    def __sub__(self, other: int | Poly) -> Poly:
        return self + -self.cast(other)

    def __rsub__(self, other: int | Poly) -> Poly:
        return self.cast(other) + -self

    def __mul__(self, other: int | Poly) -> Poly:
        out: dict[Monomial, int] = {}
        for k, a in self.terms.items():
            for l, b in self.cast(other).terms.items():
                key = tuple(sorted(k + l))
                out[key] = out.get(key, 0) + a * b
        return Poly(out)

    __rmul__ = __mul__

    def evaluate(self, env: Mapping[str, int]) -> int:
        total = 0
        for monomial, coefficient in self.terms.items():
            value = coefficient
            for name in monomial:
                value *= env[name]
            total += value
        return total

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def text(self) -> str:
        if not self.terms:
            return '0'
        return ' + '.join(f'({c})' + (('*' + '*'.join(m)) if m else '')
                          for m, c in sorted(self.terms.items()))

@dataclass(frozen=True)
class Net:
    """Rows index transition labels; columns index places."""
    pre: tuple[tuple[int, ...], ...]
    post: tuple[tuple[int, ...], ...]
    names: tuple[str, ...] = ()

    def __post_init__(self):
        if not self.pre or len(self.pre) != len(self.post):
            raise ValueError('A net must have equally many pre/post rows, at least one.')
        d = len(self.pre[0])
        if any(len(row) != d for row in self.pre + self.post):
            raise ValueError('Inconsistent place counts.')
        if any(type(x) is not int or x < 0 for row in self.pre + self.post for x in row):
            raise ValueError('Arc weights must be nonnegative integers.')
        if self.names and (len(self.names) != len(self.pre) or len(set(self.names)) != len(self.names)):
            raise ValueError('Labels must be distinct and match transition count.')

    @property
    def m(self) -> int:
        return len(self.pre)

    @property
    def d(self) -> int:
        return len(self.pre[0])

    def demand(self, a: int, b: int) -> tuple[int, ...]:
        return tuple(x + max(y - z, 0)
                     for x, y, z in zip(self.pre[a], self.pre[b], self.post[a]))

    def independence(self) -> frozenset[tuple[int, int]]:
        return frozenset((a, b) for a in range(self.m) for b in range(self.m)
                         if a != b and self.demand(a, b) == self.demand(b, a))

    def step(self, marking: Sequence[int], a: int) -> tuple[int, ...] | None:
        if len(marking) != self.d:
            raise ValueError('Wrong marking dimension.')
        if any(x < c for x, c in zip(marking, self.pre[a])):
            return None
        return tuple(x - c + p for x, c, p in zip(marking, self.pre[a], self.post[a]))

    def run(self, initial: Sequence[int], word: Sequence[int]) -> list[tuple[int, ...]] | None:
        trace = [tuple(initial)]
        for a in word:
            if not 0 <= a < self.m:
                raise ValueError('Unknown label.')
            nxt = self.step(trace[-1], a)
            if nxt is None:
                return None
            trace.append(nxt)
        return trace


def forbidden_history(word: Sequence[int], m: int, independence: Iterable[tuple[int, int]]):
    I = frozenset(independence)
    history = [tuple(0 for _ in range(m))]
    valid = True
    for b in word:
        old = history[-1]
        valid = valid and old[b] == 0
        history.append(tuple(int((a, b) in I and (a < b or old[a])) for a in range(m)))
    return valid, history


def graph_realization(m: int, independence: Iterable[tuple[int, int]]) -> Net:
    """Realize an arbitrary symmetric irreflexive I by unit-weight transitions."""
    I = frozenset(independence)
    if any(a == b or not (0 <= a < m and 0 <= b < m) or (b, a) not in I for a, b in I):
        raise ValueError('I must be symmetric and irreflexive on the alphabet.')
    pairs = [(a, b) for a in range(m) for b in range(a + 1, m) if (a, b) not in I]
    pre = [[0] * len(pairs) for _ in range(m)]
    post = [[0] * len(pairs) for _ in range(m)]
    for p, (a, b) in enumerate(pairs):
        post[a][p] = 1
        pre[b][p] = 1
    return Net(tuple(map(tuple, pre)), tuple(map(tuple, post)))

UpperBounds = tuple[tuple[int | None, ...], ...]


def interval_independence(net: Net, upper: UpperBounds) -> frozenset[tuple[int, int]]:
    """Exact partial-map commutation for extra finite upper guards.

The lower guard is net.pre; the update is net.post - net.pre. None means
infinity. Empty one-step domains must be removed by the caller.
"""
    if len(upper) != net.m or any(len(row) != net.d for row in upper):
        raise ValueError('Upper guards must match transition and place counts.')
    if any(u is not None and (type(u) is not int or u < net.pre[a][p])
           for a, row in enumerate(upper) for p, u in enumerate(row)):
        raise ValueError('Upper guards must be None or integers >= the lower guard.')
    def box(a, b):
        lows, highs = [], []
        for p in range(net.d):
            delta = net.post[a][p] - net.pre[a][p]
            lo = max(net.pre[a][p], net.pre[b][p] - delta)
            candidates = []
            if upper[a][p] is not None: candidates.append(upper[a][p])
            if upper[b][p] is not None: candidates.append(upper[b][p] - delta)
            hi = min(candidates) if candidates else None
            if hi is not None and lo > hi: return None
            lows.append(lo); highs.append(hi)
        return tuple(lows), tuple(highs)
    return frozenset((a,b) for a in range(net.m) for b in range(net.m)
                     if a != b and box(a,b) == box(b,a))


def guarded_run(net: Net, upper: UpperBounds, initial: Sequence[int], word: Sequence[int]):
    """Literal simulator used independently of the polynomial constraints."""
    trace = net.run(initial, word)
    if trace is None: return None
    for i,a in enumerate(word):
        if any(u is not None and trace[i][p] > u for p,u in enumerate(upper[a])):
            return None
    return trace


@dataclass
class Certificate:
    net: Net
    initial: tuple[int, ...]
    final: tuple[int, ...]
    horizon: int
    form: str
    independence: frozenset[tuple[int, int]]
    variables: list[str]
    residuals: list[Poly]
    upper: UpperBounds | None = None

    def zero(self, env: Mapping[str, int]) -> bool:
        if set(env) != set(self.variables):
            raise ValueError('Assignment must have exactly the certificate variables.')
        if any(type(v) is not int or v < 0 for v in env.values()):
            return False
        return all(r.evaluate(env) == 0 for r in self.residuals)

    def energy(self, env: Mapping[str, int]) -> int:
        return sum(r.evaluate(env) ** 2 for r in self.residuals)

    @property
    def degree_bound(self) -> int:
        return 2 * max((r.degree for r in self.residuals), default=0)

    def expanded_polynomial(self) -> Poly:
        return sum((r * r for r in self.residuals), Poly({}))

    def decode(self, env: Mapping[str, int]) -> tuple[int, ...]:
        if not self.zero(env):
            raise ValueError('Not a natural-number zero.')
        return tuple(next(a for a in range(self.net.m) if env[f'e_{i}_{a}'] == 1)
                     for i in range(self.horizon))

    def witness(self, word: Sequence[int]) -> dict[str, int]:
        if len(word) != self.horizon:
            raise ValueError('Word has the wrong length.')
        trace = (self.net.run(self.initial, word) if self.upper is None else
                 guarded_run(self.net, self.upper, self.initial, word))
        if trace is None or trace[-1] != self.final:
            raise ValueError('Word does not realize the prescribed endpoints.')
        valid, flags = forbidden_history(word, self.net.m, self.independence)
        if self.form != 'raw' and not valid:
            raise ValueError('Word is not lexicographically canonical.')
        env: dict[str, int] = {}
        for i, marking in enumerate(trace):
            for p, value in enumerate(marking):
                env[f'x_{i}_{p}'] = value
        for i, b in enumerate(word):
            for a in range(self.net.m):
                env[f'e_{i}_{a}'] = int(a == b)
            for p in range(self.net.d):
                env[f'r_{i}_{p}'] = trace[i][p] - self.net.pre[b][p]
        if self.upper is not None:
            bounds = [self.initial[p] + self.horizon * max(row[p] for row in self.net.post)
                      for p in range(self.net.d)]
            for i,b in enumerate(word):
                for a,row in enumerate(self.upper):
                    for p,upper_bound in enumerate(row):
                        if upper_bound is not None:
                            limit = upper_bound if a == b else bounds[p]
                            env[f'g_{i}_{a}_{p}'] = limit - trace[i][p]
        if self.form != 'raw':
            for i, row in enumerate(flags):
                for a, value in enumerate(row):
                    env[f'f_{i}_{a}'] = value
            if self.form == 'quadratic':
                for i, b in enumerate(word):
                    for a in range(self.net.m):
                        c = int((a, b) in self.independence)
                        h = int((a, b) in self.independence and a < b)
                        f = flags[i][a]
                        u = f * (c - h)
                        vals = (u, f-u, c-h-u, 1+u-f-(c-h), 1-int(a == b)-f)
                        for label, value in zip(('u', 's1', 's2', 's3', 's4'), vals):
                            env[f'{label}_{i}_{a}'] = value
        if not self.zero(env):
            raise RuntimeError('Internal compiler error: constructed witness is invalid.')
        return env

    def export(self, path: str) -> None:
        data = {'domain': 'nonnegative integers', 'polynomial': 'sum of squared residuals',
                'form': self.form, 'degree_bound': self.degree_bound,
                'initial': self.initial, 'final': self.final, 'horizon': self.horizon,
                'pre': self.net.pre, 'post': self.net.post, 'upper': self.upper,
                'independence': sorted(self.independence), 'variables': self.variables,
                'residuals': [[{'coefficient': c, 'monomial': list(m)} for m,c in r.terms.items()]
                              for r in self.residuals]}
        with open(path, 'w', encoding='utf-8') as out:
            json.dump(data, out, indent=2)
            out.write('\n')


def compile_certificate(net: Net, initial: Sequence[int], final: Sequence[int], horizon: int,
                        form: str = 'quadratic', independence=None,
                        upper: UpperBounds | None = None) -> Certificate:
    if form not in ('raw', 'quartic', 'quadratic'):
        raise ValueError('Form must be raw, quartic, or quadratic.')
    if type(horizon) is not int or horizon < 0:
        raise ValueError('Horizon must be a nonnegative integer.')
    initial, final = tuple(initial), tuple(final)
    if any(len(x) != net.d or any(type(y) is not int or y < 0 for y in x) for x in (initial, final)):
        raise ValueError('Endpoints must be nonnegative integer markings.')
    upper = None if upper is None else tuple(tuple(row) for row in upper)
    maximal = net.independence() if upper is None else interval_independence(net, upper)
    I = maximal if independence is None else frozenset(independence)
    if not I <= maximal or any((b, a) not in I for a, b in I):
        raise ValueError('Independence must be symmetric and semantically sound.')
    T, d, m = horizon, net.d, net.m
    variables: list[str] = []
    residuals: list[Poly] = []
    def make(prefix, rows, columns):
        result = {}
        for i in range(rows):
            for j in range(columns):
                name = f'{prefix}_{i}_{j}'
                variables.append(name)
                result[i, j] = Poly.var(name)
        return result
    x = make('x', T + 1, d)
    e = make('e', T, m)
    r = make('r', T, d)
    for p in range(d):
        residuals.extend((x[0,p]-initial[p], x[T,p]-final[p]))
    for i in range(T):
        residuals.append(sum(e[i,a] for a in range(m))-1)
        for p in range(d):
            consume = sum(net.pre[a][p]*e[i,a] for a in range(m))
            produce = sum(net.post[a][p]*e[i,a] for a in range(m))
            residuals.extend((x[i,p]-consume-r[i,p], x[i+1,p]-r[i,p]-produce))
    if upper is not None:
        bounds = [initial[p] + T * max(row[p] for row in net.post) for p in range(d)]
        for i in range(T):
            for a,row in enumerate(upper):
                for p,upper_bound in enumerate(row):
                    if upper_bound is not None:
                        name = f'g_{i}_{a}_{p}'
                        variables.append(name)
                        slack = Poly.var(name)
                        limit = upper_bound*e[i,a] + bounds[p]*(1-e[i,a])
                        residuals.append(x[i,p] + slack - limit)
    if form != 'raw':
        f = make('f', T+1, m)
        residuals.extend(f[0,a] for a in range(m))
        extras = {label: make(label, T, m) for label in ('u','s1','s2','s3','s4')} if form == 'quadratic' else {}
        for i in range(T):
            for a in range(m):
                c = sum((e[i,b] for b in range(m) if (a,b) in I), Poly({}))
                h = sum((e[i,b] for b in range(a+1,m) if (a,b) in I), Poly({}))
                if form == 'quartic':
                    residuals.append(f[i+1,a]-h-(c-h)*f[i,a])
                else:
                    u = extras['u'][i,a]
                    residuals.extend((f[i,a]-u-extras['s1'][i,a],
                                      c-h-u-extras['s2'][i,a],
                                      1+u-f[i,a]-(c-h)-extras['s3'][i,a],
                                      f[i+1,a]-h-u,
                                      1-e[i,a]-f[i,a]-extras['s4'][i,a]))
            if form == 'quartic':
                residuals.append(sum(e[i,a]*f[i,a] for a in range(m)))
    return Certificate(net, initial, final, T, form, I, variables, residuals, upper)


def circuit_net(n: int, gates: Sequence[tuple[str, tuple[int, ...]]], output: int):
    """Boolean circuit -> 1-safe unit-weight net, parsimoniously.

Wires 0..n-1 are inputs; each gate produces the next wire.  Allowed gates:
NOT (one argument), AND/OR (two arguments), CONST0/CONST1 (no arguments).
Returns (net, initial, final, horizon).  Every accepting run has exactly
2*(n+len(gates))+1 steps and the same final marking.
"""
    if n < 0 or not 0 <= output < n+len(gates):
        raise ValueError('Invalid input count or output wire.')
    w = n + len(gates)
    T = 2*w+1
    # One control place per stage, and two value places per wire.
    d = T+1+2*w
    def value_place(j, bit): return T+1+2*j+bit
    pre, post, names = [], [], []
    def emit(stage, name, reads=(), creates=(), removes=()):
        a, b = [0]*d, [0]*d
        a[stage] = 1; b[stage+1] = 1
        for p in set(reads): a[p] = 1; b[p] = 1
        for p in creates: b[p] = 1
        for p in removes: a[p] = 1
        pre.append(tuple(a)); post.append(tuple(b)); names.append(name)
    for j in range(n):
        for bit in (0,1):
            emit(j, f'input_{j}_{bit}', creates=(value_place(j,bit),))
    for k, (op, args) in enumerate(gates):
        j = n+k
        arities = {'NOT':1, 'AND':2, 'OR':2, 'CONST0':0, 'CONST1':0}
        if op not in arities or len(args) != arities[op] or any(not 0 <= a < j for a in args):
            raise ValueError('Gate is not topologically well formed.')
        unique = sorted(set(args))
        for vals in product((0,1), repeat=len(unique)):
            state = dict(zip(unique,vals))
            ins = [state[a] for a in args]
            bit = (1-ins[0] if op == 'NOT' else (ins[0]&ins[1] if op == 'AND' else
                   (ins[0]|ins[1] if op == 'OR' else int(op == 'CONST1'))))
            emit(j, f'gate_{k}_' + ''.join(map(str,vals)),
                 reads=(value_place(a,state[a]) for a in unique), creates=(value_place(j,bit),))
    emit(w, 'accept', reads=(value_place(output,1),))
    for j in range(w):
        for bit in (0,1):
            emit(w+1+j, f'cleanup_{j}_{bit}', removes=(value_place(j,bit),))
    initial=[0]*d; initial[0]=1
    final=[0]*d; final[T]=1
    return Net(tuple(pre),tuple(post),tuple(names)), tuple(initial),tuple(final),T


def enabled_runs(net: Net, initial: Sequence[int], horizon: int):
    """Explicit DFS, for small verification examples only."""
    if type(horizon) is not int or horizon < 0:
        raise ValueError('Horizon must be a nonnegative integer.')
    stack = [(tuple(initial), ())]
    while stack:
        marking, word = stack.pop()
        if len(word) == horizon:
            yield word, marking
            continue
        for a in range(net.m-1,-1,-1):
            nxt = net.step(marking,a)
            if nxt is not None:
                stack.append((nxt,word+(a,)))
