#!/usr/bin/env python3
"""Loop-exact interaction-combinator semantics and quadratic certificate exporter.

Standard-library only. Port numbers are ordered: gamma-gamma crosses auxiliary
indices, delta-delta preserves them. The compiler does not execute its input.
All certificate variables are natural numbers; residual coefficients are integers.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
import json
from pathlib import Path
from typing import Iterable, Mapping, Sequence

TYPES = ('G', 'D', 'E')
ARITY = {'G': 2, 'D': 2, 'E': 0}
Port = tuple[int, int]  # negative cell ids are labelled free ports


def natural(x: object) -> bool:
    return type(x) is int and x >= 0


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def wire(a: Port, b: Port) -> tuple[Port, Port]:
    require(a != b, 'a wire must have two distinct ports')
    return tuple(sorted((a, b)))  # type: ignore[return-value]


def ports(cells: Mapping[int, str], free: Sequence[Port] = ()) -> tuple[Port, ...]:
    return tuple(sorted(tuple(free) + tuple((c, p) for c, typ in cells.items()
                                            for p in range(ARITY[typ] + 1))))


@dataclass
class Net:
    cells: dict[int, str]
    wires: tuple[tuple[Port, Port], ...]
    loops: int = 0
    free: tuple[Port, ...] = ()

    def validate(self) -> None:
        require(all(natural(c) and t in TYPES for c, t in self.cells.items()),
                'invalid agent id or type')
        require(natural(self.loops), 'invalid cyclic-wire count')
        require(all(isinstance(p, tuple) and len(p) == 2 and
                    type(p[0]) is int and p[0] < 0 and p[1] == 0
                    for p in self.free), 'invalid free-port name')
        require(tuple(sorted(set(self.free))) == self.free, 'noncanonical free ports')
        universe = ports(self.cells, self.free)
        require(tuple(sorted(set(self.wires))) == self.wires, 'noncanonical wire list')
        for a, b in self.wires:
            require(a < b, 'noncanonical wire endpoints')
        actual = tuple(sorted(p for ab in self.wires for p in ab))
        require(actual == universe, 'wires must form a perfect matching of all ports')

    def partner(self) -> dict[Port, Port]:
        self.validate()
        return {x: y for a, b in self.wires for x, y in ((a, b), (b, a))}

    def active_pairs(self) -> tuple[tuple[int, int], ...]:
        self.validate()
        return tuple((a[0], b[0]) for a, b in self.wires
                     if a[1] == b[1] == 0 and a[0] >= 0 and b[0] >= 0)

    def as_dict(self) -> dict:
        return {'cells': [[c, self.cells[c]] for c in sorted(self.cells)],
                'wires': [[list(a), list(b)] for a, b in self.wires],
                'loops': self.loops, 'free': [list(x) for x in self.free]}


@dataclass
class Patch:
    pair: tuple[int, int]
    cells: dict[int, str]
    next_id: int
    old_aux: tuple[Port, ...]
    interface: tuple[Port, ...]
    rhs_wires: tuple[tuple[Port, Port], ...]
    rule: str


def rule_patch(cells: Mapping[int, str], pair: tuple[int, int],
               next_id: int) -> Patch:
    """Construct a rule template from types and a lifetime schedule, not wiring."""
    a, b = pair
    require(natural(a) and natural(b) and a < b and a in cells and b in cells,
            'scheduled pair must be two live agents in increasing id order')
    require(natural(next_id) and next_id > max(cells, default=-1), 'bad allocator')
    ta, tb = cells[a], cells[b]
    out = dict(cells)
    del out[a], out[b]
    aux = tuple((c, p) for c in (a, b) for p in range(1, ARITY[cells[c]] + 1))
    # Temporary interface labels cannot collide with genuine free ports, whose p=0.
    interface = tuple((-1, i + 1) for i in range(len(aux)))
    attached = dict(zip(aux, interface))
    rhs: list[tuple[Port, Port]] = []
    rule_name = ''.join(sorted((ta, tb)))
    if ta == tb == 'E':
        pass
    elif ta == tb:
        for p in (1, 2):
            q = 3 - p if ta == 'G' else p
            rhs.append(wire(attached[(a, p)], attached[(b, q)]))
    elif 'E' in (ta, tb):
        c = b if ta == 'E' else a
        for p in (1, 2):
            fresh = next_id
            next_id += 1
            out[fresh] = 'E'
            rhs.append(wire(attached[(c, p)], (fresh, 0)))
    else:
        # Orient mixed rule as gamma vs delta, regardless of agent-id order.
        g, d = (a, b) if ta == 'G' else (b, a)
        D = (next_id, next_id + 1)
        G = (next_id + 2, next_id + 3)
        next_id += 4
        out.update({D[0]: 'D', D[1]: 'D', G[0]: 'G', G[1]: 'G'})
        for i in (1, 2):
            rhs.append(wire(attached[(g, i)], (D[i - 1], 0)))
            rhs.append(wire(attached[(d, i)], (G[i - 1], 0)))
        for i in (1, 2):
            for j in (1, 2):
                rhs.append(wire((D[i - 1], j), (G[j - 1], i)))
    return Patch(pair, out, next_id, aux, interface, tuple(sorted(rhs)), rule_name)


def temporary(net: Net, patch: Patch) -> tuple[tuple[Port, ...], dict[Port, Port],
                                             dict[Port, Port], tuple[Port, ...]]:
    old = net.partner()
    a, b = patch.pair
    require(old[(a, 0)] == (b, 0), 'scheduled pair is not active')
    alpha = {x: y for x, y in old.items() if x not in ((a, 0), (b, 0))}
    for x, y in patch.rhs_wires:
        alpha[x], alpha[y] = y, x
    V = tuple(sorted(alpha))
    beta = {x: x for x in V}
    for x, y in zip(patch.old_aux, patch.interface):
        beta[x], beta[y] = y, x
    B = ports(patch.cells, net.free)
    require(set(V) == set(B) | set(patch.old_aux) | set(patch.interface),
            'temporary port partition mismatch')
    return V, alpha, beta, B


def permutation_cycles(sigma: Sequence[int]) -> tuple[tuple[int, ...], ...]:
    n = len(sigma)
    require(sorted(sigma) == list(range(n)), 'not a permutation')
    seen: set[int] = set()
    result = []
    for i in range(n):
        if i in seen:
            continue
        cyc, j = [], i
        while j not in seen:
            seen.add(j)
            cyc.append(j)
            j = sigma[j]
        require(j == i, 'invalid orbit')
        result.append(tuple(cyc))
    return tuple(result)


def orbit_witness(sigma: Sequence[int]) -> dict[str, list[int]]:
    """Unique natural solution, using mathematical vertex labels 1,...,n."""
    n = len(sigma)
    out = {k: [0] * n for k in ('r', 'd', 'h', 'e', 's')}
    for cyc in permutation_cycles(sigma):
        root = min(cyc)
        for i in cyc:
            out['r'][i] = root + 1
            out['e'][i] = int(i == root)
            out['h'][i] = 0 if i == root else i - root - 1
            j, dist = i, 0
            while j != root:
                j = sigma[j]
                dist += 1
            out['d'][i] = dist
    out['s'] = [out['d'][sigma[i]] for i in range(n)]
    return out


def check_orbit(sigma: Sequence[int], values: Mapping[str, Sequence[int]]) -> bool:
    n = len(sigma)
    if any(len(values[k]) != n or not all(natural(x) for x in values[k])
           for k in ('r', 'd', 'h', 'e', 's')):
        return False
    r, d, h, e, s = (values[k] for k in ('r', 'd', 'h', 'e', 's'))
    for i in range(n):
        if any((e[i] * (e[i] - 1),
                r[i] + (1 - e[i]) * (h[i] + 1) - (i + 1),
                e[i] * h[i], r[i] - r[sigma[i]], s[i] - d[sigma[i]],
                d[i] - (1 - e[i]) * (s[i] + 1))):
            return False
    return True


def glue_permutation(V: Sequence[Port], alpha: Mapping[Port, Port],
                     beta: Mapping[Port, Port], B: Sequence[Port]) -> tuple:
    ix = {v: i for i, v in enumerate(V)}
    sigma = [ix[alpha[beta[v]]] for v in V]
    w = orbit_witness(sigma)
    groups: dict[int, list[Port]] = {}
    for b in B:
        groups.setdefault(w['r'][ix[b]], []).append(b)
    require(all(len(g) == 2 for g in groups.values()), 'bad path orbit')
    edges = tuple(sorted(wire(g[0], g[1]) for g in groups.values()))
    numerator = sum(w['e']) - len(B) // 2
    require(numerator >= 0 and numerator % 2 == 0, 'bad loop formula')
    return edges, numerator // 2, sigma, w


def glue_components(V: Sequence[Port], alpha: Mapping[Port, Port],
                    beta: Mapping[Port, Port], B: Sequence[Port]) -> tuple:
    """Independent multigraph traversal: never calls the permutation algorithm."""
    boundary = set(B)
    adj = {v: [alpha[v]] + ([] if beta[v] == v else [beta[v]]) for v in V}
    seen, result, loops = set(), [], 0
    for start in V:
        if start in seen:
            continue
        stack, component = [start], []
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            component.append(v)
            stack.extend(w for w in adj[v] if w not in seen)
        ends = [v for v in component if v in boundary]
        require(len(ends) in (0, 2), 'component is not a path or a cycle')
        if ends:
            result.append(wire(ends[0], ends[1]))
        else:
            loops += 1
    return tuple(sorted(result)), loops


def step(net: Net, pair: tuple[int, int], next_id: int | None = None,
         independent: bool = False) -> tuple[Net, int, dict]:
    net.validate()
    if next_id is None:
        next_id = max(net.cells, default=-1) + 1
    patch = rule_patch(net.cells, pair, next_id)
    V, alpha, beta, B = temporary(net, patch)
    if independent:
        edges, added = glue_components(V, alpha, beta, B)
        sigma, ow = [], {}
    else:
        edges, added, sigma, ow = glue_permutation(V, alpha, beta, B)
    result = Net(patch.cells, edges, net.loops + added, net.free)
    result.validate()
    return result, patch.next_id, {'rule': patch.rule, 'V': V, 'sigma': sigma,
                                  'orbit': ow, 'added_loops': added}


# Sparse polynomials: monomials are sorted tuples of variable names.
@dataclass
class Poly:
    terms: dict[tuple[str, ...], int]

    @staticmethod
    def constant(k: int) -> 'Poly':
        return Poly({(): k} if k else {})

    @staticmethod
    def variable(name: str) -> 'Poly':
        return Poly({(name,): 1})

    @staticmethod
    def coerce(value: 'Poly | int') -> 'Poly':
        return value if isinstance(value, Poly) else Poly.constant(value)

    def __add__(self, other: 'Poly | int') -> 'Poly':
        terms = self.terms.copy()
        for mon, coef in Poly.coerce(other).terms.items():
            terms[mon] = terms.get(mon, 0) + coef
            if not terms[mon]:
                del terms[mon]
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self) -> 'Poly':
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: 'Poly | int') -> 'Poly':
        return self + -Poly.coerce(other)

    def __rsub__(self, other: 'Poly | int') -> 'Poly':
        return Poly.coerce(other) + -self

    def __mul__(self, other: 'Poly | int') -> 'Poly':
        terms: dict[tuple[str, ...], int] = {}
        for a, x in self.terms.items():
            for b, y in Poly.coerce(other).terms.items():
                m = tuple(sorted(a + b))
                terms[m] = terms.get(m, 0) + x * y
        return Poly({m: c for m, c in terms.items() if c})

    __rmul__ = __mul__

    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Mapping[str, int]) -> int:
        total = 0
        for mon, c in self.terms.items():
            for name in mon:
                c *= values[name]
            total += c
        return total

    def as_list(self) -> list:
        return [[coef, list(mon)] for mon, coef in sorted(self.terms.items())]


class System:
    def __init__(self) -> None:
        self.parameters: list[str] = []
        self.variables: list[str] = []
        self.residuals: list[tuple[str, Poly]] = []

    def var(self, name: str, parameter: bool = False) -> Poly:
        require(name not in self.parameters and name not in self.variables,
                'duplicate scalar name')
        (self.parameters if parameter else self.variables).append(name)
        return Poly.variable(name)

    def add(self, label: str, p: Poly | int) -> None:
        p = Poly.coerce(p)
        require(p.degree() <= 2, f'nonquadratic residual: {label}')
        self.residuals.append((label, p))

    def failed(self, values: Mapping[str, int]) -> list[str]:
        require(set(values) == set(self.variables + self.parameters),
                'assignment must supply exactly all parameters and witnesses')
        require(all(natural(v) for v in values.values()), 'nonnatural coordinate')
        return [label for label, f in self.residuals if f.evaluate(values)]

    def energy(self, values: Mapping[str, int]) -> int:
        self.failed(values)  # validates domain/completeness
        return sum(f.evaluate(values) ** 2 for _, f in self.residuals)

    def as_dict(self) -> dict:
        return {'domain': 'N = {0,1,2,...}', 'polynomial': 'sum(residual**2)',
                'degree_bound': 4, 'parameters': self.parameters,
                'witnesses': self.variables,
                'residuals': [{'name': label, 'terms': f.as_list()}
                              for label, f in self.residuals]}


def scalar(prefix: str, a: Port, b: Port) -> str:
    a, b = sorted((a, b))
    return f'{prefix}.w[{a[0]},{a[1]};{b[0]},{b[1]}]'


@dataclass
class Compilation:
    system: System
    cells: list[dict[int, str]]
    free: tuple[Port, ...]
    schedule: tuple[tuple[int, int], ...]
    patches: list[Patch]
    universes: list[tuple[Port, ...]]
    temporary_vertices: list[tuple[Port, ...]]

    def witness(self, initial: Net, target: Net) -> dict[str, int]:
        initial.validate()
        target.validate()
        require(initial.cells == self.cells[0] and target.cells == self.cells[-1],
                'input/target types do not match schedule ledger')
        require(initial.free == target.free == self.free, 'free-port mismatch')
        states, records = [initial], []
        next_id = max(initial.cells, default=-1) + 1
        for pair in self.schedule:
            nxt, next_id, record = step(states[-1], pair, next_id)
            states.append(nxt)
            records.append(record)
        require(states[-1].as_dict() == target.as_dict(), 'wrong target')
        values: dict[str, int] = {}
        T = len(self.schedule)
        for t, net in enumerate(states):
            prefix = 'in' if t == 0 else 'out' if t == T else f'c{t}'
            partner = net.partner()
            for a, b in combinations(self.universes[t], 2):
                values[scalar(prefix, a, b)] = int(partner[a] == b)
            values[f'{prefix}.loops'] = net.loops
        for t, record in enumerate(records):
            require(tuple(record['V']) == self.temporary_vertices[t], 'vertex mismatch')
            for key, coords in record['orbit'].items():
                for i, value in enumerate(coords):
                    values[f't{t}.{key}[{i + 1}]'] = value
        require(not self.system.failed(values), 'constructed witness failed residuals')
        return values


def compile_schedule(initial_cells: Mapping[int, str], free: Sequence[Port],
                     schedule: Sequence[tuple[int, int]]) -> Compilation:
    """Parametric endpoint compiler. Neither initial nor target wires are read.

    Invalid lifetime schedules raise ValueError. T must be positive. The parameter
    vectors contain BOTH complete endpoint matchings and endpoint loop counts.
    """
    require(len(schedule) > 0, 'use direct endpoint equality for a zero-step trace')
    require(all(natural(c) and t in TYPES for c, t in initial_cells.items()),
            'invalid initial type ledger')
    free = tuple(free)
    require(tuple(sorted(set(free))) == free and all(p[0] < 0 and p[1] == 0 for p in free),
            'invalid free ports')
    cells = [dict(initial_cells)]
    patches = []
    next_id = max(initial_cells, default=-1) + 1
    for pair in schedule:
        patch = rule_patch(cells[-1], pair, next_id)
        patches.append(patch)
        cells.append(patch.cells)
        next_id = patch.next_id
    universes = [ports(c, free) for c in cells]
    require(all(len(P) % 2 == 0 for P in universes), 'odd port cardinality')
    system = System()
    matrices, loops = [], []
    T = len(schedule)
    for t, P in enumerate(universes):
        prefix = 'in' if t == 0 else 'out' if t == T else f'c{t}'
        param = t in (0, T)
        W = {}
        for a, b in combinations(P, 2):
            W[a, b] = W[b, a] = system.var(scalar(prefix, a, b), param)
        for a in P:
            W[a, a] = Poly.constant(0)
        for i, a in enumerate(P):
            system.add(f'c{t}.matching[{i}]', sum((W[a, b] for b in P),
                                                Poly.constant(0)) - 1)
        matrices.append(W)
        loops.append(system.var(f'{prefix}.loops', param))
    all_V = []
    for t, patch in enumerate(patches):
        W, Wnext = matrices[t], matrices[t + 1]
        a, b = patch.pair
        system.add(f't{t}.active', W[(a, 0), (b, 0)] - 1)
        old_remaining = tuple(x for x in universes[t] if x not in ((a, 0), (b, 0)))
        rhs_ports = tuple(x for ab in patch.rhs_wires for x in ab)
        V = tuple(sorted(old_remaining + rhs_ports))
        require(len(V) == len(set(V)), 'temporary labels not disjoint')
        all_V.append(V)
        beta = {x: x for x in V}
        for x, y in zip(patch.old_aux, patch.interface):
            beta[x], beta[y] = y, x
        oldset = set(old_remaining)
        rhs_partner = {x: y for a_, b_ in patch.rhs_wires for x, y in ((a_, b_), (b_, a_))}

        def A(x: Port, y: Port) -> Poly:
            if x in oldset and y in oldset:
                return W[x, y]
            return Poly.constant(int(rhs_partner.get(x) == y))

        data = {k: [system.var(f't{t}.{k}[{i + 1}]') for i in range(len(V))]
                for k in ('r', 'd', 'h', 'e', 's')}
        r, d, h, e, s = (data[k] for k in ('r', 'd', 'h', 'e', 's'))
        for i, x in enumerate(V):
            select_r = sum((A(beta[x], y) * r[j] for j, y in enumerate(V)), Poly.constant(0))
            select_d = sum((A(beta[x], y) * d[j] for j, y in enumerate(V)), Poly.constant(0))
            for suffix, f in (
                ('bit', e[i] * (e[i] - 1)),
                ('minimum', r[i] + (1 - e[i]) * (h[i] + 1) - (i + 1)),
                ('reset', e[i] * h[i]),
                ('orbit', r[i] - select_r),
                ('lookup', s[i] - select_d),
                ('distance', d[i] - (1 - e[i]) * (s[i] + 1))):
                system.add(f't{t}.{suffix}[{i + 1}]', f)
        ix = {x: i for i, x in enumerate(V)}
        B = universes[t + 1]
        for u, v in combinations(B, 2):
            system.add(f't{t}.output[{ix[u] + 1},{ix[v] + 1}]',
                       Wnext[u, v] * (r[ix[u]] - r[ix[v]]))
        system.add(f't{t}.loops', sum(e, Poly.constant(0)) + 2 * loops[t]
                   - 2 * loops[t + 1] - len(B) // 2)
    return Compilation(system, cells, free, tuple(schedule), patches, universes, all_V)


def obstruction_examples() -> tuple[Net, Net]:
    cells = {i: 'D' for i in range(4)}
    decode = lambda n: (n // 3, n % 3)
    def net(edges: list[list[int]]) -> Net:
        result = Net(cells.copy(), tuple(sorted(wire(decode(a), decode(b)) for a, b in edges)))
        result.validate()
        return result
    return (net([[0, 3], [1, 7], [2, 9], [4, 10], [5, 6], [8, 11]]),
            net([[0, 3], [1, 7], [2, 9], [4, 10], [5, 8], [6, 11]]))


def write_example(destination: Path) -> dict:
    destination.mkdir(parents=True, exist_ok=True)
    A, B = obstruction_examples()
    target = Net({}, (), 2)
    compiled = compile_schedule(A.cells, (), ((0, 1), (2, 3)))
    values = compiled.witness(A, target)
    payload = compiled.system.as_dict()
    (destination / 'quartic_A_schedule.json').write_text(json.dumps(payload, indent=2) + '\n')
    (destination / 'witness_A.json').write_text(json.dumps(values, indent=2, sort_keys=True) + '\n')
    (destination / 'endpoints.json').write_text(json.dumps({'A': A.as_dict(), 'B': B.as_dict(),
                                                         'target': target.as_dict()}, indent=2) + '\n')
    return {'parameters': len(compiled.system.parameters),
            'witnesses': len(compiled.system.variables),
            'residuals': len(compiled.system.residuals),
            'nonzero_residual_polynomials': sum(bool(f.terms) for _, f in compiled.system.residuals),
            'quadratic_degree': max(f.degree() for _, f in compiled.system.residuals),
            'quartic_value_at_witness': compiled.system.energy(values),
            'temporary_sizes': list(map(len, compiled.temporary_vertices)),
            'configuration_port_counts': list(map(len, compiled.universes))}


if __name__ == '__main__':
    print(json.dumps(write_example(Path(__file__).resolve().parents[1] / 'data'), indent=2))
