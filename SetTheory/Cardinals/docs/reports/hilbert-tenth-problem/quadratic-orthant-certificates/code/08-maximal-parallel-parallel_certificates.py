#!/usr/bin/env python3
"""Exact quadratic certificates for maximal parallel multiset rewriting.

Python 3.10+, standard library only. All states, stoichiometries, firing counts,
and witnesses are nonnegative integers. Polynomials are stored as sums of
squares of affine forms plus products of nonnegative variables. This is a
transparent compiler, not an integer-polynomial equation solver.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from itertools import product
from typing import Iterable, Mapping, Sequence
import json


def natural(n: int) -> bool:
    return isinstance(n, int) and not isinstance(n, bool) and n >= 0


@dataclass(frozen=True)
class Affine:
    coefficients: Mapping[str, int] = field(default_factory=dict)
    constant: int = 0

    @staticmethod
    def variable(name: str) -> 'Affine':
        return Affine({name: 1})

    def __add__(self, other: 'Affine | int') -> 'Affine':
        if isinstance(other, int):
            other = Affine({}, other)
        c = dict(self.coefficients)
        for k, v in other.coefficients.items():
            c[k] = c.get(k, 0) + v
            if not c[k]:
                del c[k]
        return Affine(c, self.constant + other.constant)

    __radd__ = __add__

    def __neg__(self) -> 'Affine':
        return Affine({k: -v for k, v in self.coefficients.items()}, -self.constant)

    def __sub__(self, other: 'Affine | int') -> 'Affine':
        return self + (-other)

    def __mul__(self, scalar: int) -> 'Affine':
        if not isinstance(scalar, int):
            raise TypeError('Affine forms can only be multiplied by integers.')
        return Affine({k: scalar * v for k, v in self.coefficients.items() if scalar * v},
                      scalar * self.constant)

    __rmul__ = __mul__

    def evaluate(self, values: Mapping[str, int]) -> int:
        return self.constant + sum(c * values[k] for k, c in self.coefficients.items())

    def as_dict(self) -> dict:
        return {'constant': self.constant, 'coefficients': dict(self.coefficients)}


@dataclass
class Quadratic:
    squares: list[Affine] = field(default_factory=list)
    products: list[tuple[str, str]] = field(default_factory=list)

    def evaluate(self, values: Mapping[str, int]) -> int:
        return sum(a.evaluate(values) ** 2 for a in self.squares) + sum(
            values[a] * values[b] for a, b in self.products)

    def expanded(self) -> dict[tuple[str, ...], int]:
        result: dict[tuple[str, ...], int] = {}
        def add(key: tuple[str, ...], value: int) -> None:
            result[key] = result.get(key, 0) + value
        for linear in self.squares:
            terms = [((), linear.constant)] + [((k,), c) for k, c in linear.coefficients.items()]
            for ka, ca in terms:
                for kb, cb in terms:
                    add(tuple(sorted(ka + kb)), ca * cb)
        for a, b in self.products:
            add(tuple(sorted((a, b))), 1)
        return {k: c for k, c in sorted(result.items()) if c}

    def as_dict(self) -> dict:
        return {'squares': [a.as_dict() for a in self.squares],
                'nonnegative_products': [list(p) for p in self.products],
                'expanded_terms': [{'variables': list(k), 'coefficient': c}
                                   for k, c in self.expanded().items()]}


@dataclass(frozen=True)
class Atom:
    """Pre-state threshold test x[species] >= threshold, or its negation."""
    species: int
    threshold: int
    present: bool = True

    def holds(self, x: Sequence[int]) -> bool:
        return (x[self.species] >= self.threshold) == self.present


@dataclass(frozen=True)
class Network:
    # Matrices are stored as tuples of rule columns, not as rows.
    consume: tuple[tuple[int, ...], ...]
    produce: tuple[tuple[int, ...], ...]
    guards: tuple[tuple[Atom, ...], ...] = ()

    def __post_init__(self) -> None:
        if not self.consume or not self.consume[0]:
            raise ValueError('At least one species and one rule are required.')
        d, m = len(self.consume[0]), len(self.consume)
        if len(self.produce) != m:
            raise ValueError('Consumption and production must have equal rule counts.')
        if any(len(col) != d or any(not natural(a) for a in col)
               for col in self.consume + self.produce):
            raise ValueError('Matrices must be rectangular and nonnegative integral.')
        if any(not any(col) for col in self.consume):
            raise ValueError('Every rule must consume at least one object.')
        if self.guards and len(self.guards) != m:
            raise ValueError('Provide one conjunction of guard atoms per rule.')
        for conjunction in self.guards:
            for atom in conjunction:
                if not 0 <= atom.species < d or not natural(atom.threshold) or atom.threshold == 0:
                    raise ValueError('Guard species/threshold is out of range.')

    @property
    def d(self) -> int:
        return len(self.consume[0])

    @property
    def m(self) -> int:
        return len(self.consume)

    @property
    def thresholds(self) -> tuple[tuple[int, int], ...]:
        return tuple(sorted({(i, a) for col in self.consume for i, a in enumerate(col) if a}))

    def enabled(self, x: Sequence[int]) -> tuple[bool, ...]:
        return tuple(all(a.holds(x) for a in conjunction)
                     for conjunction in (self.guards or ((),) * self.m))

    def residual(self, x: Sequence[int], f: Sequence[int]) -> tuple[int, ...]:
        return tuple(x[i] - sum(self.consume[j][i] * f[j] for j in range(self.m))
                     for i in range(self.d))

    def legal(self, x: Sequence[int], f: Sequence[int], flat: bool = False) -> bool:
        if len(x) != self.d or len(f) != self.m:
            return False
        if any(not natural(a) for a in tuple(x) + tuple(f)):
            return False
        if flat and any(a > 1 for a in f):
            return False
        e = self.enabled(x)
        if any(f[j] and not e[j] for j in range(self.m)):
            return False
        r = self.residual(x, f)
        if min(r) < 0:
            return False
        # Independent semantic test: can one more copy of a rule be appended?
        return not any(e[j] and (not flat or f[j] == 0)
                       and all(a <= r[i] for i, a in enumerate(self.consume[j]))
                       for j in range(self.m))

    def outcomes(self, x: Sequence[int], flat: bool = False,
                 retention: Sequence[int] | None = None) -> Iterable[tuple[tuple[int, ...], tuple[int, ...]]]:
        if len(x) != self.d or any(not natural(a) for a in x):
            raise ValueError('Invalid state.')
        keep = tuple(retention) if retention is not None else (1,) * self.d
        if len(keep) != self.d or any(a not in (0, 1) for a in keep):
            raise ValueError('Retention entries must be 0 or 1.')
        bounds = [min(x[i] // a for i, a in enumerate(col) if a) for col in self.consume]
        for f in product(*(range(min(b, 1) + 1 if flat else b + 1) for b in bounds)):
            if self.legal(x, f, flat):
                r = self.residual(x, f)
                y = tuple(keep[i] * r[i] + sum(self.produce[j][i] * f[j] for j in range(self.m))
                          for i in range(self.d))
                yield f, y


class RoundCertificate:
    """Compile one round; x,y are free coordinates and all other names auxiliaries."""
    def __init__(self, network: Network, *, flat: bool = False,
                 retention: Sequence[int] | None = None, prefix: str = '') -> None:
        self.network, self.flat, self.prefix = network, flat, prefix
        self.retention = tuple(retention) if retention is not None else (1,) * network.d
        if len(self.retention) != network.d or any(a not in (0, 1) for a in self.retention):
            raise ValueError('Retention entries must be 0 or 1.')
        self.polynomial = Quadratic()
        self.auxiliary_names: list[str] = []
        self.input_names = [prefix + f'x{i}' for i in range(network.d)]
        self.output_names = [prefix + f'y{i}' for i in range(network.d)]
        self.comparators: list[tuple[str, Affine, int]] = []
        self.conjunctions: list[tuple[str, Affine, Affine]] = []
        x = list(map(Affine.variable, self.input_names))
        y = list(map(Affine.variable, self.output_names))
        f = [self.var(f'f{j}') for j in range(network.m)]
        r = [self.var(f'r{i}') for i in range(network.d)]
        for i in range(network.d):
            self.polynomial.squares.append(x[i] - sum(network.consume[j][i] * f[j]
                                                       for j in range(network.m)) - r[i])
            self.polynomial.squares.append(y[i] - sum(network.produce[j][i] * f[j]
                                                       for j in range(network.m)) - self.retention[i] * r[i])
        flags: dict[tuple[int, int], Affine] = {}
        for i, a in network.thresholds:
            flags[i, a], _ = self.compare(r[i], a, f'q{i}_{a}')
        for j, col in enumerate(network.consume):
            e, disabled = Affine({}, 1), Affine({}, 0)
            atoms = (network.guards or ((),) * network.m)[j]
            for h, atom in enumerate(atoms):
                b, c = self.compare(x[atom.species], atom.threshold, f'guard{j}_{h}')
                yes, no = (b, c) if atom.present else (c, b)
                if h == 0:
                    e, disabled = yes, no
                else:
                    e, disabled = self.and_gate(e, yes, f'and{j}_{h}')
            if atoms:
                disabled_name = next(iter(disabled.coefficients))
                self.polynomial.products.append((disabled_name, self.prefix + f'f{j}'))
            k = sum(a > 0 for a in col)
            s = self.var(f's{j}')
            lhs = sum(flags[i, a] for i, a in enumerate(col) if a) + e + s
            if flat:
                g = self.var(f'g{j}')
                self.polynomial.squares.append(f[j] + g - 1)
                lhs += g
            self.polynomial.squares.append(lhs - k - int(flat))
        expected = network.d + 2 * network.m + 4 * len(network.thresholds)
        if not network.guards:
            assert len(self.auxiliary_names) == expected + (network.m if flat else 0)

    def var(self, suffix: str) -> Affine:
        name = self.prefix + suffix
        if name in self.auxiliary_names:
            raise ValueError(f'Duplicate variable: {name}')
        self.auxiliary_names.append(name)
        return Affine.variable(name)

    def compare(self, value: Affine, threshold: int, tag: str) -> tuple[Affine, Affine]:
        b, c, v, w = [self.var(tag + '_' + z) for z in ('b', 'c', 'v', 'w')]
        self.polynomial.squares += [b + c - 1, value + v - (threshold - 1) - b - w]
        self.polynomial.products += [(self.prefix + tag + '_b', self.prefix + tag + '_v'),
                                     (self.prefix + tag + '_c', self.prefix + tag + '_w')]
        self.comparators.append((tag, value, threshold))
        return b, c

    def and_gate(self, a: Affine, b: Affine, tag: str) -> tuple[Affine, Affine]:
        e, p, q, c = [self.var(tag + '_' + z) for z in ('e', 'p', 'q', 'c')]
        self.polynomial.squares += [a - e - p, b - e - q, e + c - 1]
        self.polynomial.products.append((self.prefix + tag + '_p', self.prefix + tag + '_q'))
        self.conjunctions.append((tag, a, b))
        return e, c

    def canonical_assignment(self, x: Sequence[int], f: Sequence[int],
                             y: Sequence[int] | None = None) -> dict[str, int] | None:
        """Return the unique auxiliary assignment for a legal f, or None.

        If an explicit y is supplied, reject it unless it is the actual output.
        This method is a witness constructor, not a search for arbitrary roots.
        """
        net = self.network
        if not net.legal(x, f, self.flat):
            return None
        r = net.residual(x, f)
        actual_y = tuple(self.retention[i] * r[i] + sum(net.produce[j][i] * f[j]
                                                       for j in range(net.m)) for i in range(net.d))
        if y is not None and tuple(y) != actual_y:
            return None
        a = dict(zip(self.input_names, x))
        a.update(zip(self.output_names, actual_y))
        def setv(name: str, value: int) -> None:
            a[self.prefix + name] = value
        for j, value in enumerate(f):
            setv(f'f{j}', value)
        for i, value in enumerate(r):
            setv(f'r{i}', value)
        for tag, expression, threshold in self.comparators:
            value = expression.evaluate(a)
            b = int(value >= threshold)
            for name, v in zip(('b', 'c', 'v', 'w'),
                               (b, 1-b, 0 if b else threshold-1-value,
                                value-threshold if b else 0)):
                setv(tag + '_' + name, v)
        for tag, first, second in self.conjunctions:
            u, v = first.evaluate(a), second.evaluate(a)
            e = min(u, v)
            for name, value in zip(('e', 'p', 'q', 'c'), (e, u-e, v-e, 1-e)):
                setv(tag + '_' + name, value)
        enabled = net.enabled(x)
        for j, col in enumerate(net.consume):
            k = sum(v > 0 for v in col)
            sufficient = sum(r[i] >= v for i, v in enumerate(col) if v)
            s = k - int(enabled[j]) - sufficient
            if self.flat:
                setv(f'g{j}', 1-f[j])
                s += f[j]
            setv(f's{j}', s)
        if any(not natural(a[k]) for k in self.auxiliary_names):
            raise AssertionError('Canonical construction produced an invalid witness.')
        if self.polynomial.evaluate(a) != 0:
            raise AssertionError('Canonical construction failed its polynomial.')
        return a

    def as_dict(self) -> dict:
        return {'description': 'One-round witness-faithful quadratic; all coordinates natural.',
                'consume_columns': self.network.consume, 'produce_columns': self.network.produce,
                'flat': self.flat, 'retention': self.retention,
                'input_names': self.input_names, 'output_names': self.output_names,
                'auxiliary_names': self.auxiliary_names, 'polynomial': self.polynomial.as_dict()}



class HistoryCertificate:
    """Base unguarded, ordinary, retaining semantics; optionally first halting.

    Compiles a horizon-dependent polynomial, not a fixed-arity polynomial
    for an unbounded running time. Initial state coordinates are free inputs.
    """
    def __init__(self, network: Network, steps: int, *, first_halt: bool = False) -> None:
        if network.guards:
            raise ValueError('HistoryCertificate currently supports unguarded networks only.')
        if not natural(steps):
            raise ValueError('Invalid horizon.')
        self.network, self.steps, self.first_halt = network, steps, first_halt
        self.polynomial = Quadratic()
        self.initial_names = [f'state0_{i}' for i in range(network.d)]
        self.witness_names: list[str] = []
        self.rounds: list[tuple[RoundCertificate, dict[str, str]]] = []
        self.terminal_comparators: list[tuple[int, int, str]] = []
        for t in range(steps):
            compiler = RoundCertificate(network, prefix=f't{t}_')
            rename = {compiler.input_names[i]: f'state{t}_{i}' for i in range(network.d)}
            rename.update({compiler.output_names[i]: f'state{t+1}_{i}' for i in range(network.d)})
            self.rounds.append((compiler, rename))
            self.witness_names += [f'state{t+1}_{i}' for i in range(network.d)]
            self.witness_names += compiler.auxiliary_names
            self.polynomial.squares += [Affine({rename.get(k,k): c for k,c in a.coefficients.items()},
                                                 a.constant) for a in compiler.polynomial.squares]
            self.polynomial.products += [(rename.get(a,a), rename.get(b,b))
                                          for a,b in compiler.polynomial.products]
            if first_halt:
                name = f'nonempty{t}'
                self.witness_names.append(name)
                self.polynomial.squares.append(sum(Affine.variable(f't{t}_f{j}')
                                                    for j in range(network.m)) -
                                                Affine.variable(name) - 1)
        if first_halt:
            for i,a in network.thresholds:
                tag = f'term{i}_{a}'
                names = [tag+'_'+z for z in ('b','c','v','w')]
                self.witness_names += names
                b,c,v,w = map(Affine.variable,names)
                x = Affine.variable(f'state{steps}_{i}')
                self.polynomial.squares += [b+c-1, x+v-(a-1)-b-w]
                self.polynomial.products += [(names[0],names[2]),(names[1],names[3])]
                self.terminal_comparators.append((i,a,tag))
            for j,col in enumerate(network.consume):
                name = f'term_s{j}'
                self.witness_names.append(name)
                self.polynomial.squares.append(sum(Affine.variable(f'term{i}_{a}_b')
                                                    for i,a in enumerate(col) if a) +
                                                Affine.variable(name) - (sum(a>0 for a in col)-1))
        base = steps*(2*network.d+2*network.m+4*len(network.thresholds))
        expected = base + (steps+4*len(network.thresholds)+network.m if first_halt else 0)
        assert len(self.witness_names) == expected
        assert len(set(self.witness_names)) == len(self.witness_names)

    def canonical_assignment(self, initial: Sequence[int],
                             history: Sequence[Sequence[int]]) -> dict[str, int] | None:
        if len(history) != self.steps or len(initial) != self.network.d:
            return None
        if any(not natural(v) for v in initial):
            return None
        result = dict(zip(self.initial_names, initial))
        state = tuple(initial)
        for t, ((compiler, rename), extent) in enumerate(zip(self.rounds,history)):
            if self.first_halt and sum(extent) == 0:
                return None
            assignment = compiler.canonical_assignment(state,extent)
            if assignment is None:
                return None
            result.update({rename.get(k,k):v for k,v in assignment.items()})
            state = tuple(assignment[k] for k in compiler.output_names)
            if self.first_halt:
                result[f'nonempty{t}'] = sum(extent)-1
        if self.first_halt:
            if any(all(a <= state[i] for i,a in enumerate(col)) for col in self.network.consume):
                return None
            for i,a,tag in self.terminal_comparators:
                value = state[i]
                b = int(value >= a)
                for suffix,v in zip(('b','c','v','w'),
                                     (b,1-b,0 if b else a-1-value,value-a if b else 0)):
                    result[tag+'_'+suffix] = v
            for j,col in enumerate(self.network.consume):
                result[f'term_s{j}'] = sum(a>0 for a in col)-1-sum(
                    state[i]>=a for i,a in enumerate(col) if a)
        assert all(natural(result[k]) for k in self.witness_names)
        assert self.polynomial.evaluate(result) == 0
        return result

    def as_dict(self) -> dict:
        return {'description': 'Fixed-horizon exact extent-history quadratic.',
                'horizon': self.steps, 'first_halt': self.first_halt,
                'initial_names': self.initial_names, 'witness_names': self.witness_names,
                'polynomial': self.polynomial.as_dict()}

def rank_rational(rows: Sequence[Sequence[int]]) -> int:
    from fractions import Fraction
    a = [[Fraction(v) for v in row] for row in rows]
    if not a:
        return 0
    r = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        q = a[r][col]
        a[r] = [v/q for v in a[r]]
        for i in range(r+1, len(a)):
            q = a[i][col]
            a[i] = [x-q*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def resource_cover_rank(net: Network) -> tuple[int, tuple[int, ...]]:
    """Exact exhaustive row-cover search; exponential in species count."""
    best = net.m + 1
    best_cover: tuple[int, ...] = ()
    for bits in product((0, 1), repeat=net.d):
        cover = tuple(i for i, b in enumerate(bits) if b)
        if all(any(col[i] for i in cover) for col in net.consume):
            rank = rank_rational([[col[i] for col in net.consume] for i in cover])
            if rank < best:
                best, best_cover = rank, cover
    return best, best_cover


def trace_count(net: Network, x: tuple[int, ...], steps: int, *, flat: bool = False) -> int:
    if not natural(steps):
        raise ValueError('The horizon must be a nonnegative integer.')
    from functools import lru_cache
    @lru_cache(None)
    def count(state: tuple[int, ...], t: int) -> int:
        if t == 0:
            return 1
        return sum(count(y, t-1) for _, y in net.outcomes(state, flat))
    return count(x, steps)


if __name__ == '__main__':
    # A+B -> C, A -> B; x=(2,1,0), f=(1,1), y=(0,1,1).
    net = Network(((1,1,0), (1,0,0)), ((0,0,1), (0,1,0)))
    compiler = RoundCertificate(net)
    witness = compiler.canonical_assignment((2,1,0), (1,1))
    print(json.dumps({'certificate': compiler.as_dict(), 'witness': witness}, indent=2))
