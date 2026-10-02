"""Exact, witness-faithful Diophantine-to-thermal compiler (Python 3.10+).

All arithmetic is over nonnegative Python integers; floats and bools are
rejected.  There is no universal-machine polynomial hard-coded here.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction
from itertools import product
from typing import Callable, Mapping, Sequence


def natural(x: int, name: str = 'value') -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f'{name} must be an exact nonnegative int')
    return x


@dataclass(frozen=True)
class Atom:
    kind: str
    value: int

    def evaluate(self, modes: Sequence[int], parameters: Sequence[int]) -> int:
        if self.kind == 'const':
            return self.value
        if self.kind == 'mode':
            return modes[self.value]
        if self.kind == 'param':
            return parameters[self.value]
        raise ValueError('invalid atom')


@dataclass(frozen=True)
class Gate:
    operation: str
    left: Atom
    right: Atom
    output: int


class Compiler:
    """Build a natural +/* circuit; gate count includes only materialized gates."""
    def __init__(self, inputs: int, parameters: int = 0):
        self.inputs = natural(inputs, 'inputs')
        self.parameters = natural(parameters, 'parameters')
        self.gates: list[Gate] = []
        self._cache: dict[tuple, Atom] = {}

    def variable(self, i: int) -> Atom:
        natural(i)
        if i >= self.inputs:
            raise ValueError('input index out of range')
        return Atom('mode', i)

    def parameter(self, i: int) -> Atom:
        natural(i)
        if i >= self.parameters:
            raise ValueError('parameter index out of range')
        return Atom('param', i)

    def constant(self, n: int) -> Atom:
        return Atom('const', natural(n))

    def _gate(self, op: str, a: Atom, b: Atom) -> Atom:
        if a.kind == b.kind == 'const':
            return self.constant(a.value + b.value if op == 'add' else a.value * b.value)
        zero, one = self.constant(0), self.constant(1)
        if op == 'add':
            if a == zero: return b
            if b == zero: return a
        else:
            if a == zero or b == zero: return zero
            if a == one: return b
            if b == one: return a
        # Natural + and * are commutative; this only identifies circuit gates.
        a, b = sorted((a, b), key=lambda t: (t.kind, t.value))
        key = (op, a, b)
        if key not in self._cache:
            out = self.inputs + len(self.gates)
            self.gates.append(Gate(op, a, b, out))
            self._cache[key] = Atom('mode', out)
        return self._cache[key]

    def add(self, a: Atom, b: Atom) -> Atom:
        return self._gate('add', a, b)

    def multiply(self, a: Atom, b: Atom) -> Atom:
        return self._gate('mul', a, b)

    def power(self, a: Atom, n: int) -> Atom:
        n = natural(n)
        out = self.constant(1)
        while n:
            if n & 1:
                out = self.multiply(out, a)
            n //= 2
            if n:
                a = self.multiply(a, a)
        return out

    def finish(self, left: Atom, right: Atom) -> 'Compiled':
        return Compiled(self.inputs, self.parameters, tuple(self.gates), left, right)


@dataclass(frozen=True)
class Compiled:
    inputs: int
    parameters: int
    gates: tuple[Gate, ...]
    left: Atom
    right: Atom

    @property
    def modes(self) -> int:
        return self.inputs + len(self.gates) + 1

    @property
    def equations(self) -> int:
        return len(self.gates) + 2

    @property
    def local_terms(self) -> int:
        return (self.modes + 1) * self.equations

    def _parameters(self, params: Sequence[int]) -> tuple[int, ...]:
        if len(params) != self.parameters:
            raise ValueError('wrong number of parameters')
        return tuple(natural(x, 'parameter') for x in params)

    def canonical(self, inputs: Sequence[int], params: Sequence[int] = ()) -> tuple[int, ...]:
        if len(inputs) != self.inputs:
            raise ValueError('wrong number of input witnesses')
        values = [natural(x, 'input witness') for x in inputs]
        ps = self._parameters(params)
        for g in self.gates:
            a, b = g.left.evaluate(values, ps), g.right.evaluate(values, ps)
            values.append(a + b if g.operation == 'add' else a * b)
        values.append(1)   # marker forbids a zero-energy occupation vacuum
        return tuple(values)

    def residuals(self, modes: Sequence[int], params: Sequence[int] = ()) -> tuple[int, ...]:
        if len(modes) != self.modes:
            raise ValueError('wrong number of modes')
        ns = tuple(natural(x, 'mode') for x in modes)
        ps = self._parameters(params)
        out = []
        for g in self.gates:
            a, b = g.left.evaluate(ns, ps), g.right.evaluate(ns, ps)
            out.append(ns[g.output] - (a + b if g.operation == 'add' else a * b))
        out.extend((self.left.evaluate(ns, ps) - self.right.evaluate(ns, ps), ns[-1] - 1))
        return tuple(out)

    def penalty(self, modes: Sequence[int], params: Sequence[int] = ()) -> int:
        return sum(r * r for r in self.residuals(modes, params))

    def energy(self, modes: Sequence[int], params: Sequence[int] = ()) -> int:
        return (1 + sum(modes)) * self.penalty(modes, params)

    def export(self) -> dict:
        result = asdict(self)
        result.update(modes=self.modes, equations=self.equations,
                      local_terms=self.local_terms, degree_bound=5)
        return result


def compile_polynomial(terms: Mapping[tuple[int, ...], int], inputs: int,
                       parameters: int = 0) -> Compiled:
    """Compile P=0. Exponents are ordered: parameters first, then witnesses."""
    c = Compiler(inputs, parameters)
    atoms = [c.parameter(i) for i in range(parameters)] + [c.variable(i) for i in range(inputs)]
    sides = [c.constant(0), c.constant(0)]
    for powers, coefficient in sorted(terms.items()):
        if len(powers) != len(atoms) or type(coefficient) is not int:
            raise ValueError('invalid sparse integer polynomial')
        for e in powers:
            natural(e, 'exponent')
        if coefficient == 0:
            continue
        term = c.constant(abs(coefficient))
        for a, e in zip(atoms, powers):
            term = c.multiply(term, c.power(a, e))
        side = 0 if coefficient > 0 else 1
        sides[side] = c.add(sides[side], term)
    return c.finish(*sides)


@dataclass(frozen=True)
class Interval:
    lower: Fraction
    upper: Fraction
    cutoff: int
    energy_cutoff: int
    visited: int

    @property
    def width(self) -> Fraction:
        return self.upper - self.lower


def partition_interval(energy: Callable[[tuple[int, ...]], int], modes: int,
                       q: Fraction, t: Fraction, tolerance: Fraction,
                       excited_only: bool = False,
                       max_points: int = 2_000_000) -> Interval:
    """Certified enclosure by exact rational sums and proven geometric tails.

    Precondition on energy: integer >=0; if positive, >=1+sum(n).
    excited_only=True discards zero states and permits t=1.
    Large-energy terms are discarded WITH a certified error bound, avoiding
    gigantic rational denominators. An explicit resource limit raises an
    exception; it never silently turns a partial calculation into a certificate.
    """
    natural(modes, 'modes')
    if modes == 0:
        raise ValueError('at least one mode is required')
    if not all(type(v) is Fraction for v in (q, t, tolerance)):
        raise ValueError('q, t, tolerance must be exact Fractions')
    if not (0 < q < 1 and 0 <= t <= 1 and tolerance > 0):
        raise ValueError('parameters outside valid range')
    if not excited_only and t == 1:
        raise ValueError('full unconfined trace is not an effective input')
    if t == 0:
        h = natural(energy((0,) * modes), 'energy')
        value = Fraction(0) if excited_only and h == 0 else q ** h
        return Interval(value, value, 0, h + 1, 1)
    rho = q * t if excited_only else t
    factor = q if excited_only else Fraction(1)
    B = 0
    tail = modes * factor * rho ** (B + 1) / (1 - rho) ** modes
    while tail > tolerance / 2:
        B += 1
        tail *= rho
    points = (B + 1) ** modes
    if points > max_points:
        raise RuntimeError(f'request needs {points} points, above limit {max_points}')
    cap = 1
    omitted = points * q
    while omitted > tolerance / 2:
        cap += 1
        omitted *= q
    total = Fraction(0)
    qpower = [q ** i for i in range(cap)]
    tpowers = [t ** i for i in range(modes * B + 1)]
    for ns in product(range(B + 1), repeat=modes):
        h = natural(energy(ns), 'energy')
        if h > 0 and h < 1 + sum(ns):
            raise ValueError('energy violates the radial lower-bound precondition')
        if excited_only and h == 0:
            continue
        if h < cap:
            total += qpower[h] * tpowers[sum(ns)]
    return Interval(total, total + tail + omitted, B, cap, points)


def critical_fugacity(energy: Callable[[tuple[int, ...]], int], modes: int,
                      tolerance: Fraction = Fraction(1, 1024),
                      ground_series: Callable[[Fraction], Fraction] | None = None,
                      max_points: int = 2_000_000) -> tuple[Fraction, Fraction, int]:
    """Enclose the 1/2 crossing, or endpoint 1 when there is no crossing.

    Requires energy(0)>=1. A supplied ground_series is an externally justified
    exact formula, not inferred from a finite sample. Without it, the general
    certified full-partition evaluator is used.
    """
    if not 0 < tolerance < Fraction(1, 4):
        raise ValueError('tolerance must be between 0 and 1/4')
    if energy((0,) * modes) < 1:
        raise ValueError('the occupation vacuum must not be a zero state')
    q = Fraction(1, 8 * (modes + 1))
    a, b, calls = Fraction(0), Fraction(1), 0
    delta = tolerance / 16
    while b - a > tolerance:
        m = (a + b) / 2
        iv = partition_interval(energy, modes, q, m, delta,
                                excited_only=ground_series is not None,
                                max_points=max_points)
        shift = Fraction(0) if ground_series is None else ground_series(m)
        lo, hi = iv.lower + shift, iv.upper + shift
        calls += 1
        if hi < Fraction(1, 2):
            a = m
        elif lo > Fraction(1, 2):
            b = m
        else:
            # |Z(m)-1/2|<=delta and Z' >= 1/4 near the crossing.
            a, b = max(a, m - 4 * delta), min(b, m + 4 * delta)
            break
    return a, b, calls
