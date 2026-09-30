"""Witness-faithful Boolean circuit -> sparse coercive quartic compiler.

Standard-library implementation. Variables range over R for the geometric
statements, or over N for the Diophantine statements. Sparse monomials are
sorted tuples of variable indices, with repeated indices denoting powers.
This executable is a research prototype, not a proof-assistant certificate.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import Counter, defaultdict
from typing import Iterable, Sequence
import json

Monomial = tuple[int, ...]
Polynomial = dict[Monomial, int]


def add(p: Polynomial, q: Polynomial) -> Polynomial:
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + c
        if not out[m]:
            del out[m]
    return out


def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for m, c in p.items():
        for n, d in q.items():
            k = tuple(sorted(m + n))
            out[k] = out.get(k, 0) + c * d
    return {m: c for m, c in out.items() if c}


def evaluate_poly(p: Polynomial, values: Sequence):
    out = 0
    for m, c in p.items():
        v = c
        for i in m:
            v *= values[i]
        out += v
    return out


@dataclass(frozen=True)
class Gate:
    kind: str
    args: tuple[int, ...] = ()


@dataclass(frozen=True)
class Circuit:
    inputs: int
    gates: tuple[Gate, ...]
    output: int

    def __post_init__(self):
        if self.inputs < 0:
            raise ValueError('The number of inputs must be nonnegative.')
        arities = {'AND': 2, 'NOT': 1, 'COPY': 1, 'ZERO': 0, 'ONE': 0}
        for j, g in enumerate(self.gates):
            if g.kind not in arities or len(g.args) != arities[g.kind]:
                raise ValueError(f'Invalid gate: {g!r}')
            if any(a < 0 or a >= self.inputs + j for a in g.args):
                raise ValueError('Circuit operands must precede their gate.')
        if not 0 <= self.output < self.inputs + len(self.gates):
            raise ValueError('Output wire does not exist.')

    def run(self, bits: Sequence[int]) -> int:
        if len(bits) != self.inputs or any(b not in (0, 1) for b in bits):
            raise ValueError('Expected one Boolean value per input.')
        values = list(bits)
        for g in self.gates:
            a = [values[j] for j in g.args]
            values.append({'AND': lambda: a[0] * a[1],
                           'NOT': lambda: 1 - a[0],
                           'COPY': lambda: a[0],
                           'ZERO': lambda: 0,
                           'ONE': lambda: 1}[g.kind]())
        return values[self.output]


@dataclass(frozen=True)
class Constraint:
    kind: str
    out: int
    args: tuple[int, ...] = ()

    def polynomial(self) -> Polynomial:
        z = self.out
        if self.kind == 'AND':
            x, y = self.args
            return {(z,): 1, tuple(sorted((x, y))): -1}
        if self.kind == 'NOT':
            x, u = self.args
            return {(z,): 1, (x,): 1, (u,): -1}
        if self.kind in ('COPY', 'ACCEPT'):
            return {(z,): 1, (self.args[0],): -1}
        if self.kind == 'ZERO':
            return {(z,): 1}
        if self.kind == 'UNIT':
            return {(z,): 1, (): -1}
        raise ValueError(f'Unknown constraint: {self.kind}')

    def value(self, x: Sequence):
        return evaluate_poly(self.polynomial(), x)

    def support(self) -> set[int]:
        return {self.out, *self.args}

    def gradient(self, x: Sequence) -> dict[int, object]:
        z = self.out
        if self.kind == 'AND':
            a, b = self.args
            return {z: 1, a: -x[b], b: -x[a]}
        if self.kind == 'NOT':
            a, u = self.args
            return {z: 1, a: 1, u: -1}
        if self.kind in ('COPY', 'ACCEPT'):
            return {z: 1, self.args[0]: -1}
        return {z: 1}


@dataclass
class Compiled:
    circuit: Circuit
    variables: int
    constraints: list[Constraint]
    definitions: dict[int, Constraint]
    unit: int

    def extend(self, bits: Sequence[int]) -> tuple[int, ...]:
        if len(bits) != self.circuit.inputs or any(b not in (0, 1) for b in bits):
            raise ValueError('Expected one Boolean value per input.')
        # Iterative depth-first evaluation avoids Python's recursion-depth
        # limit for long source circuits. Numeric variable IDs are not a
        # topological ordering after occurrence routing.
        values = dict(enumerate(bits))
        active: set[int] = set()
        for root in range(self.variables):
            stack: list[tuple[int, bool]] = [(root, False)]
            while stack:
                v, ready = stack.pop()
                if v in values:
                    continue
                c = self.definitions[v]
                if not ready:
                    if v in active:
                        raise RuntimeError('Cyclic definition in compiler output.')
                    active.add(v)
                    stack.append((v, True))
                    stack.extend((a, False) for a in reversed(c.args)
                                 if a not in values)
                    continue
                a = [values[j] for j in c.args]
                if c.kind == 'UNIT': val = 1
                elif c.kind == 'ZERO': val = 0
                elif c.kind == 'COPY': val = a[0]
                elif c.kind == 'AND': val = a[0] * a[1]
                elif c.kind == 'NOT': val = a[1] - a[0]
                else: raise RuntimeError('Invalid defining constraint.')
                values[v] = val
                active.remove(v)
        return tuple(values[i] for i in range(self.variables))

    def energy(self, values: Sequence):
        if len(values) != self.variables:
            raise ValueError('Wrong coordinate dimension.')
        return sum((v * (v - 1)) ** 2 for v in values) + sum(
            c.value(values) ** 2 for c in self.constraints)

    def polynomial(self) -> Polynomial:
        p: Polynomial = {}
        for i in range(self.variables):
            b = {(i, i): 1, (i,): -1}
            p = add(p, multiply(b, b))
        for c in self.constraints:
            q = c.polynomial()
            p = add(p, multiply(q, q))
        return p

    def structural_statistics(self) -> dict:
        incidence = Counter()
        adjacency: dict[int, set[int]] = defaultdict(set)
        for c in self.constraints:
            support = c.support()
            incidence.update(support)
            for v in support:
                adjacency[v].update(support - {v})
        p = self.polynomial()
        return {
            'inputs': self.circuit.inputs,
            'original_gates': len(self.circuit.gates),
            'variables': self.variables,
            'nonboolean_constraints': len(self.constraints),
            'total_squared_residuals': self.variables + len(self.constraints),
            'max_incidence': max(incidence.values(), default=0),
            'max_interaction_degree': max(map(len, adjacency.values()), default=0),
            'degree': max(map(len, p), default=0),
            'coefficient_height': max(map(abs, p.values()), default=0),
            'constant_coefficient': p.get((), 0),
            'monomials': len(p),
        }

    def write_json(self, path: str) -> None:
        obj = {
            'format': 'quartic-probability-landscape-v1',
            'statistics': self.structural_statistics(),
            'circuit': {'inputs': self.circuit.inputs,
                        'gates': [{'kind': g.kind, 'args': list(g.args)}
                                  for g in self.circuit.gates],
                        'output': self.circuit.output},
            'constraints': [{'kind': c.kind, 'out': c.out, 'args': list(c.args)}
                            for c in self.constraints],
            'polynomial': [{'coefficient': c, 'variables': list(m)}
                           for m, c in sorted(self.polynomial().items())],
        }
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(obj, f, indent=2)
            f.write('\n')


def compile_circuit(circuit: Circuit) -> Compiled:
    """Compile with fresh occurrence wires, one trunk per used original wire,
    and binary copy trees. The interaction graph has maximum degree three.

    Every noninput variable has one defining constraint; the final ACCEPT
    constraint is the only additional non-Boolean constraint. All uses,
    including the terminal comparison and distributed unit, are routed.
    """
    k, s = circuit.inputs, len(circuit.gates)
    unit = k + s
    next_id = unit + 1
    raw: list[tuple[str, int | None, tuple[int, ...]]] = []
    for j, g in enumerate(circuit.gates):
        z = k + j
        if g.kind == 'NOT': args = g.args + (unit,)
        elif g.kind == 'ONE': args = (unit,)
        else: args = g.args
        kind = 'COPY' if g.kind == 'ONE' else g.kind
        raw.append((kind, z, args))
    raw.append(('ACCEPT', None, (circuit.output, unit)))
    uses: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for j, (_, _, args) in enumerate(raw):
        for pos, source in enumerate(args):
            uses[source].append((j, pos))
    routed: dict[tuple[int, int], int] = {}
    copies: list[Constraint] = []

    def new_child(parent: int) -> int:
        nonlocal next_id
        child = next_id
        next_id += 1
        copies.append(Constraint('COPY', child, (parent,)))
        return child

    def route(parent: int, targets: list[tuple[int, int]]) -> None:
        # One trunk edge isolates each original gate from the branching tree.
        # This makes the final variable-interaction graph subcubic.
        trunk = new_child(parent)
        if len(targets) == 1:
            routed[targets[0]] = trunk
        else:
            midpoint = len(targets) // 2
            grow(trunk, targets[:midpoint], targets[midpoint:])

    def grow(parent: int, left: list, right: list) -> None:
        for group in (left, right):
            child = new_child(parent)
            if len(group) == 1:
                routed[group[0]] = child
            else:
                split = len(group) // 2
                grow(child, group[:split], group[split:])

    for source, targets in sorted(uses.items()):
        route(source, targets)
    constraints = [Constraint('UNIT', unit)] + copies
    for j, (kind, out, args) in enumerate(raw):
        a = tuple(routed[(j, pos)] for pos in range(len(args)))
        if kind == 'ACCEPT':
            constraints.append(Constraint('ACCEPT', a[0], (a[1],)))
        else:
            assert out is not None
            constraints.append(Constraint(kind, out, a))
    definitions = {c.out: c for c in constraints if c.kind != 'ACCEPT'}
    result = Compiled(circuit, next_id, constraints, definitions, unit)
    # These are executable structural assertions, not substitutes for the proof.
    assert len(definitions) == next_id - k
    assert len(constraints) == next_id - k + 1
    assert next_id <= k + 5 * s + 5
    assert all(len(c.support()) == 1 + len(c.args) for c in constraints)
    return result


def or_circuit(inputs: int) -> Circuit:
    """Accept iff at least one of the supplied bits is one."""
    if inputs < 0:
        raise ValueError('Negative input count.')
    if inputs == 0:
        return Circuit(0, (Gate('ZERO'),), 0)
    gates: list[Gate] = []
    z = 0
    for bit in range(1, inputs):
        a = inputs + len(gates); gates.append(Gate('NOT', (z,)))
        b = inputs + len(gates); gates.append(Gate('NOT', (bit,)))
        c = inputs + len(gates); gates.append(Gate('AND', (a, b)))
        z = inputs + len(gates); gates.append(Gate('NOT', (c,)))
    return Circuit(inputs, tuple(gates), z)


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--or-inputs', type=int, default=3)
    parser.add_argument('--output', default='landscape.json')
    args = parser.parse_args()
    compiled = compile_circuit(or_circuit(args.or_inputs))
    compiled.write_json(args.output)
    print(json.dumps(compiled.structural_statistics(), indent=2))
