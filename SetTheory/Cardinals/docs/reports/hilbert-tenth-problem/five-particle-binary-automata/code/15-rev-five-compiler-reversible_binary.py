"""Validated finite guarded-swap compiler. Proof: COMPILER_PROOF.md.

Construct a rule only with ``compile_source`` and the JSON schema in
SOURCE_SCHEMA.md. Returned records and their data are immutable snapshots.
The finite-support interpreter accepts sets/frozensets of exact Python ints;
its rule also has the full-shift mathematical definition given in the proof.
No universal source table is bundled.
"""
from dataclasses import dataclass, field
from types import MappingProxyType

__all__ = ['compile_source', 'CompiledSource', 'Compiler', 'Branch', 'Gate']


def _integer(value, path, minimum=None):
    if type(value) is not int:
        raise TypeError(f'{path} must be an exact integer (not bool or float)')
    if minimum is not None and value < minimum:
        raise ValueError(f'{path} must be at least {minimum}')
    return value


def _string(value, path):
    if type(value) is not str:
        raise TypeError(f'{path} must be a string')
    return value


def _boolean(value, path):
    if type(value) is not bool:
        raise TypeError(f'{path} must be a Boolean')
    return value


def _array(value, path):
    if type(value) is not list:
        raise TypeError(f'{path} must be a JSON array (list)')
    return value


def _object(value, keys, path):
    if type(value) is not dict:
        raise TypeError(f'{path} must be a JSON object (dict)')
    if any(type(key) is not str for key in value):
        raise TypeError(f'{path} object keys must be strings')
    if set(value) != set(keys):
        raise ValueError(f'{path} must have exactly the keys {", ".join(keys)}')
    return value


def _positions(value):
    if type(value) not in (set, frozenset):
        raise TypeError('positions must be a set or frozenset of exact integers')
    if any(type(z) is not int for z in value):
        raise TypeError('positions must contain only exact integers, not bool or float')
    return frozenset(value)


def _record(cls, **values):
    """Private construction after validation; no user-supplied behavior is stored."""
    obj = object.__new__(cls)
    for name, value in values.items():
        object.__setattr__(obj, name, value)
    return obj


def _parse_guard(root, path):
    """Validate without recursion; produce frozen JSON and a finite postfix program."""
    pending = [(root, False)]
    active = set()
    results, program, atoms = [], [], []
    while pending:
        node, leaving = pending.pop()
        if not leaving:
            if type(node) is not dict:
                raise TypeError(f'{path} nodes must be JSON objects (dicts)')
            if any(type(key) is not str for key in node):
                raise TypeError(f'{path} object keys must be strings')
            if id(node) in active:
                raise ValueError(f'{path} must be finite and acyclic')
            if 'op' not in node:
                raise ValueError(f'{path} node is missing op')
            op = _string(node['op'], f'{path}.op')
            if op == 'true':
                _object(node, ('op',), path)
                children = ()
            elif op in ('eq', 'gt'):
                _object(node, ('op', 'counter', 'value'), path)
                counter = _integer(node['counter'], f'{path}.counter')
                if counter not in (0, 1):
                    raise ValueError(f'{path}.counter must be 0 or 1')
                k = _integer(node['value'], f'{path}.value', 0)
                atoms.append((counter, k))
                children = ()
            elif op in ('and', 'or'):
                _object(node, ('op', 'args'), path)
                children = _array(node['args'], f'{path}.args')
            elif op == 'not':
                _object(node, ('op', 'arg'), path)
                children = (node['arg'],)
            else:
                raise ValueError(f'{path} has unknown operation {op!r}')
            active.add(id(node))
            pending.append((node, True))
            pending.extend((child, False) for child in reversed(children))
        else:
            op = node['op']
            frozen = {'op': op}
            if op in ('eq', 'gt'):
                frozen.update(counter=node['counter'], value=node['value'])
                program.append((op, node['counter'], node['value']))
            elif op in ('and', 'or'):
                n = len(node['args'])
                children = tuple(results[-n:]) if n else ()
                if n:
                    del results[-n:]
                frozen['args'] = children
                program.append((op, n))
            elif op == 'not':
                frozen['arg'] = results.pop()
                program.append((op,))
            else:
                program.append((op,))
            results.append(MappingProxyType(frozen))
            active.remove(id(node))
    return results[0], tuple(program), tuple(atoms)


def _evaluate(program, counters):
    values = []
    for instruction in program:
        op = instruction[0]
        if op == 'true':
            values.append(True)
        elif op == 'eq':
            values.append(counters[instruction[1]] == instruction[2])
        elif op == 'gt':
            values.append(counters[instruction[1]] > instruction[2])
        elif op == 'not':
            values[-1] = not values[-1]
        else:
            n = instruction[1]
            operands = values[-n:] if n else ()
            result = all(operands) if op == 'and' else any(operands)
            if n:
                del values[-n:]
            values.append(result)
    return values[0]


@dataclass(frozen=True, slots=True, init=False)
class Branch:
    """Immutable branch with precomputed domain/image class truth tables."""
    name: str
    source: str
    target: str
    side: int
    delta: int
    J: int
    domain_table: tuple = field(repr=False)
    image_table: tuple = field(repr=False)

    def __init__(self, *args, **kwargs):
        raise TypeError('Branch cannot be constructed directly; use compile_source')

    def guard(self, c0, c1):
        """Evaluate the source predicate on two exact natural-number counters."""
        _integer(c0, 'counter 0', 0)
        _integer(c1, 'counter 1', 0)
        return self.domain_table[min(c0, self.J + 1)][min(c1, self.J + 1)]

    def image_guard(self, c0, c1):
        _integer(c0, 'counter 0', 0)
        _integer(c1, 'counter 1', 0)
        return self.image_table[min(c0, self.J + 1)][min(c1, self.J + 1)]


@dataclass(frozen=True, slots=True, init=False)
class _ClassGuard:
    J: int
    Z: int
    table: tuple = field(repr=False)

    def __init__(self, *args, **kwargs):
        raise TypeError('Context guards are private compiler data')

    def allows(self, x, u):
        classes = []
        for side in (-1, 1):
            found = [k for k in range(self.J + 1) if u + side * (self.Z + k) in x]
            if len(found) > 1:
                return False
            classes.append(found[0] if found else self.J + 1)
        return self.table[classes[0]][classes[1]]


@dataclass(frozen=True, slots=True, init=False)
class Gate:
    """One immutable local factor; obtained from a compiled rule's E or P tuple."""
    name: str
    P: frozenset
    Q: frozenset
    B: int
    L: int
    M: int
    radius: int
    guard: object = field(repr=False)
    shapes: tuple

    def __init__(self, *args, **kwargs):
        raise TypeError('Gate cannot be constructed directly; use compile_source')

    def _raw(self, x):
        out = {}
        for label, shape in enumerate(self.shapes):
            for first in x:
                u = first - shape[0]
                if (all(u + p in x for p in shape)
                        and sum(u - self.B <= z <= u + self.B for z in x) == len(shape)):
                    if u in out and out[u] != label:
                        raise RuntimeError('Internal gate invariant: ambiguous raw occurrence')
                    out[u] = label
        return out

    def raw(self, x):
        return self._raw(_positions(x))

    def _apply(self, x, verify):
        raw = self._raw(x)
        active = []
        for u, label in raw.items():
            shape = self.shapes[label]
            if sum(u - self.L <= z <= u + self.L for z in x) != len(shape):
                continue
            if any(0 < abs(v - u) <= self.M for v in raw):
                continue
            if self.guard is not None and not self.guard.allows(x, u):
                continue
            active.append((u, label))
        if not active:
            return x
        y = set(x)
        for u, label in active:
            y.difference_update(u + p for p in self.shapes[label])
            y.update(u + p for p in self.shapes[1 - label])
        y = frozenset(y)
        if verify:
            if len(y) != len(x):
                raise RuntimeError('Gate failed finite particle conservation')
            if set(self._raw(y)) != set(raw):
                raise RuntimeError('Gate changed raw occurrence keys')
            if self._apply(y, False) != x:
                raise RuntimeError('Gate failed involution verification')
        return y

    def apply(self, x, verify=False):
        return self._apply(_positions(x), _boolean(verify, 'verify'))


def _make_gate(name, P, Q, B, guard=None, T=0):
    _string(name, 'gate name')
    P, Q = _positions(P), _positions(Q)
    _integer(B, 'gate B', 0)
    _integer(T, 'gate T', 0)
    if type(guard) is not _ClassGuard and guard is not None:
        raise TypeError('Only immutable compiler class guards are supported')
    if len(P) != len(Q) or len(P) < 2:
        raise ValueError('Gate shapes must have equal mass at least two')
    if min(P) < -B or max(P) > B or min(Q) < -B or max(Q) > B:
        raise ValueError('Gate shapes must lie in [-B, B]')
    if {p - min(P) for p in P} == {q - min(Q) for q in Q}:
        raise ValueError('Gate shapes must not be translates')
    L = 3 * B + 1
    M = max(L + B, T + B) + 1
    return _record(Gate, name=name, P=P, Q=Q, B=B, L=L, M=M,
                   radius=M + 2 * B, guard=guard,
                   shapes=(tuple(sorted(P)), tuple(sorted(Q))))


@dataclass(frozen=True, slots=True, init=False)
class CompiledSource:
    """Fixed rule and immutable source snapshot; constructed by compile_source."""
    controls: tuple
    branches: tuple = field(repr=False)
    J: int
    p: int
    a: int
    m: int
    modes: tuple
    gap: object = field(repr=False)
    D: int
    S: int
    B2: int
    L: int
    B3: int
    Z: int
    E: tuple = field(repr=False)
    P: tuple = field(repr=False)
    radius: int
    start: str
    halt: str
    source_data: object = field(repr=False)

    def __init__(self, *args, **kwargs):
        raise TypeError('CompiledSource/Compiler cannot be constructed directly; use compile_source')

    def encode(self, q, c0, c1, sign='+'):
        _string(q, 'control')
        if q not in self.controls:
            raise ValueError('Unknown control')
        _integer(c0, 'counter 0', 0)
        _integer(c1, 'counter 1', 0)
        _string(sign, 'sign')
        if sign not in ('+', '-'):
            raise ValueError("sign must be '+' or '-'")
        return frozenset((-self.Z - c0, 0, self.Z + c1, self.S,
                          self.S + self.gap[(('H', q), sign)]))

    def step(self, x, inverse=False, verify=False):
        x = _positions(x)
        _boolean(inverse, 'inverse')
        _boolean(verify, 'verify')
        seq = self.E + self.P
        if inverse:
            seq = reversed(seq)
        for gate in seq:
            x = gate._apply(x, verify)
        return x

    def ledger(self):
        return dict(m=self.m, p=self.p, a=self.a, J=self.J, D=self.D,
                    S=self.S, B2=self.B2, L=self.L, B3=self.B3, Z=self.Z,
                    E=len(self.E), P=len(self.P), factors=len(self.E) + len(self.P),
                    radius=self.radius, observer_length=3 * self.D + 3,
                    particles=5, alphabet=[0, 1])


# Kept as a type alias for callers inspecting previously named compiler objects.
# Like CompiledSource, this is not a construction entry point.
Compiler = CompiledSource


def _compile_validated(controls, branches, J, start, halt, snapshot):
    moving = tuple(e for e in branches if e.delta)
    p, a, m = len(moving), len(branches) - len(moving), len(controls)
    modes = tuple([('H', q) for q in controls]
                  + [(kind, e.name) for e in moving for kind in ('O', 'I')])
    gap = {(mode, sign): i + 1 for i, (mode, sign) in
           enumerate((mode, sign) for mode in modes for sign in ('+', '-'))}
    D = len(gap)
    S, B2, L, B3 = 2 * D + 2, D + 1, 3 * D + 4, 4 * D + 5
    Z = 10 * B3 + 10 + 2 * J
    E, P = [], []

    def pair(mode, sign, x=0):
        return {x, x + gap[mode, sign]}

    def triple(mode, sign, x):
        return {0} | pair(mode, sign, x)

    def gate(block, name, left, right, B, guard=None):
        T = Z + J if guard is not None else 0
        block.append(_make_gate(name, left, right, B, guard, T))

    def guard(e, inverse=False):
        return _record(_ClassGuard, J=J, Z=Z,
                       table=e.image_table if inverse else e.domain_table)

    for e in moving:
        for kind, w in [('O', e.side), ('I', -e.side)]:
            mode = (kind, e.name)
            gate(E, f'free:{mode}', pair(mode, '+'), pair(mode, '-', w), B2)
            gate(P, f'phase-free:{mode}', pair(mode, '+'), pair(mode, '-'), B2)
            for t in range(S, L + 1):
                gate(E, f'behind:{mode}:{t}', triple(mode, '+', w * t),
                     triple(mode, '-', w * (t + 1)), B3)
            for t in range(S + 1, L + 1):
                gate(E, f'ahead:{mode}:{t}', triple(mode, '+', -w * t),
                     triple(mode, '-', -w * (t - 1)), B3)
            for side in (-1, 1):
                for t in range(S, L + 1):
                    gate(P, f'phase-near:{mode}:{side}:{t}',
                         triple(mode, '+', side * t), triple(mode, '-', side * t), B3)
        v = e.side
        gate(E, f'dispatch:{e.name}', triple(('H', e.source), '+', S),
             triple(('O', e.name), '-', v * S), B3, guard(e))
        gate(E, f'endpoint:{e.name}', triple(('O', e.name), '+', -v * S),
             {v * e.delta} | pair(('I', e.name), '-', v * e.delta - v * S), B3)
        gate(E, f'commit:{e.name}', triple(('I', e.name), '+', v * S),
             triple(('H', e.target), '-', S), B3, guard(e, True))
    for e in branches:
        if not e.delta:
            gate(E, f'direct:{e.name}', triple(('H', e.source), '+', S),
                 triple(('H', e.target), '-', S), B3, guard(e))
    for q in controls:
        gate(P, f'phase-home:{q}', triple(('H', q), '+', S),
             triple(('H', q), '-', S), B3)
    expected = 8 * p * D + 29 * p + m + a
    if len(E) + len(P) != expected:
        raise RuntimeError('Internal compiler factor-count invariant failed')
    radius = sum(g.radius for g in E + P)
    bound = (4 * p * (6 * D + 8) + (8 * p * D + 23 * p + m) * (24 * D + 32)
             + (2 * p + a) * (Z + J + 12 * D + 16))
    if radius != bound:
        raise RuntimeError('Internal compiler radius invariant failed')
    return _record(CompiledSource, controls=controls, branches=branches, J=J,
                   p=p, a=a, m=m, modes=modes, gap=MappingProxyType(gap),
                   D=D, S=S, B2=B2, L=L, B3=B3, Z=Z, E=tuple(E), P=tuple(P),
                   radius=radius, start=start, halt=halt, source_data=snapshot)


def compile_source(data):
    """Validate a finite JSON source and return its immutable compiled rule.

    Invalid types raise TypeError; invalid schema/semantics raise ValueError.
    Validation and optional runtime verification remain active under python -O.
    Exact field/type rules, including rejection of extra keys, are documented in
    SOURCE_SCHEMA.md. Input containers are never retained.
    """
    _object(data, ('schema', 'controls', 'start', 'halt', 'class_cut', 'branches'), 'source')
    if _string(data['schema'], 'schema') != 'reversible-two-counter-v1':
        raise ValueError('Unknown source schema')
    controls = tuple(_string(q, 'control') for q in _array(data['controls'], 'controls'))
    if len(set(controls)) != len(controls):
        raise ValueError('Control names must be unique')
    J = _integer(data['class_cut'], 'class_cut', 0)
    start, halt = _string(data['start'], 'start'), _string(data['halt'], 'halt')
    if start not in controls or halt not in controls:
        raise ValueError('start and halt must name declared controls')
    rows = _array(data['branches'], 'branches')
    names, branches, frozen_rows = set(), [], []
    for i, row in enumerate(rows):
        path = f'branches[{i}]'
        _object(row, ('name', 'source', 'target', 'side', 'delta', 'guard'), path)
        name = _string(row['name'], f'{path}.name')
        if name in names:
            raise ValueError('Branch names must be unique')
        names.add(name)
        source, target = (_string(row[k], f'{path}.{k}') for k in ('source', 'target'))
        if source not in controls or target not in controls:
            raise ValueError('Branch source and target must name declared controls')
        if source == halt:
            raise ValueError('The designated halt control must have no exits')
        side, delta = (_integer(row[k], f'{path}.{k}') for k in ('side', 'delta'))
        if side not in (-1, 1) or delta not in (-1, 0, 1):
            raise ValueError('side must be -1 or 1; delta must be -1, 0, or 1')
        idx = 0 if side == -1 else 1
        frozen_guard, program, atoms = _parse_guard(row['guard'], f'{path}.guard')
        for counter, k in atoms:
            if k > J or k + (delta if counter == idx else 0) > J:
                raise ValueError('class_cut is insufficient for a guard or image threshold')
        domain, image = [], []
        for c0 in range(J + 2):
            domain_row, image_row = [], []
            for c1 in range(J + 2):
                c = (c0, c1)
                enabled = _evaluate(program, c)
                if enabled and c[idx] + delta < 0:
                    raise ValueError('Guard permits a negative post-counter')
                domain_row.append(enabled)
                old = list(c)
                old[idx] -= delta
                image_row.append(min(old) >= 0 and _evaluate(program, old))
            domain.append(tuple(domain_row))
            image.append(tuple(image_row))
        branches.append(_record(Branch, name=name, source=source, target=target,
                                side=side, delta=delta, J=J,
                                domain_table=tuple(domain), image_table=tuple(image)))
        frozen_rows.append(MappingProxyType(dict(name=name, source=source, target=target,
                                                side=side, delta=delta, guard=frozen_guard)))
    branches = tuple(branches)
    # The cut ensures source and image predicates are constant on every product
    # class, so these representative checks prove global domain/image disjointness.
    for q in controls:
        outgoing = tuple(e for e in branches if e.source == q)
        incoming = tuple(e for e in branches if e.target == q)
        for c0 in range(J + 2):
            for c1 in range(J + 2):
                if sum(e.domain_table[c0][c1] for e in outgoing) > 1:
                    raise ValueError(f'Overlapping branch domains at {q!r}, class {(c0, c1)}')
                if sum(e.image_table[c0][c1] for e in incoming) > 1:
                    raise ValueError(f'Overlapping branch images at {q!r}, class {(c0, c1)}')
    snapshot = MappingProxyType(dict(schema='reversible-two-counter-v1', controls=controls,
                                    start=start, halt=halt, class_cut=J, branches=tuple(frozen_rows)))
    return _compile_validated(controls, branches, J, start, halt, snapshot)
