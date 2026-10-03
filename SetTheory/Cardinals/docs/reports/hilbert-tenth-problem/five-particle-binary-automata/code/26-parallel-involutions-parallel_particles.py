"""Prospectively isolated parallel involutions, a NEW rule off valid states.

Finite-support reference interpreter of PROOF.md. The frozen source compiler
supplies immutable endpoint templates only; none of its ordered gate execution
is used by ParallelCompiler.step. This research implementation materializes
small source template arrays and does not claim source-sized universal execution.
"""
from dataclasses import dataclass
from frozen_reversible_binary import compile_source

__all__ = ['ParallelCompiler']


def _positions(x):
    if type(x) not in (set, frozenset) or any(type(z) is not int for z in x):
        raise TypeError('positions must be a set or frozenset of exact integers')
    return frozenset(x)


def _boolean(x, name):
    if type(x) is not bool:
        raise TypeError(name + ' must be a Boolean')
    return x


@dataclass(frozen=True, slots=True)
class Pattern:
    name: str
    P: frozenset
    Q: frozenset
    isolation: int
    guard: object = None

    def __post_init__(self):
        object.__setattr__(self, 'P', _positions(self.P))
        object.__setattr__(self, 'Q', _positions(self.Q))

    @property
    def shapes(self):
        return self.P, self.Q


@dataclass(frozen=True, slots=True, init=False)
class ParallelBlock:
    """Internal lemma harness; arbitrary guards require the theorem contract.

    Only ParallelCompiler is a supported source-facing construction entry point.
    """
    patterns: tuple
    b: int
    r: int
    H: int
    radius: int

    def __init__(self, patterns, b, r):
        if type(b) is not int or type(r) is not int:
            raise TypeError('Radius parameters must be exact integers')
        object.__setattr__(self, 'patterns', tuple(patterns))
        object.__setattr__(self, 'b', b)
        object.__setattr__(self, 'r', r)
        object.__setattr__(self, 'H', 2 * (b + r))
        object.__setattr__(self, 'radius', 3 * (b + r))
        if not 0 <= b <= r:
            raise ValueError('Require 0 <= b <= r')
        for p in self.patterns:
            if len(p.P) != len(p.Q) or not p.P or p.P == p.Q:
                raise ValueError('Require distinct nonempty equal-mass endpoints')
            if any(abs(z) > b for z in p.P | p.Q):
                raise ValueError('Endpoint outside write radius')
            if not b <= p.isolation <= r:
                # Compiler pair templates have a smaller isolation than global b.
                if not max(map(abs, p.P | p.Q)) <= p.isolation <= r:
                    raise ValueError('Invalid exactness radius')

    def candidates(self, x, center=None, radius=None):
        """Return keyed orientations; optional anchor interval is LOCAL only.

        A pattern occurrence must have exactly its endpoint particles in the
        pattern's isolation window. Guard objects read only immutable local bits.
        """
        out = {}
        for j, p in enumerate(self.patterns):
            for label, shape in enumerate(p.shapes):
                first = min(shape)
                for z in x:
                    u = z - first
                    if center is not None and abs(u - center) > radius:
                        continue
                    if all(u + d in x for d in shape) and sum(
                            abs(v - u) <= p.isolation for v in x) == len(shape):
                        if p.guard is not None and not p.guard.allows(x, u):
                            continue
                        key = (j, u)
                        if key in out and out[key] != label:
                            raise RuntimeError('Ambiguous endpoint orientation')
                        out[key] = label
        return out

    def swap(self, x, key, label):
        j, u = key
        p = self.patterns[j]
        return frozenset((x - {u + d for d in p.shapes[label]}) |
                         {u + d for d in p.shapes[1 - label]})

    def eligible(self, x, candidates=None):
        raw = self.candidates(x) if candidates is None else candidates
        active = {}
        for key, label in raw.items():
            _, u = key
            if any(k != key and abs(k[1] - u) <= self.H for k in raw):
                continue
            y = self.swap(x, key, label)
            before = {k for k in raw if abs(k[1] - u) <= self.r + self.b}
            after = self.candidates(y, u, self.r + self.b)
            if before == set(after):
                if after.get(key) != 1 - label:
                    raise RuntimeError('Endpoint swap is not symmetric')
                active[key] = label
        return active

    def apply(self, x, verify=False):
        x = _positions(x)
        _boolean(verify, 'verify')
        raw = self.candidates(x)
        active = self.eligible(x, raw)
        y = set(x)
        for key, label in active.items():
            j, u = key
            p = self.patterns[j]
            y.difference_update(u + d for d in p.shapes[label])
            y.update(u + d for d in p.shapes[1 - label])
        y = frozenset(y)
        if verify:
            if len(y) != len(x):
                raise RuntimeError('Mass not conserved')
            raw_y = self.candidates(y)
            if set(raw_y) != set(raw):
                raise RuntimeError('Candidate-key set changed')
            active_y = self.eligible(y, raw_y)
            if set(active_y) != set(active):
                raise RuntimeError('Selected key set changed')
            if any(active_y[k] != 1 - active[k] for k in active):
                raise RuntimeError('Selected orientation did not reverse')
            if self.apply(y) != x:
                raise RuntimeError('Block not involutive')
        return y

    def local_output(self, x, i=0):
        """A literal finite-neighborhood implementation; no global support needed.

        All candidates whose predicates are queried fit within the certified
        radius around i. Missing bits outside that radius are never consulted.
        """
        x = _positions(x)
        if type(i) is not int:
            raise TypeError('Output coordinate must be an exact integer')
        x = frozenset(z for z in x if abs(z-i) <= self.radius)
        writing = self.candidates(x, i, self.b)
        result = i in x
        for key, label in writing.items():
            _, u = key
            nearby = self.candidates(x, u, self.H)
            if any(k != key for k in nearby):
                continue
            y = self.swap(x, key, label)
            before = self.candidates(x, u, self.r+self.b)
            after = self.candidates(y, u, self.r+self.b)
            if set(before) != set(after):
                continue
            p = self.patterns[key[0]]
            if i-u in p.shapes[label]:
                result = False
            if i-u in p.shapes[1-label]:
                result = True
        return int(result)


@dataclass(frozen=True, slots=True, init=False)
class ParallelCompiler:
    """Immutable new CA compiled from the frozen source JSON interface.

    step accepts only sets/frozensets of exact Python integers and Boolean flags.
    Custom predicate objects are not accepted through this entry point.
    """
    old: object
    E: ParallelBlock
    P: ParallelBlock
    radius: int

    def __init__(self, source):
        c = compile_source(source)
        object.__setattr__(self, 'old', c)
        def patterns(gates):
            return tuple(Pattern(g.name, g.P, g.Q, g.L, g.guard) for g in gates)
        object.__setattr__(self, 'E', ParallelBlock(patterns(c.E), c.B3, c.Z+c.J))
        object.__setattr__(self, 'P', ParallelBlock(patterns(c.P), c.B3, 3*c.B3+1))
        object.__setattr__(self, 'radius', self.E.radius + self.P.radius)
        if self.radius != 180*c.D+258+9*c.J:
            raise RuntimeError('Resource arithmetic disagrees')

    def step(self, x, inverse=False, verify=False):
        x = _positions(x)
        _boolean(inverse, 'inverse')
        _boolean(verify, 'verify')
        first, second = (self.P, self.E) if inverse else (self.E, self.P)
        return second.apply(first.apply(x, verify), verify)

    def ledger(self):
        c = self.old
        return dict(c.ledger(), old_radius=c.radius, radius=self.radius,
                    edge_radius=self.E.radius, phase_radius=self.P.radius,
                    edge_read_radius=self.E.r, phase_read_radius=self.P.r,
                    edge_exclusion=self.E.H, phase_exclusion=self.P.H,
                    new_rule_off_admissible=True)
