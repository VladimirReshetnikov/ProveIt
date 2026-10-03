"""Source-sized exact finite-support evaluator of the NEW parallel CA.

This is not the ordered evaluator. Its pinned dependency supplies source
validation, immutable metadata, arithmetic template lookup, candidate-index
discovery, and sparse class guards only. No ordered step/apply is called.
"""
from bisect import bisect_left, bisect_right
from dataclasses import dataclass, field
from hashlib import sha256
from pathlib import Path
from types import MappingProxyType, ModuleType
import sys

__all__ = ['SparseParallelCompiler', 'BlockTrace', 'StepTrace']
METADATA_SHA256 = '42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61'
_path = Path(__file__).resolve().with_name('frozen_lazy_source.py')
_bytes = _path.read_bytes()
if sha256(_bytes).hexdigest() != METADATA_SHA256:
    raise RuntimeError('Frozen source metadata dependency has changed')
_metadata = ModuleType('_parallel_pinned_source_metadata')
_metadata.__file__ = str(_path)
sys.modules[_metadata.__name__] = _metadata
exec(compile(_bytes, str(_path), 'exec'), _metadata.__dict__)
del _bytes
_ref = _metadata.ref


@dataclass(frozen=True, slots=True)
class BlockTrace:
    block: str
    input_particles: int
    candidate_types: int
    raw_keys: int
    isolated_keys: int
    prospective_queries: int
    prospective_candidate_types: int
    selected: tuple


@dataclass(frozen=True, slots=True)
class StepTrace:
    inverse: bool
    blocks: tuple


def _interval(center, radius):
    if center is None and radius is None:
        return
    if center is None or radius is None:
        raise ValueError('center and radius must be supplied together')
    _ref._integer(center, 'center')
    _ref._integer(radius, 'radius', 0)


def _swap(x, gate, anchor, label):
    return frozenset((x - {anchor+d for d in gate.shapes[label]}) |
                     {anchor+d for d in gate.shapes[1-label]})


@dataclass(frozen=True, slots=True, init=False)
class _SparseBlock:
    metadata: object = field(repr=False)
    name: str
    lower: int
    upper: int
    b: int
    r: int
    H: int
    radius: int

    def __init__(self, *args, **kwargs):
        raise TypeError('Blocks are obtained from SparseParallelCompiler')

    def _raw(self, x, center=None, radius=None):
        """All raw keys, including keys that will fail later selection.

        Global template IDs are stable across E and P. Restricting the anchor
        interval is only an output filter: discovery still uses the whole x.
        """
        ordered = sorted(x)
        indices = sorted(i for i in self.metadata._candidate_indices(x)
                         if self.lower <= i < self.upper)
        raw = {}
        for i in indices:
            gate = self.metadata.gate_at(i)
            for label, shape in enumerate(gate.shapes):
                for first in ordered:
                    u = first-shape[0]
                    if center is not None and abs(u-center) > radius:
                        continue
                    if not all(u+d in x for d in shape):
                        continue
                    # New-rule raw exactness is L, not old-rule raw radius B.
                    if (bisect_right(ordered, u+gate.L) -
                            bisect_left(ordered, u-gate.L)) != len(shape):
                        continue
                    if gate.guard is not None and not _metadata._guard_sparse(
                            gate.guard, ordered, u):
                        continue
                    key = (i, u)
                    if key in raw and raw[key] != label:
                        raise RuntimeError('Ambiguous endpoint orientation')
                    raw[key] = label
        return raw, len(indices)

    def candidates(self, positions, center=None, radius=None):
        x = _ref._positions(positions)
        _interval(center, radius)
        return MappingProxyType(self._raw(x, center, radius)[0])

    def _select(self, x, raw):
        # A nearest-neighbor test suffices, including distinct types at one u.
        keys = sorted(raw, key=lambda k: (k[1], k[0]))
        active = {}
        isolated = queries = prospective_types = 0
        for j, key in enumerate(keys):
            i, u = key
            if ((j and u-keys[j-1][1] <= self.H) or
                    (j+1 < len(keys) and keys[j+1][1]-u <= self.H)):
                continue
            isolated += 1
            gate = self.metadata.gate_at(i)
            label = raw[key]
            y = _swap(x, gate, u, label)
            before = {k for k in raw if abs(k[1]-u) <= self.b+self.r}
            after, types = self._raw(y, u, self.b+self.r)
            queries += 1
            prospective_types += types
            if before == set(after):
                if after.get(key) != 1-label:
                    raise RuntimeError('Endpoint swap is not symmetric')
                active[key] = label
        return active, isolated, queries, prospective_types

    def eligible(self, positions):
        x = _ref._positions(positions)
        raw, _ = self._raw(x)
        return MappingProxyType(self._select(x, raw)[0])

    def _write(self, x, active):
        # Every decision was made on the same immutable input support.
        y = set(x)
        for (i, u), label in active.items():
            gate = self.metadata.gate_at(i)
            y.difference_update(u+d for d in gate.shapes[label])
            y.update(u+d for d in gate.shapes[1-label])
        return frozenset(y)

    def apply(self, positions, verify=False, trace=False):
        x = _ref._positions(positions)
        _ref._boolean(verify, 'verify')
        _ref._boolean(trace, 'trace')
        raw, types = self._raw(x)
        active, isolated, queries, prospective_types = self._select(x, raw)
        y = self._write(x, active)
        if verify:
            if len(y) != len(x):
                raise RuntimeError('Mass not conserved')
            raw_y, _ = self._raw(y)
            if set(raw_y) != set(raw):
                raise RuntimeError('Candidate-key set changed')
            active_y = self._select(y, raw_y)[0]
            if set(active_y) != set(active):
                raise RuntimeError('Selected key set changed')
            if any(active_y[k] != 1-active[k] for k in active):
                raise RuntimeError('Selected orientation did not reverse')
            if self._write(y, active_y) != x:
                raise RuntimeError('Block not involutive')
        if trace:
            stats = BlockTrace(self.name, len(x), types, len(raw), isolated,
                               queries, prospective_types,
                               tuple((i,u,label) for (i,u),label in active.items()))
            return y, stats
        return y

    def local_output(self, positions, i=0):
        """The same certified finite-radius oracle as the eager new rule."""
        x = _ref._positions(positions)
        _ref._integer(i, 'output coordinate')
        x = frozenset(z for z in x if abs(z-i) <= self.radius)
        writing = self._raw(x, i, self.b)[0]
        result = i in x
        for key, label in writing.items():
            index, u = key
            nearby = self._raw(x, u, self.H)[0]
            if any(k != key for k in nearby):
                continue
            gate = self.metadata.gate_at(index)
            y = _swap(x, gate, u, label)
            before = self._raw(x, u, self.r+self.b)[0]
            after = self._raw(y, u, self.r+self.b)[0]
            if set(before) != set(after):
                continue
            if i-u in gate.shapes[label]:
                result = False
            if i-u in gate.shapes[1-label]:
                result = True
        return int(result)


@dataclass(frozen=True, slots=True, init=False)
class SparseParallelCompiler:
    """Immutable two-involution CA for every finite particle configuration.

    Supports must be sets/frozensets of exact Python ints; flags exact bools.
    Source validation retains explicit finite class descriptors of size
    O((p+a)(J+2)^2), but never constructs all F endpoint templates.
    """
    metadata: object = field(repr=False)
    E: _SparseBlock
    P: _SparseBlock
    radius: int

    def __init__(self, source):
        c = _metadata.compile_lazy_source(source)
        object.__setattr__(self, 'metadata', c)
        def block(name, lower, upper, r):
            return _ref._record(_SparseBlock, metadata=c, name=name,
                                lower=lower, upper=upper, b=c.B3, r=r,
                                H=2*(c.B3+r), radius=3*(c.B3+r))
        object.__setattr__(self, 'E', block('E', 0, c.E_count, c.Z+c.J))
        object.__setattr__(self, 'P', block('P', c.E_count, c.factors, 3*c.B3+1))
        object.__setattr__(self, 'radius', self.E.radius+self.P.radius)
        if self.radius != 180*c.D+258+9*c.J:
            raise RuntimeError('Resource arithmetic disagrees')

    def encode(self, q, c0, c1, sign='+'):
        return self.metadata.encode(q, c0, c1, sign)

    def gate_at(self, index):
        """One endpoint template by global E+P ID, never an ordered step."""
        return self.metadata.gate_at(index)

    def step(self, positions, inverse=False, verify=False, trace=False):
        x = _ref._positions(positions)
        _ref._boolean(inverse, 'inverse')
        _ref._boolean(verify, 'verify')
        _ref._boolean(trace, 'trace')
        first, second = (self.P, self.E) if inverse else (self.E, self.P)
        if trace:
            y, t1 = first.apply(x, verify, True)
            z, t2 = second.apply(y, verify, True)
            return z, StepTrace(inverse, (t1, t2))
        return second.apply(first.apply(x, verify), verify)

    def ledger(self):
        c = self.metadata
        return dict(c.ledger(), old_radius=c.radius, radius=self.radius,
                    edge_radius=self.E.radius, phase_radius=self.P.radius,
                    edge_read_radius=self.E.r, phase_read_radius=self.P.r,
                    edge_exclusion=self.E.H, phase_exclusion=self.P.H,
                    new_rule_off_admissible=True)
