"""Sparse exact evaluation of the frozen ordered reversible binary compiler.

No local-factor array is constructed. Arbitrary finite binary supports are
accepted, including malformed ones. See PROOF.md for ordering/completeness.
"""
from bisect import bisect_left, bisect_right
from dataclasses import dataclass, field
from hashlib import sha256
from pathlib import Path
from types import MappingProxyType, ModuleType
import sys

FROZEN_SHA256 = 'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f'
_reference_path = Path(__file__).resolve().with_name('frozen_reversible_binary.py')
_reference_bytes = _reference_path.read_bytes()
if sha256(_reference_bytes).hexdigest() != FROZEN_SHA256:
    raise RuntimeError('Frozen compiler dependency has changed')
# Execute the exact verified bytes, not an import resolved through sys.path.
ref = ModuleType('_lazy_pinned_reversible_reference')
ref.__file__ = str(_reference_path)
sys.modules[ref.__name__] = ref
exec(compile(_reference_bytes, str(_reference_path), 'exec'), ref.__dict__)
del _reference_bytes


@dataclass(frozen=True, slots=True, init=False)
class LazySource:
    controls: tuple
    branches: tuple = field(repr=False)
    moving: tuple = field(repr=False)
    direct: tuple = field(repr=False)
    control_index: object = field(repr=False)
    home_out: object = field(repr=False)
    home_in: object = field(repr=False)
    J: int
    p: int
    a: int
    m: int
    D: int
    S: int
    B2: int
    L: int
    B3: int
    Z: int
    E_count: int
    P_count: int
    factors: int
    radius: int
    start: str
    halt: str
    source_data: object = field(repr=False)

    def __init__(self, *args, **kwargs):
        raise TypeError('Use compile_lazy_source')

    def _gap(self, kind, i, sign):
        if kind == 'H':
            return 2*i + 1 + (sign == '-')
        return 2*self.m + 4*i + (1 if kind == 'O' else 3) + (sign == '-')

    def encode(self, q, c0, c1, sign='+'):
        ref._string(q, 'control')
        if q not in self.control_index:
            raise ValueError('Unknown control')
        ref._integer(c0, 'counter 0', 0)
        ref._integer(c1, 'counter 1', 0)
        ref._string(sign, 'sign')
        if sign not in ('+', '-'):
            raise ValueError("sign must be '+' or '-'")
        return frozenset((-self.Z-c0, 0, self.Z+c1, self.S,
                          self.S+self._gap('H', self.control_index[q], sign)))

    def ledger(self):
        return dict(m=self.m, p=self.p, a=self.a, J=self.J, D=self.D,
                    S=self.S, B2=self.B2, L=self.L, B3=self.B3, Z=self.Z,
                    E=self.E_count, P=self.P_count, factors=self.factors,
                    radius=self.radius, observer_length=3*self.D+3,
                    particles=5, alphabet=[0, 1])

    def gate_at(self, index):
        """Materialize just one original gate, at its zero-based E+P index."""
        ref._integer(index, 'factor index', 0)
        if index >= self.factors:
            raise ValueError('factor index is out of range')
        r = self.D+3                 # inclusive S..L
        es = 4*self.D+15
        em = 2*self.D+6
        pm = 2*self.D+7
        def pair(kind, i, sign, anchor=0):
            return {anchor, anchor+self._gap(kind, i, sign)}
        def triple(kind, i, sign, anchor):
            return {0} | pair(kind, i, sign, anchor)
        def make(name, left, right, B, branch=None, inverse=False):
            guard = None if branch is None else ref._record(
                ref._ClassGuard, J=self.J, Z=self.Z,
                table=branch.image_table if inverse else branch.domain_table)
            return ref._make_gate(name, left, right, B, guard,
                                  self.Z+self.J if guard is not None else 0)
        if index < self.E_count:
            if index >= self.p*es:
                e = self.direct[index-self.p*es]
                qi, qj = self.control_index[e.source], self.control_index[e.target]
                return make(f'direct:{e.name}', triple('H', qi, '+', self.S),
                            triple('H', qj, '-', self.S), self.B3, e)
            i, local = divmod(index, es)
            e = self.moving[i]
            if local < 2*em:
                kind_no, local = divmod(local, em)
                kind = ('O', 'I')[kind_no]
                mode = (kind, e.name)
                w = e.side if kind == 'O' else -e.side
                if local == 0:
                    return make(f'free:{mode}', pair(kind, i, '+'),
                                pair(kind, i, '-', w), self.B2)
                if local <= r:
                    t = self.S+local-1
                    return make(f'behind:{mode}:{t}', triple(kind, i, '+', w*t),
                                triple(kind, i, '-', w*(t+1)), self.B3)
                t = self.S+1+(local-1-r)
                return make(f'ahead:{mode}:{t}', triple(kind, i, '+', -w*t),
                            triple(kind, i, '-', -w*(t-1)), self.B3)
            interaction = local-2*em
            v = e.side
            if interaction == 0:
                qi = self.control_index[e.source]
                return make(f'dispatch:{e.name}', triple('H', qi, '+', self.S),
                            triple('O', i, '-', v*self.S), self.B3, e)
            if interaction == 1:
                return make(f'endpoint:{e.name}', triple('O', i, '+', -v*self.S),
                            {v*e.delta} | pair('I', i, '-', v*e.delta-v*self.S), self.B3)
            qj = self.control_index[e.target]
            return make(f'commit:{e.name}', triple('I', i, '+', v*self.S),
                        triple('H', qj, '-', self.S), self.B3, e, True)
        index -= self.E_count
        if index >= self.p*2*pm:
            qi = index-self.p*2*pm
            q = self.controls[qi]
            return make(f'phase-home:{q}', triple('H', qi, '+', self.S),
                        triple('H', qi, '-', self.S), self.B3)
        mode_no, local = divmod(index, pm)
        i, kind_no = divmod(mode_no, 2)
        kind = ('O', 'I')[kind_no]
        mode = (kind, self.moving[i].name)
        if local == 0:
            return make(f'phase-free:{mode}', pair(kind, i, '+'),
                        pair(kind, i, '-'), self.B2)
        side_no, offset = divmod(local-1, r)
        side = (-1, 1)[side_no]
        t = self.S+offset
        return make(f'phase-near:{mode}:{side}:{t}', triple(kind, i, '+', side*t),
                    triple(kind, i, '-', side*t), self.B3)

    def _candidate_indices(self, x):
        """Superset of factors with a raw occurrence, without enumerating t."""
        ordered = sorted(x)
        candidates = set()
        es, em, pm, r = 4*self.D+15, 2*self.D+6, 2*self.D+7, self.D+3
        for left_i, h in enumerate(ordered):
            for other_i in range(left_i+1, len(ordered)):
                d = ordered[other_i]-h
                if d > self.D:
                    break
                positive = bool(d & 1)
                if d <= 2*self.m:
                    qi = (d-1)//2
                    if h-self.S in x:
                        candidates.add(self.E_count+2*self.p*pm+qi)
                        candidates.update((self.home_out if positive else self.home_in).get(qi, ()))
                    continue
                mode_no, offset = divmod(d-2*self.m-1, 4)
                kind_no = offset//2
                e = self.moving[mode_no]
                w = e.side if kind_no == 0 else -e.side
                eb = mode_no*es+kind_no*em
                pb = self.E_count+(2*mode_no+kind_no)*pm
                candidates.add(eb)
                candidates.add(pb)
                for z in ordered:
                    if z == h or z == h+d:
                        continue
                    distance = h-z
                    t = w*distance-(0 if positive else 1)
                    if self.S <= t <= self.L:
                        candidates.add(eb+1+t-self.S)
                    t = -w*distance+(0 if positive else 1)
                    if self.S+1 <= t <= self.L:
                        candidates.add(eb+1+r+t-(self.S+1))
                    t = abs(distance)
                    if self.S <= t <= self.L:
                        side_no = 0 if distance < 0 else 1
                        candidates.add(pb+1+side_no*r+t-self.S)
                    interactions = mode_no*es+2*em
                    if kind_no == 0:
                        if positive and distance == -e.side*self.S:
                            candidates.add(interactions+1)
                        if not positive and distance == e.side*self.S:
                            candidates.add(interactions)
                    else:
                        if positive and distance == e.side*self.S:
                            candidates.add(interactions+2)
                        if not positive and distance == -e.side*self.S:
                            candidates.add(interactions+1)
        return candidates

    def candidate_indices(self, positions):
        return tuple(sorted(self._candidate_indices(ref._positions(positions))))

    def step(self, positions, inverse=False, verify=False, trace=False):
        """Exact ordered composition. trace=True returns (support, immutable stats).

        Candidates are refreshed after *every* changing factor. Factors already
        passed in the requested order are never revisited. A factor computes all
        eligible keys from the same pre-factor support and rewrites simultaneously.
        """
        x = ref._positions(positions)
        ref._boolean(inverse, 'inverse')
        ref._boolean(verify, 'verify')
        ref._boolean(trace, 'trace')
        cursor = self.factors if inverse else -1
        tested, changed, generations, events = 0, 0, 0, []
        while True:
            generations += 1
            indices = self._candidate_indices(x)
            pending = sorted((i for i in indices if i < cursor), reverse=True) if inverse else sorted(i for i in indices if i > cursor)
            for i in pending:
                gate = self.gate_at(i)
                y, anchors = apply_gate(gate, x, verify)
                tested += 1
                cursor = i
                if y != x:
                    changed += 1
                    if trace:
                        events.append((i, gate.name, anchors))
                    x = y
                    break
            else:
                stats = MappingProxyType(dict(tested_factors=tested, changed_factors=changed,
                                               candidate_generations=generations, events=tuple(events)))
                return (x, stats) if trace else x


def _raw_sparse(gate, x, ordered):
    raw = {}
    for label, shape in enumerate(gate.shapes):
        for first in ordered:
            u = first-shape[0]
            if (all(u+p in x for p in shape)
                    and bisect_right(ordered, u+gate.B)-bisect_left(ordered, u-gate.B) == len(shape)):
                if u in raw and raw[u] != label:
                    raise RuntimeError('Ambiguous raw occurrence')
                raw[u] = label
    return raw


def _guard_sparse(guard, ordered, u):
    classes = []
    for side in (-1, 1):
        low, high = (u-guard.Z-guard.J, u-guard.Z) if side == -1 else (u+guard.Z, u+guard.Z+guard.J)
        left, right = bisect_left(ordered, low), bisect_right(ordered, high)
        if right-left > 1:
            return False
        classes.append(guard.J+1 if left == right else side*(ordered[left]-u)-guard.Z)
    return guard.table[classes[0]][classes[1]]


def apply_gate(gate, positions, verify=False):
    """Sparse implementation of exactly ref.Gate.apply; also returns active keys."""
    if type(gate) is not ref.Gate:
        raise TypeError('gate must be an exact frozen Gate')
    x = ref._positions(positions)
    ref._boolean(verify, 'verify')
    ordered = sorted(x)
    raw = _raw_sparse(gate, x, ordered)
    keys = sorted(raw)
    active = []
    for i, u in enumerate(keys):
        label = raw[u]
        if bisect_right(ordered, u+gate.L)-bisect_left(ordered, u-gate.L) != len(gate.shapes[label]):
            continue
        if (i and u-keys[i-1] <= gate.M) or (i+1 < len(keys) and keys[i+1]-u <= gate.M):
            continue
        if gate.guard is not None and not _guard_sparse(gate.guard, ordered, u):
            continue
        active.append((u, label))
    if not active:
        return x, ()
    y = set(x)
    for u, label in active:
        y.difference_update(u+p for p in gate.shapes[label])
        y.update(u+p for p in gate.shapes[1-label])
    y = frozenset(y)
    if verify:
        if len(y) != len(x):
            raise RuntimeError('Particle conservation failed')
        if set(_raw_sparse(gate, y, sorted(y))) != set(raw):
            raise RuntimeError('Raw occurrence key invariance failed')
        if apply_gate(gate, y, False)[0] != x:
            raise RuntimeError('Gate involution check failed')
    return y, tuple(u for u, _ in active)


def compile_lazy_source(data):
    """Validate the original schema without allocating any local factor.

    Validation duplicates the frozen compiler's semantic checks, using indexed
    control incidence rather than its quadratic all-branches scan per control.
    Primitive schema, guard parsing, and class evaluation are pinned reuse.
    """
    ref._object(data, ('schema', 'controls', 'start', 'halt', 'class_cut', 'branches'), 'source')
    if ref._string(data['schema'], 'schema') != 'reversible-two-counter-v1':
        raise ValueError('Unknown source schema')
    controls = tuple(ref._string(q, 'control') for q in ref._array(data['controls'], 'controls'))
    control_index = {q: i for i, q in enumerate(controls)}
    if len(control_index) != len(controls):
        raise ValueError('Control names must be unique')
    J = ref._integer(data['class_cut'], 'class_cut', 0)
    start, halt = ref._string(data['start'], 'start'), ref._string(data['halt'], 'halt')
    if start not in control_index or halt not in control_index:
        raise ValueError('start and halt must name declared controls')
    rows = ref._array(data['branches'], 'branches')
    names, branches, frozen_rows = set(), [], []
    outgoing_masks, incoming_masks = {}, {}
    domain_conflicts, image_conflicts = {}, {}
    for i, row in enumerate(rows):
        path = f'branches[{i}]'
        ref._object(row, ('name', 'source', 'target', 'side', 'delta', 'guard'), path)
        name = ref._string(row['name'], f'{path}.name')
        if name in names:
            raise ValueError('Branch names must be unique')
        names.add(name)
        source, target = (ref._string(row[k], f'{path}.{k}') for k in ('source', 'target'))
        if source not in control_index or target not in control_index:
            raise ValueError('Branch source and target must name declared controls')
        if source == halt:
            raise ValueError('The designated halt control must have no exits')
        side, delta = (ref._integer(row[k], f'{path}.{k}') for k in ('side', 'delta'))
        if side not in (-1, 1) or delta not in (-1, 0, 1):
            raise ValueError('side must be -1 or 1; delta must be -1, 0, or 1')
        idx = 0 if side == -1 else 1
        frozen_guard, program, atoms = ref._parse_guard(row['guard'], f'{path}.guard')
        for counter, k in atoms:
            if k > J or k+(delta if counter == idx else 0) > J:
                raise ValueError('class_cut is insufficient for a guard or image threshold')
        domain, image, dm, im = [], [], 0, 0
        for c0 in range(J+2):
            dr, ir = [], []
            for c1 in range(J+2):
                c = (c0, c1)
                enabled = ref._evaluate(program, c)
                if enabled and c[idx]+delta < 0:
                    raise ValueError('Guard permits a negative post-counter')
                old = list(c)
                old[idx] -= delta
                image_enabled = min(old) >= 0 and ref._evaluate(program, old)
                dr.append(enabled)
                ir.append(image_enabled)
                bit = 1 << (c0*(J+2)+c1)
                if enabled:
                    dm |= bit
                if image_enabled:
                    im |= bit
            domain.append(tuple(dr))
            image.append(tuple(ir))
        domain_conflicts[source] = domain_conflicts.get(source, 0) | (outgoing_masks.get(source, 0) & dm)
        image_conflicts[target] = image_conflicts.get(target, 0) | (incoming_masks.get(target, 0) & im)
        outgoing_masks[source] = outgoing_masks.get(source, 0) | dm
        incoming_masks[target] = incoming_masks.get(target, 0) | im
        branches.append(ref._record(ref.Branch, name=name, source=source, target=target,
                                    side=side, delta=delta, J=J,
                                    domain_table=tuple(domain), image_table=tuple(image)))
        frozen_rows.append(MappingProxyType(dict(name=name, source=source, target=target,
                                                side=side, delta=delta, guard=frozen_guard)))
    # Parse/type-check every row before semantic overlap rejection, as frozen.
    for q in controls:
        dm, im = domain_conflicts.get(q, 0), image_conflicts.get(q, 0)
        conflict = dm | im
        if conflict:
            bit = conflict & -conflict
            cls = divmod(bit.bit_length()-1, J+2)
            which = 'domains' if dm & bit else 'images'
            raise ValueError(f'Overlapping branch {which} at {q!r}, class {cls}')
    branches = tuple(branches)
    moving, direct = tuple(e for e in branches if e.delta), tuple(e for e in branches if not e.delta)
    m, p, a = len(controls), len(moving), len(direct)
    D = 2*m+4*p
    S, B2, L, B3 = 2*D+2, D+1, 3*D+4, 4*D+5
    Z = 10*B3+10+2*J
    es, em = 4*D+15, 2*D+6
    E_count, P_count = p*es+a, p*(4*D+14)+m
    home_out, home_in = {}, {}
    for i, e in enumerate(moving):
        home_out.setdefault(control_index[e.source], []).append(i*es+2*em)
        home_in.setdefault(control_index[e.target], []).append(i*es+2*em+2)
    for i, e in enumerate(direct):
        home_out.setdefault(control_index[e.source], []).append(p*es+i)
        home_in.setdefault(control_index[e.target], []).append(p*es+i)
    radius = (4*p*(6*D+8)+(8*p*D+23*p+m)*(24*D+32)
              +(2*p+a)*(Z+J+12*D+16))
    snapshot = MappingProxyType(dict(schema='reversible-two-counter-v1', controls=controls,
                                    start=start, halt=halt, class_cut=J, branches=tuple(frozen_rows)))
    return ref._record(LazySource, controls=controls, branches=branches, moving=moving, direct=direct,
                       control_index=MappingProxyType(control_index),
                       home_out=MappingProxyType({q: tuple(v) for q, v in home_out.items()}),
                       home_in=MappingProxyType({q: tuple(v) for q, v in home_in.items()}),
                       J=J, p=p, a=a, m=m, D=D, S=S, B2=B2, L=L, B3=B3, Z=Z,
                       E_count=E_count, P_count=P_count, factors=E_count+P_count,
                       radius=radius, start=start, halt=halt, source_data=snapshot)
