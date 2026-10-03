"""Independent bounded differential/API regression for sparse parallel blocks.

The oracle is the byte-pinned eager parallel interpreter, not the ordered
compiler. Every check raises explicitly and therefore survives python -O.
Only the Python standard library is used. Run next to the pinned dependencies.
"""
import argparse
import copy
import dataclasses
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys
import time
from types import MappingProxyType
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent
PINS = {
    'parallel_particles.py': '2c8b639646a587a51bddeaac16e46d2dbd8c4e8138ac67a2601025334d4a64cd',
    'frozen_reversible_binary.py': 'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f',
}
COUNTS = {}
RNG = random.Random(202610031221)


def count(key, amount=1):
    COUNTS[key] = COUNTS.get(key, 0) + amount


def check(value, detail):
    if not value:
        raise RuntimeError(detail)


def rejects(action, expected=TypeError, detail='invalid input accepted'):
    try:
        action()
    except expected:
        count('rejections')
        return
    raise RuntimeError(detail)


def branch(name, source, target, side=1, delta=0, guard=None):
    return dict(name=name, source=source, target=target, side=side, delta=delta,
                guard={'op': 'true'} if guard is None else guard)


def source(controls=None, branches=None, J=0):
    controls = ['q', 'h'] if controls is None else controls
    branches = [branch('e', 'q', 'h', 1, 1)] if branches is None else branches
    return dict(schema='reversible-two-counter-v1', controls=controls,
                start=controls[0], halt=controls[-1], class_cut=J, branches=branches)


def sources():
    yield 'empty_branch_list', source(['h'], [])
    for side in (-1, 1):
        idx = (side+1)//2
        yield 'increment_' + str(side), source(branches=[branch('inc', 'q', 'h', side, 1)])
        yield 'decrement_' + str(side), source(branches=[branch(
            'dec', 'q', 'h', side, -1, {'op': 'gt', 'counter': idx, 'value': 0})], J=1)
    yield 'zero_direct', source(branches=[branch('zero', 'q', 'h', -1, 0)])
    yield 'partitioned_direct', source(branches=[
        branch('zero', 'q', 'h', guard={'op': 'eq', 'counter': 0, 'value': 0}),
        branch('pos', 'q', 'h', guard={'op': 'gt', 'counter': 0, 'value': 0})], J=2)
    yield 'self_loop_and_empty_guard', source(['q', 'r', 'h'], [
        branch('never', 'q', 'h', 1, 1, {'op': 'or', 'args': []}),
        branch('loop', 'q', 'q', guard={'op': 'eq', 'counter': 1, 'value': 0}),
        branch('end', 'q', 'h', guard={'op': 'gt', 'counter': 1, 'value': 0})], J=1)
    yield 'guarded_partition', source(['q', 'a', 'b', 'h'], [
        branch('left', 'q', 'a', -1, 1, {'op': 'eq', 'counter': 0, 'value': 0}),
        branch('right', 'q', 'b', 1, -1, {'op': 'and', 'args': [
            {'op': 'gt', 'counter': 0, 'value': 0}, {'op': 'gt', 'counter': 1, 'value': 0}]}),
        branch('finish', 'a', 'h', -1, 0)], J=2)
    yield 'mixed_chain', source(['q', 'r', 's', 'h'], [
        branch('left', 'q', 'r', -1, 1),
        branch('right', 'r', 's', 1, 1),
        branch('direct', 's', 'h', 1, 0, {'op': 'not', 'arg': {'op': 'eq', 'counter': 0, 'value': 1}})], J=2)


def translate(x, shift):
    return frozenset(v+shift for v in x)


def globalize(raw, offset):
    return {(j+offset, u): label for (j, u), label in raw.items()}


def immutable_map(raw):
    check(isinstance(raw, MappingProxyType), ('mapping is not an immutable snapshot', type(raw)))
    rejects(lambda: raw.__setitem__((-1, 0), 0), (AttributeError, TypeError))


def immutable_trace(trace):
    check(dataclasses.is_dataclass(trace), ('trace must be a dataclass', type(trace)))
    check(trace.__dataclass_params__.frozen, 'trace dataclass is not frozen')
    fields = dataclasses.fields(trace)
    check(bool(fields), 'empty trace does not expose instrumentation')
    rejects(lambda: setattr(trace, fields[0].name, None), dataclasses.FrozenInstanceError)
    def frozen(value):
        if dataclasses.is_dataclass(value):
            check(value.__dataclass_params__.frozen, 'mutable nested trace dataclass')
            for field in dataclasses.fields(value):
                frozen(getattr(value, field.name))
        elif isinstance(value, MappingProxyType):
            for key, item in value.items():
                frozen(key); frozen(item)
        elif type(value) in (tuple, frozenset):
            for item in value:
                frozen(item)
        else:
            check(type(value) not in (dict, list, set, bytearray), ('mutable trace field', type(value)))
    frozen(trace)


def compare(a, b, x, context, verify=False, local=False, trace=False):
    x = frozenset(x)
    for name, offset in (('E', 0), ('P', a.metadata.E_count)):
        sparse, eager = getattr(a, name), getattr(b, name)
        raw = eager.candidates(x)
        active = eager.eligible(x, raw)
        got_raw = sparse.candidates(x)
        got_active = sparse.eligible(x)
        check(dict(got_raw) == globalize(raw, offset), ('candidate mismatch', context, name, sorted(x), dict(got_raw), globalize(raw, offset)))
        check(dict(got_active) == globalize(active, offset), ('active mismatch', context, name, sorted(x), dict(got_active), globalize(active, offset)))
        count('candidate_map_equalities'); count('active_map_equalities')
        y = sparse.apply(x, verify=verify)
        z = eager.apply(x)
        check(type(y) is frozenset and y == z, ('block output mismatch', context, name, sorted(x), sorted(y), sorted(z)))
        check(sparse.apply(y, verify=verify) == x, ('block not involutive', context, name))
        check(len(y) == len(x), ('block mass mismatch', context, name))
        count('block_output_equalities'); count('block_involution_checks')
        if trace:
            ty, stats = sparse.apply(x, verify=verify, trace=True)
            check(ty == y, ('trace changes block result', context, name))
            immutable_trace(stats)
            check(stats.block == name and stats.input_particles == len(x), ('trace block context', context, name))
            check(stats.raw_keys == len(raw), ('trace raw-key count', context, name))
            check({(j, u): label for j, u, label in stats.selected} == globalize(active, offset), ('trace selected keys', context, name))
            check(0 <= stats.prospective_queries == stats.isolated_keys <= len(raw), ('trace query counts', context, name))
            check(0 <= stats.candidate_types <= a.metadata.factors, ('trace candidate type count', context, name))
            count('trace_checks')
        if local:
            points = set(sorted(x | y)[:8]) | {0, -sparse.radius, sparse.radius}
            for i in points:
                check(sparse.local_output(x, i) == int(i in y), ('local result mismatch', context, name, i))
                truncated = frozenset(v for v in x if abs(v-i) <= sparse.radius)
                check(sparse.local_output(truncated, i) == int(i in y), ('certified-radius truncation mismatch', context, name, i))
                # The reference explicitly implements the finite-neighborhood oracle.
                check(sparse.local_output(x, i) == eager.local_output(x, i), ('local oracle mismatch', context, name, i))
                count('local_radius_checks')
    for inverse in (False, True):
        y = a.step(x, inverse=inverse, verify=verify)
        z = b.step(x, inverse=inverse)
        check(type(y) is frozenset and y == z, ('whole output mismatch', context, inverse, sorted(x), sorted(y), sorted(z)))
        check(a.step(y, inverse=not inverse, verify=verify) == x, ('whole inverse mismatch', context, inverse))
        check(len(y) == len(x), ('whole mass mismatch', context, inverse))
        count('whole_step_equalities'); count('whole_inverse_checks')
        if trace:
            ty, stats = a.step(x, inverse=inverse, verify=verify, trace=True)
            check(ty == y, ('trace changes whole result', context, inverse))
            immutable_trace(stats)
            check(stats.inverse is inverse, ('trace direction', context, inverse))
            check(tuple(t.block for t in stats.blocks) == (('P', 'E') if inverse else ('E', 'P')), ('trace block order', context, inverse))
            count('trace_checks')
    count('configurations')


def enabled_detectors(g):
    if g.guard is None:
        return frozenset()
    guard = g.guard
    for c0, row in enumerate(guard.table):
        for c1, enabled in enumerate(row):
            if enabled:
                return frozenset(side*(guard.Z+k) for side, k in ((-1, c0), (1, c1)) if k <= guard.J)
    return None


def factor_equal(g, h):
    for field in ('name', 'P', 'Q', 'B', 'L', 'M', 'radius', 'shapes'):
        check(getattr(g, field) == getattr(h, field), ('single factor mismatch', g.name, field))
    check((g.guard is None) == (h.guard is None), ('guard presence mismatch', g.name))
    if g.guard is not None:
        for field in ('J', 'Z', 'table'):
            check(getattr(g.guard, field) == getattr(h.guard, field), ('guard mismatch', g.name, field))
    count('factor_equalities')


def test_source(name, data, SparseParallelCompiler, ParallelCompiler):
    a, b = SparseParallelCompiler(data), ParallelCompiler(data)
    check(a.radius == b.radius, ('compiler radius mismatch', name))
    check(a.metadata.ledger() == b.old.ledger(), ('lazy source ledger mismatch', name))
    for field in ('E', 'P'):
        s, e = getattr(a, field), getattr(b, field)
        for parameter in ('b', 'r', 'H', 'radius'):
            check(getattr(s, parameter) == getattr(e, parameter), ('block geometry mismatch', name, field, parameter))
    check(a.ledger()['radius'] == b.ledger()['radius'], ('parallel ledger radius mismatch', name))
    count('sources')
    for j, g in enumerate(b.old.E+b.old.P):
        h = a.gate_at(j)
        factor_equal(g, h)
        detectors = enabled_detectors(g)
        for label, shape in enumerate((g.P, g.Q)):
            shift = -103 if (j+label) % 2 else 79
            x = translate(shape, shift)
            compare(a, b, x, (name, j, label, 'bare'), verify=(j % 23 == 0))
            count('endpoint_orientations')
            if detectors is not None and g.guard is not None:
                x = x | translate(detectors, shift)
                compare(a, b, x, (name, j, label, 'guard-enabled'), verify=True)
                block = a.E if j < a.metadata.E_count else a.P
                check(block.candidates(x).get((j, shift)) == label, ('enabled endpoint missing', name, j, label))
                count('enabled_guard_endpoints')
            noise = shift + RNG.choice((-g.L-1, -g.L, -g.B, 0, g.B, g.L, g.L+1))
            compare(a, b, x | {noise}, (name, j, label, 'spoiler'))
            count('endpoint_spoilers')
    for q, sign, counters in itertools.product(a.metadata.controls, ('+', '-'), ((0, 0), (1, 0), (0, 1), (2, 3))):
        x = a.encode(q, *counters, sign=sign)
        check(x == b.old.encode(q, *counters, sign=sign), ('encoding mismatch', name, q, sign, counters))
        compare(a, b, x, (name, q, sign, counters), verify=True, local=(q == a.metadata.start and counters == (0, 0)))
        count('encoded_states')
    for trial in range(12):
        x = frozenset(RNG.randrange(-2*a.metadata.Z, 2*a.metadata.Z+1) for _ in range(RNG.randrange(17)))
        compare(a, b, x, (name, 'random', trial), verify=True, local=(trial < 2))
        count('random_supports')
    x = a.encode(a.metadata.start, 2, 3)
    for shift in ((1 << 2048)+117, -(1 << 2048)-131):
        shifted = translate(x, shift)
        compare(a, b, shifted, (name, 'huge', shift > 0), verify=True, local=True)
        for inverse in (False, True):
            check(a.step(shifted, inverse=inverse) == translate(a.step(x, inverse=inverse), shift), ('2048-bit translation', name, inverse))
        for field in ('E', 'P'):
            block = getattr(a, field)
            check(dict(block.candidates(shifted)) == {(j, u+shift): label for (j, u), label in block.candidates(x).items()}, ('candidate translation', name, field))
            for i in sorted(x)[:3]:
                check(block.local_output(shifted, i+shift) == block.local_output(x, i), ('local translation', name, field))
        count('huge_translations')
    print('source', name, 'passed', flush=True)


def test_malformed(SparseParallelCompiler, ParallelCompiler):
    a, b = SparseParallelCompiler(source()), ParallelCompiler(source())
    cascade = frozenset((-118, -112, 0, 18, 23))
    compare(a, b, cascade, 'cascade', verify=True, local=True, trace=True)
    fixture = {}
    for field in ('E', 'P'):
        block, eager = getattr(a, field), getattr(b, field)
        raw, active = block.candidates(cascade), block.eligible(cascade)
        check(len(raw) == 1 and not active, ('cascade not rejected', field, dict(raw), dict(active)))
        check(block.apply(cascade) == cascade, ('cascade changed', field))
        key, label = next(iter(eager.candidates(cascade).items()))
        naive = eager.swap(cascade, key, label)
        check(set(eager.candidates(naive)) != set(eager.candidates(cascade)), ('cascade did not create key', field))
        fixture[field] = dict(initial_candidates=[[j, u, label] for (j, u), label in raw.items()], naive_output=sorted(naive))
    check(a.step(cascade) == cascade and b.old.step(cascade) != cascade, 'ordered/parallel distinction lost')
    universes = [(-119, -118, -114, -113, -112, 0, 18, 19, 23, 24, 25),
                 (-380, -19, -18, -17, -13, -12, -10, -9, 0, 380)]
    for n, universe in enumerate(universes):
        for mask in range(1 << len(universe)):
            x = frozenset(v for bit, v in enumerate(universe) if mask >> bit & 1)
            compare(a, b, x, ('exhaustive', n, mask), verify=True, local=(mask % 127 == 0))
            count('exhaustive_supports')
        print('malformed universe', n, 'passed', flush=True)
    base = a.encode('q', 2, 4)
    far = 3*max(a.E.H, a.P.H)+17
    x = base | translate(base, far) | translate(base, 2*far)
    compare(a, b, x, 'three simultaneous copies', verify=True, local=True, trace=True)
    for name in ('E', 'P'):
        block = getattr(a, name)
        active = block.eligible(x)
        check(len(active) == 3, ('not genuinely simultaneous', name, dict(active)))
        expected = set(x)
        # Independent simultaneous union of deletions and additions computed
        # exclusively from the original support and its selected orientations.
        deletions, additions = set(), set()
        for (j, u), label in active.items():
            gate = a.gate_at(j)
            shapes = (gate.P, gate.Q)
            deletions.update(u+v for v in shapes[label])
            additions.update(u+v for v in shapes[1-label])
        expected.difference_update(deletions); expected.update(additions)
        check(block.apply(x) == frozenset(expected), ('simultaneous update equation', name))
        count('simultaneous_block_checks')
    # H is inclusive. These configurations need not have an active endpoint;
    # exact agreement tests the competition boundary in either orientation.
    pair = b.old.E[0].P
    for block in (a.E, a.P):
        for distance in (block.H-1, block.H, block.H+1, 2*block.H+3):
            compare(a, b, frozenset(pair) | translate(pair, distance), ('exclusion_boundary', block.H, distance), verify=True, local=True)
            count('exclusion_boundaries')
    return dict(cascade=dict(input=sorted(cascade), blocks=fixture), exhaustive_universe_sizes=list(map(len, universes)), simultaneous_copies=3)


def test_guards(SparseParallelCompiler, ParallelCompiler):
    data = source(branches=[branch('guard', 'q', 'h', -1, 0, {'op': 'and', 'args': [
        {'op': 'gt', 'counter': 0, 'value': 1},
        {'op': 'not', 'arg': {'op': 'eq', 'counter': 1, 'value': 0}}]})], J=3)
    a, b = SparseParallelCompiler(data), ParallelCompiler(data)
    g = b.old.E[0]
    # Include all exact detector classes, the no-detector high class, malformed
    # multiple detectors, and particles immediately outside the detector band.
    choices = [(), (0,), (1,), (2,), (3,), (0, 1), (1, 3), (-1,), (4,)]
    for left, right, label in itertools.product(choices, choices, (0, 1)):
        detector = {-a.metadata.Z-k for k in left} | {a.metadata.Z+k for k in right}
        x = frozenset((g.P, g.Q)[label]) | detector
        compare(a, b, x, ('guard_detectors', left, right, label), verify=True, local=((left, right) in (((), ()), ((0, 1), (2,)), ((2,), (3,)))))
        should = len(left) <= 1 and len(right) <= 1
        lc = left[0] if left and 0 <= left[0] <= 3 else 4
        rc = right[0] if right and 0 <= right[0] <= 3 else 4
        should = should and lc > 1 and rc != 0
        check(((0, 0) in a.E.candidates(x)) == should, ('detector truth table', left, right, label))
        count('detector_configurations')
    # Test the optional anchor filter, including negative/large centers and
    # exactly inclusive interval endpoints, without changing predicate context.
    x = a.encode('q', 2, 3)
    x = x | translate(x, 4*a.E.H+17)
    for name, offset in (('E', 0), ('P', a.metadata.E_count)):
        sparse, eager = getattr(a, name), getattr(b, name)
        for center, radius in itertools.product((-sparse.H, 0, sparse.H, 4*a.E.H+17, 1 << 2048), (0, 1, sparse.b, sparse.H)):
            check(dict(sparse.candidates(x, center=center, radius=radius)) == globalize(eager.candidates(x, center=center, radius=radius), offset), ('candidate interval mismatch', name, center, radius))
            count('candidate_interval_checks')


def test_api(SparseParallelCompiler, ParallelCompiler):
    data = source()
    a, b = SparseParallelCompiler(data), ParallelCompiler(data)
    x = a.encode('q', 0, 0)
    want = a.step(x)
    class IntSubclass(int):
        pass
    class SetSubclass(set):
        pass
    class FrozenSubclass(frozenset):
        pass
    invalid_positions = [[], tuple(x), iter(x), None, '123', {True}, {False}, {1.0}, {IntSubclass(1)}, {'1'}, SetSubclass(x), FrozenSubclass(x), {1+0j}]
    for value in invalid_positions:
        actions = [lambda value=value: a.step(value)]
        for block in (a.E, a.P):
            actions.extend([lambda value=value, block=block: block.candidates(value),
                            lambda value=value, block=block: block.eligible(value),
                            lambda value=value, block=block: block.apply(value),
                            lambda value=value, block=block: block.local_output(value)])
        for action in actions:
            rejects(action)
    for value in (0, 1, None, 'true', [], 1.0, IntSubclass(0)):
        for flag in ('inverse', 'verify', 'trace'):
            rejects(lambda value=value, flag=flag: a.step(x, **{flag: value}))
        for block in (a.E, a.P):
            for flag in ('verify', 'trace'):
                rejects(lambda value=value, flag=flag, block=block: block.apply(x, **{flag: value}))
    for value in (True, False, 0.0, IntSubclass(0), '0', None):
        for block in (a.E, a.P):
            rejects(lambda value=value, block=block: block.local_output(x, value))
            rejects(lambda value=value, block=block: block.candidates(x, center=value, radius=1), (TypeError, ValueError))
            rejects(lambda value=value, block=block: block.candidates(x, center=0, radius=value), (TypeError, ValueError))
        rejects(lambda value=value: a.gate_at(value))
    for block in (a.E, a.P):
        for kwargs in ({'center': 0}, {'radius': 1}, {'center': 0, 'radius': -1}):
            rejects(lambda kwargs=kwargs, block=block: block.candidates(x, **kwargs), (TypeError, ValueError))
        immutable_map(block.candidates(x)); immutable_map(block.eligible(x))
        mutable = set(x)
        raw = block.candidates(mutable)
        snapshot = dict(raw)
        active = block.eligible(mutable)
        active_snapshot = dict(active)
        mutable.clear()
        check(dict(raw) == snapshot and dict(active) == active_snapshot, 'candidate map retained mutable input')
    for index in (-1, a.metadata.factors, a.metadata.factors+1):
        rejects(lambda index=index: a.gate_at(index), ValueError)
    for args in ((True, 0, 0), ('missing', 0, 0), ('q', True, 0), ('q', 0, 1.0), ('q', -1, 0), ('q', 0, -1), ('q', IntSubclass(0), 0)):
        rejects(lambda args=args: a.encode(*args), (TypeError, ValueError))
    for sign in (None, True, 1, '+-', ''):
        rejects(lambda sign=sign: a.encode('q', 0, 0, sign=sign), (TypeError, ValueError))
    for target, name, value in ((a, 'radius', 0), (a, 'E', None), (a, 'metadata', None),
                                (a.E, 'r', 0), (a.P, 'H', 0), (a.metadata, 'D', 0),
                                (a.metadata.branches[0], 'delta', 0)):
        rejects(lambda target=target, name=name, value=value: setattr(target, name, value), dataclasses.FrozenInstanceError)
    for raw in (a.metadata.source_data, a.metadata.control_index, a.metadata.home_out, a.metadata.home_in,
                a.metadata.source_data['branches'][0], a.metadata.source_data['branches'][0]['guard']):
        rejects(lambda raw=raw: raw.__setitem__('unexpected', None), (TypeError, AttributeError))
    mutable = set(x)
    y = a.step(mutable)
    mutable.clear()
    check(type(y) is frozenset and y == want, 'output retained mutable input')
    data['controls'].append('extra')
    data['branches'][0]['guard']['op'] = 'invalid'
    data['branches'].clear()
    check(a.metadata.controls == ('q', 'h') and a.step(x) == want, 'source aliases changed compiled rule')
    ledger = a.ledger()
    ledger['radius'] = -1
    if 'alphabet' in ledger:
        ledger['alphabet'].append(2)
    check(a.ledger()['radius'] == b.radius, 'ledger dictionary alias')
    check(a.metadata.ledger()['alphabet'] == [0, 1], 'ledger nested alias')
    compare(a, b, x, 'API trace', verify=True, trace=True)
    original = source()
    bad = []
    for path, value in [(('class_cut',), True), (('class_cut',), -1), (('controls',), ('q', 'h')),
                        (('start',), 1), (('halt',), 'missing'), (('schema',), 'no'),
                        (('branches', 0, 'side'), True), (('branches', 0, 'delta'), 1.0),
                        (('branches', 0, 'side'), 0), (('branches', 0, 'target'), 'missing'),
                        (('branches', 0, 'source'), 'h'),
                        (('branches', 0, 'guard'), {'op': 'eq', 'counter': 1, 'value': 0}),
                        (('branches', 0, 'guard'), {'op': 'eq', 'counter': True, 'value': 0})]:
        data = copy.deepcopy(original)
        at = data
        for key in path[:-1]:
            at = at[key]
        at[path[-1]] = value
        bad.append(data)
    data = copy.deepcopy(original); data['branches'] *= 2; bad.append(data)
    data = copy.deepcopy(original); data['extra'] = 1; bad.append(data)
    data = copy.deepcopy(original); data['branches'][0]['guard'] = {'op': 'not'}; bad.append(data)
    data = copy.deepcopy(original); data['branches'][0]['delta'] = -1; bad.append(data)
    data = copy.deepcopy(original); data['branches'].append(branch('dup', 'q', 'h', 1, 1)); bad.append(data)
    cycle = {'op': 'not'}; cycle['arg'] = cycle
    data = copy.deepcopy(original); data['branches'][0]['guard'] = cycle; bad.append(data)
    for number, data in enumerate(bad):
        outcomes = []
        for constructor in (SparseParallelCompiler, ParallelCompiler):
            try:
                constructor(data)
            except (TypeError, ValueError) as exc:
                outcomes.append(type(exc).__name__)
            else:
                outcomes.append(None)
        check(outcomes[0] is not None and outcomes[0] == outcomes[1], ('source rejection mismatch', number, outcomes))
        count('invalid_source_equalities')



def test_no_eager_runtime(SparseParallelCompiler):
    import sparse_parallel as implementation
    metadata_module = implementation._metadata
    reference = implementation._ref
    lazy_type = metadata_module.LazySource
    original_gate_at = lazy_type.gate_at
    materialized = []
    def forbidden(*args, **kwargs):
        raise RuntimeError('Sparse runtime called eager construction or ordered execution')
    def one_template(self, index):
        materialized.append(index)
        return original_gate_at(self, index)
    n = 128
    controls = ['q'+str(i) for i in range(n)]
    data = source(controls, [branch('e'+str(i), controls[i], controls[i+1], (-1, 1)[i % 2], 1) for i in range(n-1)])
    # These sentinels test the actual pinned modules loaded by sparse_parallel,
    # not unrelated imports with the same public class/function names.
    with patch.object(reference, 'compile_source', forbidden), \
         patch.object(reference, '_compile_validated', forbidden), \
         patch.object(reference.CompiledSource, 'step', forbidden), \
         patch.object(reference.Gate, 'apply', forbidden), \
         patch.object(reference.Gate, '_apply', forbidden), \
         patch.object(lazy_type, 'step', forbidden), \
         patch.object(lazy_type, 'gate_at', one_template):
        a = SparseParallelCompiler(data)
        check(not materialized, 'constructor materialized endpoint templates')
        check(a.metadata.factors > 700000, 'large source fixture too small')
        check(not hasattr(a.metadata, 'E') and not hasattr(a.metadata, 'P'), 'metadata stores eager factor arrays')
        x = a.encode(a.metadata.start, 2, 3)
        y, trace = a.step(x, verify=True, trace=True)
        check(a.step(y, inverse=True, verify=True) == x, 'sentinel runtime inverse failed')
        for block in (a.E, a.P):
            block.candidates(x); block.eligible(x)
            by = block.apply(x, verify=True)
            for i in sorted(x | by):
                check(block.local_output(x, i) == int(i in by), 'sentinel local-output mismatch')
        check(len(set(materialized)) < 32, ('runtime enumerated factors', len(set(materialized))))
        check(all(0 <= j < a.metadata.factors for j in materialized), 'runtime requested invalid factor')
        immutable_trace(trace)
        count('no_eager_runtime_checks')
        count('large_source_factors', a.metadata.factors)
        count('large_source_materialized_distinct', len(set(materialized)))
    print('eager-construction and ordered-execution sentinels passed', flush=True)



def test_probe_bounds(SparseParallelCompiler):
    a = SparseParallelCompiler(source())
    cls = type(a.E)
    original_raw = cls._raw
    base = a.encode('q', 2, 4)
    far = 3*max(a.E.H, a.P.H)+17
    fixtures = [
        ('empty', frozenset()),
        ('singleton', frozenset({1 << 2048})),
        ('free_pair', a.gate_at(0).P),
        ('cascade_rejected', frozenset((-118, -112, 0, 18, 23))),
        ('encoded', base),
        ('competing_copies', base | translate(base, a.E.H)),
        ('three_separated_copies', base | translate(base, far) | translate(base, 2*far)),
        ('dense_malformed', frozenset(range(-5, 6))),
    ]
    max_unverified = max_verified = 0
    for name, x in fixtures:
        for inverse, verify in itertools.product((False, True), repeat=2):
            calls = []
            def counted_raw(self, support, center=None, radius=None):
                calls.append((self.name, len(support), center, radius))
                return original_raw(self, support, center, radius)
            with patch.object(cls, '_raw', counted_raw):
                y, trace = a.step(x, inverse=inverse, verify=verify, trace=True)
            n = len(x)
            check(len(y) == n, ('probe fixture mass', name, inverse, verify))
            bound = 2*n+4 if verify else n+2
            check(len(calls) <= bound, ('raw support probe bound exceeded', name, inverse, verify, n, len(calls), bound))
            hypothetical = sum(block.prospective_queries for block in trace.blocks)
            check(hypothetical <= 2*(n//2), ('hypothetical call bound exceeded', name, inverse, verify, n, hypothetical))
            check(all(block.prospective_queries <= n//2 for block in trace.blocks), ('per-block isolation bound', name, inverse, verify))
            check(sum(center is None for _, _, center, _ in calls) == (4 if verify else 2), ('unexpected unfiltered raw probes', name, inverse, verify))
            check(len(calls) == (4+2*hypothetical if verify else 2+hypothetical), ('trace/raw probe accounting', name, inverse, verify))
            check(all(mass == n for _, mass, _, _ in calls), ('hypothetical probe changed support mass', name))
            for block_name, _, center, radius in calls:
                if center is not None:
                    block = getattr(a, block_name)
                    check(type(center) is int and radius == block.b+block.r, ('prospective neighborhood', name, block_name))
            if name == 'cascade_rejected':
                check(hypothetical == 2 and y == x and all(not block.selected for block in trace.blocks), 'cascade rejection skipped prospective probes')
            if name == 'three_separated_copies':
                expected_selected = (3, 0) if inverse else (3, 3)
                check(hypothetical == sum(expected_selected) and tuple(len(block.selected) for block in trace.blocks) == expected_selected, 'separated-copy probe fixture failed')
            if verify:
                max_verified = max(max_verified, len(calls))
            else:
                max_unverified = max(max_unverified, len(calls))
            count('raw_probe_bound_checks')
    count('max_unverified_raw_probes', max_unverified)
    count('max_verified_raw_probes', max_verified)
    print('raw and hypothetical support-probe bounds passed', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    parser.add_argument('--section', choices=('all', 'api', 'sources', 'malformed', 'guards'), default='all')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    began = time.perf_counter()
    for filename, expected in PINS.items():
        check(hashlib.sha256((ROOT/filename).read_bytes()).hexdigest() == expected, ('oracle hash mismatch', filename))
    from sparse_parallel import SparseParallelCompiler
    from parallel_particles import ParallelCompiler
    if args.section in ('all', 'api'):
        test_api(SparseParallelCompiler, ParallelCompiler)
        test_no_eager_runtime(SparseParallelCompiler)
        test_probe_bounds(SparseParallelCompiler)
        print('API passed', flush=True)
    if args.section in ('all', 'sources'):
        for name, data in sources():
            test_source(name, data, SparseParallelCompiler, ParallelCompiler)
    fixtures = None
    if args.section in ('all', 'malformed'):
        fixtures = test_malformed(SparseParallelCompiler, ParallelCompiler)
    if args.section in ('all', 'guards'):
        test_guards(SparseParallelCompiler, ParallelCompiler)
        print('guard detector and interval tests passed', flush=True)
    receipt = dict(status='passed', optimized=bool(sys.flags.optimize), section=args.section,
                   counts=COUNTS, fixtures=fixtures, elapsed_seconds=time.perf_counter()-began,
                   oracle_sha256=PINS,
                   sparse_parallel_sha256=hashlib.sha256((ROOT/'sparse_parallel.py').read_bytes()).hexdigest(),
                   test_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    name = 'test-sparse-parallel' + ('-optimized' if sys.flags.optimize else '')
    if args.section != 'all':
        name += '-' + args.section
    (args.output_dir/(name+'-receipt.json')).write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
