"""Read-only frozen-evaluator oracle generation for the new certificate tests.

Run with python -B. Outputs only in this research folder. No third-party packages.
"""
import hashlib
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
PIN = ROOT
sys.dont_write_bytecode = True
sys.path.insert(0, str(PIN))
from sparse_parallel import SparseParallelCompiler
from parallel_particles import ParallelCompiler


def branch(name='e', side=1, delta=1, guard=None):
    return dict(name=name, source='q', target='h', side=side, delta=delta,
                guard={'op': 'true'} if guard is None else guard)


def source(branches=None, J=0, controls=None):
    controls = ['q', 'h'] if controls is None else controls
    return dict(schema='reversible-two-counter-v1', controls=controls,
                start=controls[0], halt=controls[-1], class_cut=J,
                branches=[branch()] if branches is None else branches)


SOURCES = {'empty': source([], controls=['h']),
           'direct': source([branch(delta=0)]),
           'increment_right_zero': source([branch(guard={'op': 'eq', 'counter': 1, 'value': 0})], J=1),
           'guarded_direct': source([branch(delta=0, guard={'op': 'and', 'args': [
               {'op': 'gt', 'counter': 0, 'value': 1},
               {'op': 'not', 'arg': {'op': 'eq', 'counter': 1, 'value': 0}}]})], J=3)}
for side, name in [(-1, 'left'), (1, 'right')]:
    SOURCES['increment_' + name] = source([branch(side=side)])
    SOURCES['decrement_' + name] = source([branch(side=side, delta=-1,
        guard={'op': 'gt', 'counter': (side+1)//2, 'value': 0})], J=1)

COMPILED = {name: (SparseParallelCompiler(data), ParallelCompiler(data))
            for name, data in SOURCES.items()}
COUNTS = {'sparse_eager_snapshots': 0, 'block_checks': 0,
          'whole_direction_checks': 0, 'case_count': 0}


def check(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def rows(raw):
    return [[i, u, label] for (i, u), label in sorted(raw.items())]


def snapshot(name, positions):
    a, b = COMPILED[name]
    x = frozenset(positions)
    out = {'input': sorted(x), 'mass': len(x), 'blocks': {}}
    for bn in ('E', 'P'):
        block, eager = getattr(a, bn), getattr(b, bn)
        offset = 0 if bn == 'E' else a.metadata.E_count
        raw = dict(block.candidates(x))
        active = dict(block.eligible(x))
        check(raw == {(i+offset, u): label for (i, u), label in eager.candidates(x).items()},
              ('raw mismatch', name, bn, x))
        check(active == {(i+offset, u): label for (i, u), label in eager.eligible(x).items()},
              ('eligible mismatch', name, bn, x))
        y, trace = block.apply(x, verify=True, trace=True)
        check(y == eager.apply(x, verify=True), ('output mismatch', name, bn, x))
        check(block.apply(y) == x, ('involution', name, bn, x))
        out['blocks'][bn] = dict(raw=rows(raw), eligible=rows(active),
                                isolated_count=trace.isolated_keys, output=sorted(y))
        COUNTS['block_checks'] += 1
    for inverse in (False, True):
        y = a.step(x, inverse=inverse, verify=True)
        check(y == b.step(x, inverse=inverse, verify=True), ('whole mismatch', name, inverse, x))
        check(a.step(y, inverse=not inverse) == x, ('whole inverse', name, inverse, x))
        out['inverse_output' if inverse else 'forward_output'] = sorted(y)
        COUNTS['whole_direction_checks'] += 1
    COUNTS['sparse_eager_snapshots'] += 1
    return out


CASES = []


def add_case(cid, name, positions, **extra):
    item = dict(id=cid, source=name, **snapshot(name, positions), **extra)
    CASES.append(item)
    COUNTS['case_count'] += 1
    return item


def gate_case(cid, name, i, label, anchor=0, detectors=True, **extra):
    a, _ = COMPILED[name]
    g = a.gate_at(i)
    x = {anchor+d for d in g.shapes[label]}
    if detectors and g.guard is not None:
        for c0, row in enumerate(g.guard.table):
            if any(row):
                c1 = next(c for c, enabled in enumerate(row) if enabled)
                for side, c in [(-1, c0), (1, c1)]:
                    if c <= g.guard.J:
                        x.add(anchor+side*(g.guard.Z+c))
                break
    item = add_case(cid, name, x, focus=dict(block='E' if i < a.metadata.E_count else 'P',
                    key=[i, anchor], orientation=label, type_name=g.name), **extra)
    bn = item['focus']['block']
    check([i, anchor, label] in item['blocks'][bn]['raw'], ('focus not raw', cid))
    return item


for name in SOURCES:
    add_case(name + '_empty', name, [])
    add_case(name + '_singleton', name, [-7])

# Both orientations of every type in the smallest moving source. The oracle may
# enumerate its 95 types; this is test-data generation, never compiler syntax.
a, _ = COMPILED['increment_right']
for i in range(a.metadata.factors):
    for label in (0, 1):
        gate_case('all_types_%03d_%d' % (i, label), 'increment_right', i, label,
                  anchor=-103 if label else 79, category='all_type_orientations')

# Reverse-anchor hazards for both directions and both nonzero updates.
for name in ('increment_left', 'decrement_left', 'increment_right', 'decrement_right'):
    a, _ = COMPILED[name]
    m = a.metadata
    em = 2*m.D+6
    e = m.moving[0]
    for mode, i, w in [('O', 0, e.side), ('I', em, -e.side)]:
        item = gate_case('reverse_free_' + name + '_' + mode, name, i, 1, anchor=-103,
                        category='reverse_anchor', formula='u=h-w', expected_anchor=-103)
        pair = sorted(-103+d for d in a.gate_at(i).shapes[1])
        item['anchor_data'] = dict(h=pair[0], w=w)
        check(pair[0]-w == -103, 'free reverse anchor arithmetic')
    i = 2*em+1
    item = gate_case('reverse_endpoint_' + name, name, i, 1, anchor=79,
                    category='reverse_anchor', formula='u=z-v*delta', expected_anchor=79)
    item['anchor_data'] = dict(z=79+e.side*e.delta, v=e.side, delta=e.delta)

# Dispatch always uses the domain guard, commit always the image guard, even
# on their minus endpoint. Here domain is c1=0, image c1=1.
a, _ = COMPILED['increment_right_zero']
m = a.metadata
for family, i, good in [('dispatch', 2*(2*m.D+6), 0), ('commit', 2*(2*m.D+6)+2, 1)]:
    g = a.gate_at(i)
    for label, c in itertools.product((0, 1), (0, 1)):
        x = set(g.shapes[label]) | {m.Z+c}
        item = add_case('fixed_guard_%s_%d_%d' % (family, label, c), 'increment_right_zero', x,
                        category='orientation_fixed_guard',
                        focus=dict(block='E', key=[i, 0], orientation=label, type_name=g.name),
                        right_class=c, own_raw_expected=c == good)
        check(([i, 0, label] in item['blocks']['E']['raw']) == (c == good), 'fixed guard mismatch')

# Full finite detector corpus, including both closed endpoints, high/empty
# class, two particles within one band, and adjacent outside positions.
a, _ = COMPILED['guarded_direct']
m = a.metadata
g = a.gate_at(0)
choices = [[], [0], [1], [2], [3], [0, 1], [1, 3], [-1], [4]]
for li, left in enumerate(choices):
    for ri, right in enumerate(choices):
        for label in (0, 1):
            x = set(g.shapes[label]) | {-m.Z-k for k in left} | {m.Z+k for k in right}
            lc = [k for k in left if 0 <= k <= m.J]
            rc = [k for k in right if 0 <= k <= m.J]
            good = len(lc) <= 1 and len(rc) <= 1
            good = good and (lc[0] if lc else m.J+1) > 1 and (rc[0] if rc else m.J+1) != 0
            item = add_case('guard_bands_%d_%d_%d' % (li, ri, label), 'guarded_direct', x,
                            category='guard_boundaries', detector_offsets=dict(left=left, right=right),
                            focus=dict(block='E', key=[0, 0], orientation=label), own_raw_expected=good)
            check(([0, 0, label] in item['blocks']['E']['raw']) == good, 'guard band mismatch')

# L is type-specific: L=28 for this free pair, L=64 for the direct triple.
for name, i in [('increment_right', 0), ('direct', 0)]:
    a, _ = COMPILED[name]
    g = a.gate_at(i)
    for label, side, offset in itertools.product((0, 1), (-1, 1), (0, 1)):
        noise = side*(g.L+offset)
        x = set(g.shapes[label]) | {noise}
        item = add_case('exactness_%s_%d_%d_%d' % (name, label, side, offset), name, x,
                        category='exactness_boundary', focus=dict(block='E', key=[i, 0], orientation=label),
                        noise=noise, exactness_radius=g.L, own_raw_expected=offset == 1)
        check(([i, 0, label] in item['blocks']['E']['raw']) == (offset == 1), 'exactness boundary')

# H is inclusive. Farther by one permits two simultaneous pair swaps.
a, _ = COMPILED['increment_right']
for bn, i in [('E', 0), ('P', a.metadata.E_count)]:
    block = getattr(a, bn)
    g = a.gate_at(i)
    for delta in (-1, 0, 1):
        distance = block.H+delta
        x = set(g.shapes[0]) | {distance+d for d in g.shapes[0]}
        item = add_case('isolation_%s_%+d' % (bn, delta), 'increment_right', x,
                        category='isolation_boundary', focus_block=bn,
                        separation=distance, H=block.H)
        check(len(item['blocks'][bn]['raw']) == 2, 'isolation fixture lacks two raw keys')
        check(len(item['blocks'][bn]['eligible']) == (2 if delta == 1 else 0), 'isolation boundary')

# Literal malformed new/old separator; prospective rediscovery is essential.
a, b = COMPILED['increment_right']
x = frozenset((-118, -112, 0, 18, 23))
item = add_case('malformed_cascade', 'increment_right', x, category='prospective_rejection')
item['old_ordered_output'] = sorted(b.old.step(x))
item['prospective_details'] = {}
for bn in ('E', 'P'):
    block = getattr(a, bn)
    raw = dict(block.candidates(x))
    check(len(raw) == 1 and not block.eligible(x), ('cascade changed', bn))
    (i, u), label = next(iter(raw.items()))
    g = a.gate_at(i)
    y = frozenset((x-{u+d for d in g.shapes[label]}) | {u+d for d in g.shapes[1-label]})
    after = dict(block.candidates(y, center=u, radius=block.b+block.r))
    item['prospective_details'][bn] = dict(own_key=[i, u], orientation=label,
        hypothetical_output=sorted(y), after_raw=rows(after),
        born_keys=[list(k) for k in sorted(set(after)-set(raw))], radius=block.b+block.r)
check(item['forward_output'] == sorted(x) and item['old_ordered_output'] != sorted(x), 'old/new distinction')

# Exhaustive fixed-mass domains small enough to bind one compiled circuit per
# source/mass. All expected snapshots are included, not just checksums.
DOMAINS = []
domain_specs = [
    ('empty_mass3', 'empty', [0, 6, 7, 8, 11], 3),
    ('direct_mass3', 'direct', [0, 10, 11, 12, 13, 14], 3),
    ('moving_mass2', 'increment_right', list(range(9)), 2),
    ('moving_mass3', 'increment_right', [-18, -13, -10, 0, 18, 19, 23, 24], 3),
]
for did, name, universe, mass in domain_specs:
    records = [snapshot(name, x) for x in itertools.combinations(universe, mass)]
    stats = {bn: dict(raw_events=sum(len(r['blocks'][bn]['raw']) for r in records),
                     selected_events=sum(len(r['blocks'][bn]['eligible']) for r in records),
                     changed_supports=sum(r['blocks'][bn]['output'] != r['input'] for r in records))
             for bn in ('E', 'P')}
    check(any(s['raw_events'] for s in stats.values()), ('vacuous exhaustive domain', did))
    DOMAINS.append(dict(id=did, source=name, universe=universe, mass=mass,
                       support_count=len(records), stats=stats, cases=records))

HORIZONS = []
for name, support in [('empty', [0, 6, 7]), ('direct', [0, 10, 11]),
                      ('increment_right', [0, 5]),
                      ('increment_right', [-118, -112, 0, 18, 23])]:
    a, b = COMPILED[name]
    for inverse, horizon in itertools.product((False, True), range(4)):
        x = frozenset(support)
        history = [sorted(x)]
        eager_x = x
        for _ in range(horizon):
            x = a.step(x, inverse=inverse, verify=True)
            eager_x = b.step(eager_x, inverse=inverse, verify=True)
            check(x == eager_x, ('horizon mismatch', name, horizon, inverse))
            history.append(sorted(x))
        wrong = sorted(x)
        wrong[-1] += 1
        HORIZONS.append(dict(source=name, input=support, mass=len(support),
                             inverse=inverse, horizon=horizon, history=history,
                             accepted_target=sorted(x), rejected_target=wrong))

result = dict(schema='parallel-certificate-test-oracle-v1',
    provenance=dict(method='Pinned sparse and eager NEW parallel evaluators compared for every snapshot',
                    frozen_packet='sparse-parallel-evaluator-research-20261003',
                    sha256={p: hashlib.sha256((PIN/p if p not in ('SOURCE_SCHEMA.md','test_sparse_parallel.py') else PIN/'references'/p).read_bytes()).hexdigest() for p in [
                        'sparse_parallel.py', 'frozen_lazy_source.py', 'parallel_particles.py',
                        'frozen_reversible_binary.py', 'SOURCE_SCHEMA.md', 'test_sparse_parallel.py']},
                    no_frozen_edits=True, no_upstream_execution=True),
    interpretation=dict(raw_row='[global_type_ID, invariant_anchor, orientation]',
                        block_outputs='E and P independently applied to original input',
                        whole_outputs='forward is P(E(X)); inverse is E(P(X))',
                        ordered_output='Only malformed_cascade records the old ordered rule'),
    sources={name: dict(data=data, geometry=COMPILED[name][0].metadata.ledger(),
                       E=dict(b=COMPILED[name][0].E.b, r=COMPILED[name][0].E.r, H=COMPILED[name][0].E.H),
                       P=dict(b=COMPILED[name][0].P.b, r=COMPILED[name][0].P.r, H=COMPILED[name][0].P.H))
             for name, data in SOURCES.items()},
    cases=CASES, exhaustive_domains=DOMAINS, horizon_cases=HORIZONS,
    validation_counts=COUNTS)
(ROOT/'fixtures.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps({'validation_counts': COUNTS, 'domains': [
    {k:v for k,v in d.items() if k != 'cases'} for d in DOMAINS],
    'fixtures_sha256': hashlib.sha256((ROOT/'fixtures.json').read_bytes()).hexdigest()}, indent=2))
