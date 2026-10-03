"""Independent targeted audit of lazy exactness; never builds universal factors."""
import copy
import hashlib
import itertools
import json
from pathlib import Path
import random
import time
import sys
import lazy_reversible as lazy
ref = lazy.ref
ROOT = Path(__file__).resolve().parent

def _require(condition, message='audit condition failed'):
    if not condition:
        raise AssertionError(message)

def source(controls, rows, J=2):
    return {'schema': 'reversible-two-counter-v1', 'controls': controls, 'start': controls[0], 'halt': controls[-1], 'class_cut': J, 'branches': rows}

def row(name, q, target, side, delta, guard=None):
    return dict(name=name, source=q, target=target, side=side, delta=delta, guard=guard or {'op': 'true'})

def atom(op, counter, value):
    return dict(op=op, counter=counter, value=value)

def fixtures():
    yield source(['h'], [], 0)
    yield source(['q', 'h'], [row('zero', 'q', 'h', -1, 0)], 0)
    yield source(['q', 'h'], [row('e', 'q', 'h', 1, 1)], 0)
    rows = []
    controls = ['q' + str(i) for i in range(7)]
    for i, (side, delta) in enumerate([(-1, 1), (1, 0), (-1, -1), (1, 1), (-1, 0), (1, -1)]):
        guard = atom('gt', int(side == 1), 0) if delta == -1 else None
        rows.append(row('e' + str(i), controls[i], controls[i + 1], side, delta, guard))
    yield source(controls, rows)
    yield source(['q', 'r', 'h'], [row('up', 'q', 'r', -1, 1, atom('eq', 0, 0)), row('direct', 'q', 'r', 1, 0, atom('gt', 0, 1)), row('down', 'q', 'r', -1, -1, atom('eq', 0, 1)), row('finish', 'r', 'h', 1, 0)], 2)

def main():
    begun = time.perf_counter()
    counts = {k: 0 for k in ['sources', 'gate_descriptors', 'endpoint_candidate_checks', 'sparse_gate_checks', 'guard_checks', 'step_checks', 'validation_checks', 'subset_step_checks', 'validation_fuzz_checks']}
    digest = hashlib.sha256(Path(ref.__file__).read_bytes()).hexdigest()
    _require(digest == lazy.FROZEN_SHA256)
    compiled = []

    def check_gate(g, x):
        _require(lazy.apply_gate(g, x, True)[0] == g.apply(x, True))
        counts['sparse_gate_checks'] += 1
    for data in fixtures():
        c = ref.compile_source(data)
        l = lazy.compile_lazy_source(data)
        compiled.append((c, l))
        counts['sources'] += 1
        _require(c.ledger() == l.ledger())
        _require(c.source_data == l.source_data)
        for q in c.controls:
            for sign in ('+', '-'):
                _require(c.encode(q, 0, 10 ** 50, sign) == l.encode(q, 0, 10 ** 50, sign))
        for i, g in enumerate(c.E + c.P):
            _require(l.gate_at(i) == g, (i, g, l.gate_at(i)))
            counts['gate_descriptors'] += 1
            for shape in g.shapes:
                for shift in (-10 ** 50, -19, 0, 23, 10 ** 80):
                    x = frozenset((shift + z for z in shape))
                    _require(i in l.candidate_indices(x), (i, g.name, shape, shift))
                    _require(set(g.raw(x)) == {shift})
                    counts['endpoint_candidate_checks'] += 1
                    check_gate(g, x)
                for offset in (-g.L - 1, -g.L, -g.L + 1, -g.B - 1, -g.B, g.B, g.B + 1, g.L - 1, g.L, g.L + 1):
                    check_gate(g, frozenset(shape) | {offset})
                for separation in (g.M - 1, g.M, g.M + 1):
                    check_gate(g, frozenset(shape) | frozenset((separation + z for z in g.shapes[1])))
            if g.guard is not None:
                choices = [(), (0,), (g.guard.J,), (0, g.guard.J)] if g.guard.J else [(), (0,)]
                for left, right in itertools.product(choices, repeat=2):
                    x = frozenset([-g.guard.Z - k for k in left] + [g.guard.Z + k for k in right])
                    _require(lazy._guard_sparse(g.guard, sorted(x), 0) == g.guard.allows(x, 0))
                    counts['guard_checks'] += 1
        rng = random.Random(1958 + len(c.branches))
        factors = c.E + c.P
        seeds = [frozenset(), frozenset({0}), frozenset({-1, 0, 1})]
        for _ in range(80):
            x = set()
            for _ in range(rng.randrange(1, 4)):
                g = rng.choice(factors)
                shape = rng.choice(g.shapes)
                shift = rng.choice([0, 1, -1, c.Z, -c.Z, 3 * c.B3 + 1, -3 * c.B3 - 1, 10 ** 30])
                x.update((shift + z for z in shape))
            if rng.randrange(2):
                x.add(rng.randrange(-c.Z, c.Z + 1))
            seeds.append(frozenset(x))
        for x in seeds:
            for inverse in (False, True):
                y = l.step(x, inverse, True)
                _require(y == c.step(x, inverse, True), (c.ledger(), inverse, x))
                _require(l.step(y, not inverse, True) == x)
                counts['step_checks'] += 1
    c, l = compiled[2]
    x = frozenset({-118, -112, 0, 18, 23})
    traces = {}
    for block_name, block in [('E', c.E), ('P', c.P)]:
        y = x
        events = []
        for i, g in enumerate(block):
            z = g.apply(y, True)
            if z != y:
                events.append(dict(index=i, name=g.name, before=sorted(y), after=sorted(z)))
            y = z
        z = y
        for g in block:
            z = g.apply(z, True)
        _require(z != x)
        traces[block_name] = dict(events=events, twice=sorted(z))
    _require([e['index'] for e in traces['E']['events']] == [0, 1])
    _require([e['index'] for e in traces['P']['events']] == [0, 12])
    _require(l.step(x, verify=True) == c.step(x, verify=True))
    universes = [(-119, -118, -114, -113, -112, 0, 18, 19, 23, 24, 25), (-380, -19, -18, -17, -13, -12, -10, -9, 0, 1, 380)]
    for universe in universes:
        for mask in range(1 << len(universe)):
            x = frozenset((z for j, z in enumerate(universe) if mask & 1 << j))
            for inverse in (False, True):
                y = l.step(x, inverse, True)
                _require(y == c.step(x, inverse, True), (universe, mask, inverse))
                _require(l.step(y, not inverse, True) == x)
                counts['subset_step_checks'] += 1
    g = c.P[0]
    x = frozenset(g.shapes[0]) | frozenset((g.M + z for z in g.shapes[1])) | {g.M + g.B + 1}
    _require(g.raw(x) == {0: 0, g.M: 1})
    _require(g.apply(x, True) == x)
    _require(lazy.apply_gate(g, x, True) == (x, ()))
    x = frozenset(g.shapes[0]) | frozenset((g.M + 1 + z for z in g.shapes[1]))
    y, keys = lazy.apply_gate(g, x, True)
    _require(keys == (0, g.M + 1) and y == g.apply(x, True))
    good = source(['q', 'r', 'h'], [row('first', 'q', 'r', 1, 0)], 0)
    bad = []
    for path, value in [('schema', False), ('controls', ()), ('class_cut', True), ('start', 0), ('halt', 'missing'), ('branches', ())]:
        d = copy.deepcopy(good)
        d[path] = value
        bad.append(d)
    for field, value in [('name', True), ('source', 0), ('target', 'missing'), ('side', True), ('side', 0), ('delta', False), ('delta', 2), ('guard', []), ('guard', {'op': 'eq', 'counter': 2, 'value': 0})]:
        d = copy.deepcopy(good)
        d['branches'][0][field] = value
        bad.append(d)
    for data in bad:
        errors = []
        for compiler in (ref.compile_source, lazy.compile_lazy_source):
            try:
                compiler(data)
            except Exception as e:
                errors.append(type(e).__name__)
            else:
                errors.append(None)
        _require(errors[0] == errors[1], errors)
        counts['validation_checks'] += 1
    rng = random.Random(88017)
    guards = [{'op': 'true'}, {'op': 'or', 'args': []}] + [atom(op, j, k) for op in ('eq', 'gt') for j in (0, 1) for k in (0, 1)]
    for _ in range(1000):
        controls = rng.sample(['q', 'r', 'h'], 3)
        rows = []
        for i in range(rng.randrange(5)):
            rows.append(row(str(i), rng.choice(controls[:2]), rng.choice(controls), rng.choice([-1, 1]), rng.choice([-1, 0, 1]), rng.choice(guards)))
        data = source(controls, rows, 2)
        outcomes = []
        for compiler in (ref.compile_source, lazy.compile_lazy_source):
            try:
                compiler(data)
            except Exception as e:
                outcomes.append((type(e).__name__, str(e)))
            else:
                outcomes.append(('accepted',))
        _require(outcomes[0] == outcomes[1], (data, outcomes))
        counts['validation_fuzz_checks'] += 1
    mixed = source(['q', 'r', 'h'], [row('first', 'q', 'r', 1, 0), row('overlap', 'q', 'r', 1, 0), row('bad', 'r', 'h', True, 0)], 0)
    validation_precedence = []
    for compiler in (ref.compile_source, lazy.compile_lazy_source):
        try:
            compiler(mixed)
        except Exception as e:
            validation_precedence.append({'type': type(e).__name__, 'message': str(e)})
    receipt = dict(status='passed' if validation_precedence[0]['type'] == validation_precedence[1]['type'] else 'passed except documented validation precedence', frozen_sha256=digest, lazy_sha256=hashlib.sha256(Path(lazy.__file__).read_bytes()).hexdigest(), counts=counts, cascade_input=[-118, -112, 0, 18, 23], cascades=traces, validation_precedence=validation_precedence, elapsed_seconds=time.perf_counter() - begun)
    receipt['optimization_level'] = sys.flags.optimize
    receipt['audit_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (ROOT / ('audit-receipt-optimized.json' if sys.flags.optimize else 'audit-receipt.json')).write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
if __name__ == '__main__':
    main()
