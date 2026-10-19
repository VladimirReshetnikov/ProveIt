#!/usr/bin/env python3
"""Independent finite proof audit for the boundary/deferred-erasure square.

Reads literal machine tables as data. No inherited checker is imported.
Every unmentioned tape cell is a distinct free variable; reading one is fatal.
The semantic selector guard is deliberately reported as a separate premise.
"""
from pathlib import Path
import argparse
import hashlib
import json


def table(path):
    out = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        q, b, w, d, r = line.split()
        assert d in ('L', 'R') and b in ('0', '1') and w in ('0', '1')
        key = int(q), int(b)
        assert key not in out
        out[key] = int(w), (-1 if d == 'L' else 1), int(r)
    states = {q for q, _ in out}
    assert set(out) == {(q, b) for q in states for b in (0, 1)}
    assert all(r in states or r == 254 for _, _, r in out.values())
    assert 254 not in states and 95 in states
    return out


def delayed(old):
    assert old[147, 0] == (0, 1, 169)
    assert old[80, 0] == (0, 1, 25)
    assert old[91, 1] == (0, -1, 50)
    assert sorted(k for k, v in old.items() if v[2] == 169) == [(147, 0)]
    out = {k: v for k, v in old.items() if k[0] != 169}
    out[147, 0] = 0, 1, 80
    out[80, 0] = 0, -1, 106
    out[91, 1] = 1, -1, 167
    return out


def boundary(old):
    patches = {
        (179, 1): ((1, 1, 105), (1, -1, 215)),
        (187, 1): ((1, 1, 218), (1, 1, 179)),
        (220, 1): ((1, 1, 218), (1, 1, 179)),
        (223, 0): ((0, 1, 16), (0, 1, 23)),
        (223, 1): ((1, 1, 99), (1, 1, 70)),
        (237, 0): ((0, 1, 218), (0, 1, 223)),
    }
    assert old[218, 0] == (0, -1, 223) and old[218, 1] == (1, 1, 70)
    out = {k: v for k, v in old.items() if k[0] != 218}
    for k, (a, b) in patches.items():
        assert old[k] == a
        out[k] = b
    return out


def run(tab, q, facts, steps):
    tape = dict(facts)
    h = 0
    trace = []
    for _ in range(steps):
        assert h in tape, ('unconstrained exterior read', q, h)
        assert q != 254, 'halt reached inside comparison block'
        b = tape[h]
        w, d, r = tab[q, b]
        trace.append([q, h, b, w, d, r])
        tape[h] = w
        h += d
        q = r
    return q, h, tape, trace


def compare(old, new, name, qo, qn, facts, old_steps, new_steps):
    a = run(old, qo, facts, old_steps)
    b = run(new, qn, facts, new_steps)
    assert a[:3] == b[:3], (name, a, b)
    assert a[0] not in (169, 179, 218, 223), ('bad checkpoint', name, a[0])
    return {
        'name': name, 'old_state': qo, 'new_state': qn,
        'assumptions': facts, 'old_steps': old_steps, 'new_steps': new_steps,
        'endpoint_state': a[0], 'endpoint_head': a[1],
        'complete_tapes_equal': True,
        'old_trace': a[3], 'new_trace': b[3],
        'all_unmentioned_cells': 'Independent variables, never read or written.'
    }


def delayed_audit(old, new):
    assert new == delayed(old)
    predicates = {67: {-1: 0}, 80: {-2: 0, -1: 1},
                  91: {-3: 0, -2: 1, -1: 1}, 169: {-1: 0}}
    incoming = []
    for (q, b), (w, d, r) in sorted(old.items()):
        if r not in predicates:
            continue
        facts = dict(predicates.get(q, {}))
        facts[0] = w
        for off, val in predicates[r].items():
            assert facts.get(d + off) == val, ('invariant fails', q, b, r, off)
        incoming.append([q, b, r])
    assert 95 not in predicates
    for (q, b), (w, d, r) in old.items():
        if q in (80, 91, 169):
            continue
        assert new[q, b] == (w, d, 80 if r == 169 else r)
    specs = [
        ('80/0', 80, 80, {-1: 1, 0: 0}, 1, 5),
        ('80/1', 80, 80, {0: 1}, 1, 1),
        ('169/0', 169, 80, {-1: 0, 0: 0}, 1, 3),
        ('169/1', 169, 80, {-1: 0, 0: 1, 1: 1}, 1, 5),
        ('91/0', 91, 91, {0: 0}, 1, 1),
        ('91/1', 91, 91, {-3: 0, -2: 1, -1: 1, 0: 1}, 3, 11),
    ]
    blocks = [compare(old, new, *x) for x in specs]
    return {'status': 'PASS', 'structural_predicates': predicates,
            'incoming_preservation': incoming, 'blocks': blocks,
            'semantic_premise': 'At each old169/read1 visit, tape[h+1] = 1.'}


def boundary_audit(old, new):
    assert new == boundary(old)
    expected = {
        179: {(161, 0), (236, 0), (239, 0)},
        218: {(187, 1), (220, 1), (237, 0)},
        223: {(218, 0)},
    }
    incoming = {}
    for r, keys in expected.items():
        actual = {k for k, v in old.items() if v[2] == r}
        assert actual == keys
        incoming[r] = [[*k, *old[k]] for k in sorted(keys)]
    for k in expected[179]:
        assert old[k][:2] == (0, 1)
    for k in expected[218]:
        w, d, r = old[k]
        assert d == 1
        assert new[k] == (w, d, 179 if w == 1 else 223)
    assert old[218, 0] == (0, -1, 223)
    for (q, b), action in old.items():
        if q in (179, 218, 223) or action[2] == 218:
            continue
        assert new[q, b] == action
    specs = [
        ('179/tag0/read0', 179, 179, {-1: 0, 0: 0}, 1, 1),
        ('179/tag0/read1', 179, 179, {-1: 0, 0: 1}, 1, 5),
        ('218/tag0/read0', 218, 223, {-1: 0, 0: 0}, 3, 1),
        ('218/tag0/read1', 218, 223, {-1: 0, 0: 1}, 1, 1),
        ('218/tag1/read0', 218, 179, {-1: 1, 0: 0}, 3, 1),
        ('218/tag1/read1', 218, 179, {-1: 1, 0: 1}, 1, 3),
    ]
    blocks = [compare(old, new, *x) for x in specs]
    return {'status': 'PASS', 'incoming_ports': incoming, 'blocks': blocks,
            'scope': 'Every initial binary tape at state95 and head0.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference', type=Path, required=True,
                    help='Repaired boundary240, inherited labels')
    ap.add_argument('--boundary239', type=Path, required=True)
    ap.add_argument('--candidate238', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__
    a, b = table(args.reference), table(args.boundary239)
    assert len(a) == 480 and len(b) == 478
    assert b == boundary(a)
    c = delayed(a)
    d = delayed(b)
    assert d == boundary(c) and len(d) == 476
    if args.candidate238:
        assert table(args.candidate238) == d
    # Both proofs are redone on both edges, not inferred from disjoint row edits.
    da = delayed_audit(a, c)
    db = delayed_audit(b, d)
    ba = boundary_audit(a, b)
    bc = boundary_audit(c, d)
    assert da['blocks'] == db['blocks']
    assert ba['blocks'] == bc['blocks']
    assert da['incoming_preservation'] == db['incoming_preservation']
    assert ba['incoming_ports'] == bc['incoming_ports']
    delayed_rows = {tuple([r[0], r[2]]) for p in db['blocks']
                    for k in ('old_trace', 'new_trace') for r in p[k]}
    boundary_rows = {tuple([r[0], r[2]]) for p in bc['blocks']
                     for k in ('old_trace', 'new_trace') for r in p[k]}
    delayed_changed = {k for k in a.keys() | c.keys() if a.get(k) != c.get(k)}
    boundary_changed = {k for k in a.keys() | b.keys() if a.get(k) != b.get(k)}
    assert not delayed_rows & boundary_changed
    assert not boundary_rows & delayed_changed
    reached = {95}
    while True:
        nxt = reached | {r for q in reached if q != 254 for bit in (0, 1)
                         for _, _, r in [d[q, bit]]}
        if nxt == reached:
            break
        reached = nxt
    assert len(reached - {254}) == 238
    receipt = {
        'status': 'INDEPENDENT_238_COMPOSITION_PASS',
        'input_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in (args.reference, args.boundary239)
                         + ((args.candidate238,) if args.candidate238 else ())},
        'working_states': 238, 'transition_rows': 476,
        'deleted_states': [169, 218], 'all_states_graph_reachable': True,
        'commuting_square': True,
        'independently_replayed_blocks': 24,
        'distinct_block_identities': 12,
        'delayed_on_boundary239': db, 'boundary_after_delayed': bc,
        'delayed_changed_rows': sorted(delayed_changed),
        'boundary_changed_rows': sorted(boundary_changed),
        'delayed_block_rows': sorted(delayed_rows),
        'boundary_block_rows': sorted(boundary_rows),
        'no_cross_patch_block_interference': True,
        'guard_requirement': 'Fresh boundary239 selector guard is required for its delayed fold.',
        'proof_status': 'Finite ordinary mathematical certificate; no Lean compilation claimed.',
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in
                     ('delayed_on_boundary239', 'boundary_after_delayed',
                      'delayed_block_rows', 'boundary_block_rows')}, indent=2))


if __name__ == '__main__':
    main()
