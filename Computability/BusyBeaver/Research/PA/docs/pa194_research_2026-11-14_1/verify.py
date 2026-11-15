#!/usr/bin/env python3
"""Offline construction and exact local certificates for three PA194 variants.

The finite proof premises are checked from literal rows, independently of the
upstream compiler and arithmetic-box oracle. See report/report.pdf for the
quantifier-free induction which turns these premises into an all-time iPRA
halting equivalence. The absolute PA calibration is an identified dependency.
Python 3.10+, standard library only. Do not use -O.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import io
import itertools
import json
import zipfile

ROOT = Path(__file__).resolve().parent
FAMILIES = ('GD', 'GDH', 'GDHS')
START, HALT = 74, 254
FAST = {(26, 1): (1, 1, 91), (101, 0): (0, 1, 17)}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in rows
        rows[q, b] = w, 1 if d == 'R' else -1, n
    return rows

def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))

def mapped(q):
    return 127 if q == 124 else q

def build(parent):
    selector = {(q, b): (w, d, mapped(n))
                for (q, b), (w, d, n) in parent.items()}
    selector.update({(127, 0): (0, -1, 124),
                     (124, 0): (0, 1, 8), (124, 1): (1, 1, 59)})
    child = selector | FAST
    return selector, child

def structural(rows):
    controls = {q for q, b in rows}
    assert len(controls) == 194 and len(rows) == 388
    assert all((q, b) in rows for q in controls for b in (0, 1))
    assert {n for w, d, n in rows.values()} - controls == {HALT}
    assert START in controls and HALT not in controls
    labels, index = [START], {START: 0}
    for q in labels:
        for b in (0, 1):
            n = rows[q, b][2]
            if n != HALT and n not in index:
                index[n] = len(labels)
                labels.append(n)
    assert set(labels) == controls
    index[HALT] = 194
    dense = {(index[q], b): (w, d, index[n])
             for (q, b), (w, d, n) in rows.items()}
    return dense, labels + [HALT]

def predecessors(rows, target):
    return [(q, b, *act) for (q, b), act in sorted(rows.items()) if act[2] == target]

def local_run(rows, state, head, tape, steps):
    tape = dict(tape)
    trace = []
    touched = []
    for _ in range(steps):
        assert state != HALT and head in tape
        bit = tape[head]
        write, direction, target = rows[state, bit]
        trace.append([state, head, bit, write, direction, target])
        touched.append(head)
        tape[head] = write
        state, head = target, head + direction
    return (state, head, tape), trace, touched

def selector_certificate(parent, selector):
    assert parent[127, 0] == (0, 1, 14)
    assert parent[124, 0] == (0, 1, 62)
    assert parent[127, 1] == parent[124, 1] == (1, 1, 138)
    assert selector[8, 0] == (0, 1, 14)
    assert selector[59, 0] == (0, 1, 62)
    for q, history in ((127, 0), (124, 1)):
        pred = predecessors(parent, q)
        assert pred and all((row[2], row[3]) == (history, 1) for row in pred)
    for (q, b), (w, d, n) in parent.items():
        if q not in (124, 127):
            assert selector[q, b] == (w, d, mapped(n))
    cases = []
    for q, history in ((127, 0), (124, 1)):
        for bit in (0, 1):
            tape = {-1: history, 0: bit}
            old, _, _ = local_run(parent, q, 0, tape, 1)
            target = mapped(old[0]), old[1], old[2]
            length = 1 if bit else 3
            actual, trace, touched = local_run(selector, mapped(q), 0, tape, length)
            assert actual == target and set(touched) <= {-1, 0}
            cases.append({'old_state': q, 'history': history, 'read': bit,
                          'new_steps': length, 'trace': trace})
    return {'incoming127': predecessors(parent, 127),
            'incoming124': predecessors(parent, 124), 'cases': cases}

def acceleration_certificate(selector, child):
    assert predecessors(selector, 101) == [(96, 0, 0, 1, 101)]
    assert predecessors(selector, 26) == [(11, 0, 0, -1, 26), (101, 0, 0, -1, 26)]
    assert all(row[2] == 0 for row in predecessors(selector, 11))
    assert selector[26, 1] == (1, 1, 42)
    assert selector[42, 0] == (0, 1, 13)
    assert selector[13, 0] == (0, -1, 91)
    assert selector[101, 0] == (0, -1, 26)
    assert selector[26, 0] == (0, 1, 194)
    assert selector[194, 0] == (0, 1, 17)
    assert {key for key in selector if selector[key] != child[key]} == set(FAST)
    cases = []
    for bits in itertools.product((0, 1), repeat=5):
        tape = dict(zip(range(-2, 3), bits))
        for state, allowed in ((26, tape[0] == 1 and tape[1] == tape[2] == 0),
                               (101, tape[-1] == tape[0] == 0)):
            if not allowed:
                continue
            old, trace, touched = local_run(selector, state, 0, tape, 3)
            new, new_trace, _ = local_run(child, state, 0, tape, 1)
            assert old == new and set(touched) <= set(range(-1, 3))
            cases.append({'state': state, 'bits': bits, 'old_trace': trace,
                          'new_trace': new_trace})
    assert Counter(case['state'] for case in cases) == {26: 4, 101: 8}
    return {'incoming101': predecessors(selector, 101),
            'incoming26': predecessors(selector, 26),
            'incoming11': predecessors(selector, 11), 'cases': cases}

def scalar_step(rows, conf, uses=None):
    state, head, ones = conf
    if state == HALT:
        return state, head, ones
    bit = int(head in ones)
    if uses is not None:
        uses[state, bit] += 1
    write, direction, state = rows[state, bit]
    (ones.add if write else ones.discard)(head)
    return state, head + direction, ones

def mapped_conf(c):
    return mapped(c[0]), c[1], c[2]

def synchronized_startup(parent, selector, child, seed):
    old, middle = (START, 0, set()), (START, 0, set())
    middle_steps = 0
    selector_expansions = 0
    for _ in range(seed['steps']):
        duration = 3 if old[0] in (124, 127) and old[1] not in old[2] else 1
        selector_expansions += int(duration == 3)
        old = scalar_step(parent, old)
        for _ in range(duration):
            middle = scalar_step(selector, middle)
        middle_steps += duration
        assert middle == mapped_conf(old)
    expected = seed['state'], seed['head'], set(seed['one_cells'])
    assert old == middle == expected
    middle, final = (START, 0, set()), (START, 0, set())
    expanded_steps = 0
    fast_uses, final_uses = Counter(), Counter()
    for new_steps in range(middle_steps + 1):
        if final == expected:
            break
        key = final[0], int(final[1] in final[2])
        duration = 3 if key in FAST else 1
        if key in FAST:
            fast_uses[key] += 1
        final = scalar_step(child, final, final_uses)
        for _ in range(duration):
            middle = scalar_step(selector, middle)
        expanded_steps += duration
        assert final == middle and final[0] != HALT
    else:
        raise AssertionError('Full source frame was not reached')
    assert expanded_steps == middle_steps
    changed = {key for key in parent if parent[key] != child[key]}
    assert len(changed) == 6
    assert all(final_uses[key] > 0 for key in changed)
    return {'parent_steps': seed['steps'], 'selector_steps': middle_steps,
            'new_steps': new_steps, 'selector_expansions': selector_expansions,
            'shortcut_uses': {f'{q}/{b}': k for (q, b), k in sorted(fast_uses.items())},
            'all_changed_rows_used': {f'{q}/{b}': final_uses[q, b] for q, b in sorted(changed)},
            'state': expected[0], 'head': expected[1],
            'one_cells': sorted(expected[2]), 'complete_tape_equality_at_every_checkpoint': True}

def verify(output):
    if not __debug__:
        raise RuntimeError('Verification requires assertions; do not run with -O.')
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    for name, item in provenance['inputs'].items():
        assert digest((ROOT / name).read_bytes()) == item['sha256'], name
    archive = (ROOT / 'references/pa194_gd_research_2026-11-14.zip').read_bytes()
    assert hashlib.sha1(b'blob ' + str(len(archive)).encode() + b'\0' + archive).hexdigest() == provenance['source_archive_git_blob']
    with zipfile.ZipFile(io.BytesIO(archive)) as source:
        for name, item in provenance['inputs'].items():
            if 'archive_member' in item:
                assert source.read(item['archive_member']) == (ROOT / name).read_bytes(), name
    results = {}
    for family in FAMILIES:
        parent = read_table(ROOT / 'inputs' / (family + '.native.tm'))
        seed = json.loads((ROOT / 'inputs' / (family + '.receipt.json')).read_text())['startup']
        selector, child = build(parent)
        dense, labels = structural(child)
        structural(parent)
        structural(selector)
        selector_proof = selector_certificate(parent, selector)
        fast_proof = acceleration_certificate(selector, child)
        startup = synchronized_startup(parent, selector, child, seed)
        dest = output / ('PA194' + family + '_SF')
        dest.mkdir(parents=True, exist_ok=True)
        for name, rows in (('machine.tm', dense), ('machine.native.tm', child),
                           ('selector.native.tm', selector)):
            (dest / name).write_text(table_text(rows))
        (dest / 'labels.json').write_text(json.dumps(labels) + '\n')
        changes = [{'state': q, 'read': b, 'parent': parent[q, b], 'new': child[q, b]}
                   for q, b in sorted(parent) if parent[q, b] != child[q, b]]
        result = {'name': dest.name, 'working_states': 194, 'transitions': 388,
                  'graph_reachable_states': 194, 'start': 0, 'halt': 194,
                  'changes': changes, 'sha256': digest(table_text(dense).encode()),
                  'native_sha256': digest(table_text(child).encode()),
                  'parent_sha256': digest(table_text(parent).encode()),
                  'selector_certificate': selector_proof,
                  'acceleration_certificate': fast_proof, 'startup': startup,
                  'relative_time_bounds': {'parent_to_new': '3*t', 'new_to_parent': '3*t'},
                  'scope': 'Exact finite premises of the written relative iPRA proof; no end-to-end Lean claim.'}
        (dest / 'certificate.json').write_text(json.dumps(result, indent=2) + '\n')
        results[family] = result
        print(f"{dest.name}: 194 states, 16 local cases, startup {startup['new_steps']}, {result['sha256']}")
    return results

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT / 'machines')
    args = ap.parse_args()
    verify(args.output)
