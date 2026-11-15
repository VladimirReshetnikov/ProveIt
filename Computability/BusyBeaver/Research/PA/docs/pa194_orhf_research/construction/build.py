#!/usr/bin/env python3
"""Reconstruct the two 194-state compositions and exact blank startups.

Python 3 standard library. No search or external repository is needed.
The known ORH layout, B selector and two shortcuts retain attribution.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
FAST = {(26, 1): (1, 1, 91), (101, 0): (0, 1, 17)}
B = {(87, 0): (0, 1, 88), (88, 0): (0, -1, 301),
     (301, 0): (0, 1, 122), (301, 1): (1, 1, 301)}

def read(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        assert key not in rows and d in ('L', 'R')
        rows[key] = int(w), 1 if d == 'R' else -1, int(n)
    return rows

def text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))

def digest(rows):
    return hashlib.sha256(text(rows).encode()).hexdigest()

def dense(rows):
    states = {q for q, _ in rows}
    assert len(states) == 194 and len(rows) == 388
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert all(w in (0, 1) and d in (-1, 1) for w, d, _ in rows.values())
    assert {n for _, _, n in rows.values()} - states == {254}
    labels, ix = [74], {74: 0}
    for q in labels:
        for b in (0, 1):
            n = rows[q, b][2]
            if n != 254 and n not in ix:
                ix[n] = len(labels)
                labels.append(n)
    assert set(labels) == states
    result = {(ix[q], b): (w, d, 194 if n == 254 else ix[n])
              for (q, b), (w, d, n) in rows.items()}
    return result, labels + [254]

def startup(rows, sites):
    path = sites[25][0]
    logical = [2] + [0] * 8
    physical = [0] * 9
    for i, j in enumerate((6, 2, 0, 4, 3, 7, 8, 5, 1)):
        physical[j] = logical[i]
    physical += [1] * 26
    expected = {-3, 46} | {-2 + i for i, b in enumerate(path) if b == '1'}
    p = 47
    for v in physical:
        p += 1
        expected.update(range(p, p + v + 1))
        p += v + 1
    q, h, ones = 74, 0, set()
    visits = {str(k): 0 for k in FAST}
    for t in range(100001):
        if (q, h, ones) == (84, -2, expected):
            return dict(steps=t, state=q, head=h, one_cells=sorted(ones),
                        physical_file=physical, complete_tape_equality=True,
                        shortcut_visits=visits)
        assert q != 254
        b = int(h in ones)
        if (q, b) in FAST:
            visits[str((q, b))] += 1
        w, d, q = rows[q, b]
        (ones.add if w else ones.discard)(h)
        h += d
    raise AssertionError('Exact initial source frame not reached')

def build(output):
    parent = read(ROOT / 'reference/PA194ORH/machine.native.tm')
    assert digest(read(ROOT / 'reference/PA194ORH/machine.tm')) == (
        'c16bef7a1587e31adaae747d5bad26721f30bb5c6c33dd4b798be95f5141f1d4')
    assert parent[26, 1] == (1, 1, 42)
    assert parent[101, 0] == (0, -1, 26)
    sites = json.loads((ROOT / 'reference/PA194ORH/sites.json').read_text())
    receipts = []
    for name, selector in [('PA194ORHF', False), ('PA194ORHBF', True)]:
        old = dict(parent)
        if selector:
            old.update(B)
            assert old == read(ROOT / 'reference/PA194ORHB/machine.native.tm')
        rows = dict(old)
        rows.update(FAST)
        table, labels = dense(rows)
        boot, oldboot = startup(rows, sites), startup(old, sites)
        saved = 2 * sum(boot['shortcut_visits'].values())
        assert oldboot['steps'] - boot['steps'] == saved
        out = output / name
        out.mkdir(parents=True, exist_ok=True)
        (out / 'machine.tm').write_text(text(table))
        (out / 'machine.native.tm').write_text(text(rows))
        (out / 'labels.json').write_text(json.dumps(labels) + '\n')
        changes = [{'state': q, 'read': b, 'old': parent[q, b], 'new': rows[q, b]}
                   for q, b in sorted(rows) if parent[q, b] != rows[q, b]]
        receipt = dict(name=name, working_states=194, transition_rows=388,
                       graph_reachable_working_states=194, start=0, halt=194,
                       native_start=74, native_halt=254, source_sites=len(sites),
                       source_outcomes=4778, startup=boot, parent_startup=oldboot,
                       startup_steps_saved=saved, edits_from_ORH=changes,
                       dense_sha256=digest(table), native_sha256=digest(rows),
                       contributions='New verified composition of attributed existing mechanisms',
                       formalization='Written iPRA proof; no new complete Lean/Rocq endpoint')
        (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        receipts.append(receipt)
    return receipts

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT / 'machines')
    args = ap.parse_args()
    assert __debug__, 'Run with assertions enabled'
    for r in build(args.output):
        print(r['name'], r['working_states'], r['dense_sha256'],
              'startup', r['startup']['steps'], 'saved', r['startup_steps_saved'])
