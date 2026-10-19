#!/usr/bin/env python3
"""Reconstruct the exact 239-state table and verify its canonical renaming.

These finite checks establish the artifact's identity, not nonhalting.
New code in this report; inherited machine attribution is in ATTRIBUTION.md.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent.parent
OLD_SHA = '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'
NEW_SHA = '76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b'
CANON_SHA = '4447a2423907f2b96e8bcd6c88ed2d1e353f925fb8cf36ca913224ddce5914ba'
SITES_SHA = '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    rows = {}
    start = None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line[9:])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            assert (q, b) not in rows
            rows[q, b] = (w, d, z)
    states = {q for q, _ in rows}
    assert start in states
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    return rows, start


def serialize(rows, start):
    return ('#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {z}\n'
        for (q, b), (w, d, z) in sorted(rows.items()))).encode('ascii')


def construct(root=ROOT):
    baseline = root / 'inputs/zfc240_old.tm'
    assert digest(baseline) == OLD_SHA
    old, start = read_table(baseline)
    assert len(old) == 480 and start == 95
    phi = lambda q: 80 if q == 169 else q
    new = {(q, b): (w, d, phi(z))
           for (q, b), (w, d, z) in old.items() if q != 169}
    new[80, 0] = (0, 'L', 106)
    new[91, 1] = (1, 'L', 167)
    order = [95] + sorted({q for q, _ in new} - {95})
    renaming = {q: n for n, q in enumerate(order)} | {254: 239}
    canonical = {(renaming[q], b): (w, d, renaming[z])
                 for (q, b), (w, d, z) in new.items()}
    return old, new, canonical, renaming


def verify(root=ROOT):
    old, new, canonical, renaming = construct(root)
    expected = serialize(new, 95)
    canon_bytes = serialize(canonical, 0)
    assert (root / 'machines/zfc239_old.tm').read_bytes() == expected
    assert (root / 'machines/zfc239.tm').read_bytes() == canon_bytes
    assert hashlib.sha256(expected).hexdigest() == NEW_SHA
    assert hashlib.sha256(canon_bytes).hexdigest() == CANON_SHA
    assert len(new) == len(canonical) == 478
    assert {q for q, _ in canonical} == set(range(239))
    assert {z for _, _, z in canonical.values()} - set(range(239)) == {239}
    assert renaming[95] == 0 and renaming[96] == 84 and renaming[254] == 239
    saved = json.loads((root / 'machines/renumbering.json').read_text())
    assert {int(k): v for k, v in saved['old_to_canonical'].items()} == renaming
    assert {int(k): v for k, v in saved['canonical_to_old'].items()} == {
        v: k for k, v in renaming.items()}
    sites_path = root / 'machines/sites_logical.json'
    assert digest(sites_path) == SITES_SHA
    sites = json.loads(sites_path.read_text())
    leaves = {p for p, op, arg in sites}
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    assert len(leaves) == len(sites) == 6455
    assert not leaves & prefixes
    assert all(p + b in leaves | prefixes for p in prefixes for b in '01')
    assert max(map(len, leaves)) == 51
    changed = [[q, b, list(old[q, b]), list(new[q, b])]
               for q, b in sorted(new) if new[q, b] != old[q, b]]
    assert [x[:2] for x in changed] == [[80, 0], [91, 1], [147, 0]]
    return {
        'status': 'PASS_EXACT_CONSTRUCTION_AND_RENUMBERING',
        'working_states': 239, 'rows': 478,
        'alphabet': [0, 1], 'moves': ['L', 'R'],
        'tape': 'two-way infinite, initially all zero',
        'start': 0, 'head': 0, 'halt': 239, 'dispatcher': 84,
        'deleted_old_state': 169, 'shared_old_state': 80,
        'changed_retained_rows': changed,
        'old_label_sha256': NEW_SHA, 'canonical_sha256': CANON_SHA,
        'baseline_sha256': OLD_SHA, 'sites_sha256': SITES_SHA,
        'source_leaves': 6455, 'maximum_depth': 51,
        'guarded_cases': sum(2 if op == 'CD' else 1 for p, op, arg in sites),
        'scope': 'Exact finite artifact construction; not a consistency decision.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Assertions must be enabled. Remove -O and PYTHONOPTIMIZE.')
    result = verify(args.root.resolve())
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
