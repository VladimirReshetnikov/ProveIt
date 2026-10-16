#!/usr/bin/env python3
"""Read-only independent checker for the frozen modified-program certificates.

Does not import basis_search, the grammar generator, or the binary backend.
The theorem checked is RM operation bisimulation of each displayed pair of
DAGs.  Table shape/hash checks do not prove binary compilation correctness.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from verify_rm_certificate import Machine


def read_dag(path):
    data = json.loads(path.read_text())
    assert data['root'] == 0
    return {int(n): tuple(es) for n, es in data['nodes'].items()}


def check(directory):
    oldrows = read_dag(directory / 'reference.dag.json')
    newrows = read_dag(directory / 'candidate.dag.json')
    old, new = Machine(oldrows), Machine(newrows)
    cert = json.loads((directory / 'rm_certificate.json').read_text())
    records = cert['pairs']
    assert cert['initial'] == 0 and cert['branch_order'] == 'EDecnz: zero, positive'
    assert old.contract('') == (records[0]['old'], records[0]['instruction'])
    assert new.contract('') == (records[0]['new'], records[0]['instruction'])
    distinct = set()
    for record in records:
        a, b, label = record['old'], record['new'], record['instruction']
        assert (a, b) not in distinct
        distinct.add((a, b))
        assert old.lookup(a) == (a, label) and new.lookup(b) == (b, label)
        ls, rs = old.targets(a, label), new.targets(b, label)
        assert len(ls) == len(rs) == len(record['successors'])
        for i, l, r in zip(record['successors'], ls, rs, strict=True):
            assert type(i) is int and 0 <= i < len(records)
            target = records[i]
            assert l == (target['old'], target['instruction'])
            assert r == (target['new'], target['instruction'])
    reached, pending = set(), [0]
    while pending:
        i = pending.pop()
        if i not in reached:
            reached.add(i)
            pending.extend(records[i]['successors'])
    assert len(reached) == len(records)
    e = json.loads((directory / 'evidence.json').read_text())
    raw = (directory / 'candidate.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == e['numeric_sha256']
    n = e['cost']['working_states']
    table = {}
    for line in raw.decode().splitlines():
        if line.startswith('#'):
            assert line == '#! start 0'
            continue
        q, b, w, d, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        assert 0 <= q < n and b in (0, 1) and w in (0, 1)
        assert d in ('L', 'R') and 0 <= target <= n
        assert (q, b) not in table
        table[q, b] = (w, d, target)
    assert set(table) == {(q, b) for q in range(n) for b in (0, 1)}
    reached, pending = set(), [0]
    while pending:
        q = pending.pop()
        if q < n and q not in reached:
            reached.add(q)
            pending.extend(table[q, b][2] for b in (0, 1))
    assert reached == set(range(n))
    return {'basis': e['basis'], 'working_states': n, 'transitions': 2 * n,
            'related_pairs': len(records), 'reference_nodes': len(oldrows),
            'candidate_nodes': len(newrows),
            'operation_labels': dict(Counter(r['instruction'].split()[0] for r in records)),
            'numeric_sha256': e['numeric_sha256'], 'certificate_verified': True,
            'scope': 'modified reference RM versus its rebracketing',
            'binary_compiler_proved': False, 'ZFC_endpoint_proved': False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory', type=Path, required=True,
                    help='a directory containing L/, KSP/, and KBP/ outputs')
    args = ap.parse_args()
    assert __debug__, 'run without -O'
    results = {basis: check(args.directory / basis) for basis in ('L', 'KSP', 'KBP')}
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
