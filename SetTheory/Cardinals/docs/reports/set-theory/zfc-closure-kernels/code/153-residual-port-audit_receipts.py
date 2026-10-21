#!/usr/bin/env python3
"""Integrity, census and coverage audit of stored primitive-proof receipts.

This does not rederive every symbolic case. Use --full-runtime in reproduce.py
for a fresh unbounded runtime proof with the pinned checker.
"""
import argparse, hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
NAMES = ('weak218_rejected', 'zero_guard219', 'counter_salt223_interface')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, w, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in result
        result[key] = int(w), direction, int(target)
    return result

def audit(base221, name, runtime=None):
    folder = ROOT / 'machine' / name
    runtime = runtime or folder / 'runtime'
    receipt = json.loads((runtime / 'runtime.json').read_text())
    cases = json.loads((runtime / 'cases.json').read_text())
    source = json.loads((folder / 'sites.json').read_text())
    table = read_table(folder / 'machine.native.tm')
    manifest = json.loads((folder / 'manifest.json').read_text())
    states = {q for q, bit in table}
    assert 0 in states and 254 not in states
    assert len(table) == 2 * len(states) == manifest['transition_rows']
    assert all((q, b) in table for q in states for b in (0, 1))
    assert all(w in (0, 1) and d in ('L', 'R') and z in states | {254}
               for w, d, z in table.values())
    reached, queue = {0}, [0]
    for q in queue:
        for bit in (0, 1):
            z = table[q, bit][2]
            if z != 254 and z not in reached:
                reached.add(z)
                queue.append(z)
    assert reached == states, 'Native count includes unreachable control states'
    expected = [(i, positive) for i, (_, op, _) in enumerate(source)
                for positive in ((False, True) if op == 'CD' else (False,))]
    assert [(c['index'], c['positive']) for c in cases] == expected
    assert len(cases) == receipt['cases'] == receipt['expected_cases']
    assert receipt['status'] == 'ALL_PRIMITIVE_INTERFACES_PROVED'
    assert receipt['table_sha256'] == sha(folder / 'machine.native.tm') == manifest['table_sha256']
    assert receipt['sites_sha256'] == sha(folder / 'sites.json') == manifest['sites_sha256']
    assert receipt['driver_sha256'] == sha(ROOT / 'machine/check_interfaces.py')
    for path, digest in receipt['dependencies'].items():
        assert sha(base221 / path) == digest, ('Dependency mismatch', path)
    used_rows = set(map(tuple, receipt['used_native_rows']))
    assert used_rows <= set(table)
    expected_unused = {(103, 0)} if name == 'counter_salt223_interface' else set()
    assert set(table) - used_rows == expected_unused
    for c in cases:
        assert isinstance(c['positive'], bool)
        assert isinstance(c['symbolic_steps'], int) and c['symbolic_steps'] > 0
        assert sum(c['kinds'].values()) == c['symbolic_steps']
        duration = c['duration']
        assert len(duration) == 13 and all(type(x) is int and x >= 0 for x in duration)
        assert duration[0] > 0
        assert len(c['motion']) == 13 and all(type(x) is int for x in c['motion'])
    assert sum(c['symbolic_steps'] for c in cases) == receipt['symbolic_steps']
    return dict(name=name, status='STORED_INTEGRITY_AND_COVERAGE_PASS',
                states=len(states), transition_rows=len(table), guarded_cases=len(cases),
                symbolic_steps=receipt['symbolic_steps'],
                rows_used_by_primitive_proofs=len(used_rows),
                rows_not_used_by_primitive_proofs=sorted(set(table)-used_rows),
                minimum_duration_constant=min(c['duration'][0] for c in cases),
                runtime_receipt_sha256=sha(runtime/'runtime.json'),
                cases_sha256=sha(runtime/'cases.json'),
                scope='Exact hashes, syntax, reachability census, complete guard coverage, recorded row coverage, and duration format; not a fresh rederivation of the symbolic case proofs.')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline221', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    a = ap.parse_args()
    assert __debug__, 'Assertions must be enabled'
    result = [audit(a.baseline221.resolve(), name) for name in NAMES]
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
