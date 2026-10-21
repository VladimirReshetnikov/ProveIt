#!/usr/bin/env python3
"""Offline verification of the distributed research packet.

Default: exact finite proofs and stored-certificate coverage.
--full-runtime: additionally rederive all 6,167 unbounded primitive contracts.
No result of this program asserts a completed 217-state consistency machine.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
DATA = ROOT / 'data'
EVIDENCE = ROOT / 'evidence'
PIN = '704b87442afbd571833a628cd558f1d207fd8b2f'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            key = int(q), int(b)
            assert key not in rows and b in ('0', '1') and w in ('0', '1')
            assert d in ('L', 'R')
            rows[key] = int(w), 1 if d == 'R' else -1, int(z)
    states = {q for q, b in rows}
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert {z for w, d, z in rows.values()} - states == {254}
    return rows, states


def replay(table, start, count):
    q, h, ones = start, 0, set()
    for _ in range(count):
        assert q != 254
        w, d, q = table[q, int(h in ones)]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    return q, h, ones


def is_ray(table, q, h, ones):
    if h in ones:
        return False
    w, d, z = table[q, 0]
    return z == q and (all(x < h for x in ones) if d == 1 else all(x > h for x in ones))


def core_rays(table, states):
    total, census, longest = 0, {}, {}
    for start in sorted(states):
        q, h, ones = start, 0, set()
        for tick in range(1000):
            if is_ray(table, q, h, ones):
                total += tick
                census[q] = census.get(q, 0) + 1
                longest[q] = max(longest.get(q, 0), tick)
                break
            w, d, q = table[q, int(h in ones)]
            if w:
                ones.add(h)
            else:
                ones.discard(h)
            h += d
        else:
            raise AssertionError(('no exact core ray', start))
    assert total == 1787 and census == {35: 198, 1: 3, 75: 9, 6: 7}
    assert longest == {35: 85, 1: 2, 75: 8, 6: 35}
    return {'initial_states': len(states), 'finite_steps': total,
            'sink_counts': census, 'maximum_prefix_by_sink': longest}


def mutant_rays(base, states):
    changes = [tuple(map(int, line.split())) for line in
               (DATA / 'one-row-survivors.txt').read_text().splitlines()]
    assert len(changes) == len(set(changes)) == 252
    expected = {(change, start) for change in changes for start in states}
    seen, total, longest, support = set(), 0, 0, 0
    digest = hashlib.sha256()
    with gzip.open(DATA / 'one-row-rays.jsonl.gz', 'rb') as stream:
        for raw in stream:
            digest.update(raw)
            a, b, w, d, z, start, status, n, q, h, cells = json.loads(raw)
            change = (a, b, w, d, z)
            key = change, start
            assert key in expected and key not in seen and status == 5
            table = dict(base)
            table[a, b] = w, d, z
            state, head, ones = replay(table, start, n)
            assert (state, head, ones) == (q, h, set(cells))
            assert is_ray(table, q, h, ones)
            seen.add(key)
            total += n
            longest = max(longest, n)
            support = max(support, len(ones))
    assert seen == expected and len(seen) == 54684
    assert (total, longest, support) == (459639, 93, 3)
    assert digest.hexdigest() == 'e0817e08333b7b7c744c9e9ef3ca272147d823a6f0a3408d18266b41727302ad'
    return {'tables': 252, 'starts_per_table': 217, 'witnesses': len(seen),
            'finite_steps': total, 'maximum_prefix': longest, 'maximum_support': support}


def runtime_coverage(base):
    rec = json.loads((EVIDENCE / 'core217-runtime.json').read_text())
    cases = json.loads((EVIDENCE / 'core217-cases.json').read_text())
    sites = json.loads((DATA / 'sites218.json').read_text())
    expected = [(i, positive) for i, (_, op, arg) in enumerate(sites)
                for positive in ((False, True) if op == 'CD' else (False,))]
    assert [(c['index'], c['positive']) for c in cases] == expected
    assert len(cases) == rec['cases'] == rec['expected_cases'] == 6167
    assert rec['status'] == 'ALL_PRIMITIVE_INTERFACES_PROVED'
    assert sum(c['symbolic_steps'] for c in cases) == rec['symbolic_steps'] == 1515310
    assert min(c['duration'][0] for c in cases) == rec['minimum_actual_steps'] == 12
    assert rec['directly_used_native_rows'] == [list(k) for k in sorted(base)]
    assert rec['table_sha256'] == sha(DATA / 'core217.native.tm')
    assert rec['sites_sha256'] == sha(DATA / 'sites218.json')
    assert rec['driver_sha256'] == sha(ROOT / 'code/check_core217_runtime.py')
    for name, digest in rec['dependencies'].items():
        assert sha(ROOT / 'upstream' / name) == digest
    for c in cases:
        assert 0 < c['symbolic_steps'] < 4000
        assert len(c['duration']) == len(c['motion']) == 13
        assert all(type(n) is int and n >= 0 for n in c['duration'])
        assert c['duration'][0] > 0
        assert sum(c['kinds'].values()) == c['symbolic_steps']
    return {'cases': 6167, 'symbolic_rules': 1515310, 'rows': len(base),
            'minimum_positive_duration_constant': 12,
            'scope': 'Stored coverage/provenance check; use --full-runtime for fresh induction.'}


def command(args):
    subprocess.run([sys.executable, *map(str, args)], check=True, cwd=ROOT)


def main():
    assert __debug__ and not sys.flags.optimize, 'Do not use python -O.'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full-runtime', action='store_true')
    ap.add_argument('--skip-manifest', action='store_true', help='For authoring only.')
    a = ap.parse_args()
    began = time.monotonic()
    output = ROOT / 'reproduced'
    output.mkdir(exist_ok=True)
    results = {'upstream_commit': PIN, 'completed_217_state_consistency_machine': False}
    if not a.skip_manifest:
        manifest = json.loads((ROOT / 'manifest.json').read_text())
        for item in manifest['files']:
            path = ROOT / item['path']
            assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], item['path']
        results['manifest_files_checked'] = len(manifest['files'])
    base, states = read_table(DATA / 'core217.native.tm')
    old, oldstates = read_table(DATA / 'k218.native.tm')
    short, shortstates = read_table(DATA / 'delete50.native.tm')
    assert (len(states), len(base)) == (217, 434)
    assert (len(oldstates), len(old)) == (218, 436)
    assert (len(shortstates), len(short)) == (217, 434)
    results['exact_core_rays'] = core_rays(base, states)
    results['one_row_rays'] = mutant_rays(base, states)
    results['stored_runtime_coverage'] = runtime_coverage(base)
    command([ROOT / 'code/replay_seed3.py', '--check-only', DATA / 'seed3-proof.json',
             '--output', output / 'seed3'])
    command([ROOT / 'code/verify_action_variants.py', DATA / 'k218.native.tm',
             DATA / 'action-variants.txt', '--output', output / 'action-variants.json'])
    command([ROOT / 'code/verify_scanner_route.py', '--accepted', DATA / 'k218.native.tm',
             '--short', DATA / 'delete50.native.tm', '--sites', DATA / 'sites218.json',
             '--output', output / 'scanner-route.json'])
    if a.full_runtime:
        command([ROOT / 'code/check_core217_runtime.py', '--baseline', ROOT / 'upstream',
                 '--table', DATA / 'core217.native.tm', '--sites', DATA / 'sites218.json',
                 '--output', output / 'core-runtime'])
        fresh = json.loads((output / 'core-runtime/runtime.json').read_text())
        assert fresh['status'] == 'ALL_PRIMITIVE_INTERFACES_PROVED'
        assert fresh['symbolic_steps'] == 1515310
        assert sha(output / 'core-runtime/cases.json') == sha(EVIDENCE / 'core217-cases.json')
        results['fresh_unbounded_runtime'] = 'PASS; exact cases.json bytes reproduced'
    results['status'] = 'RESEARCH_EVIDENCE_VERIFIED'
    results['seconds'] = time.monotonic() - began
    (output / 'verification.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
