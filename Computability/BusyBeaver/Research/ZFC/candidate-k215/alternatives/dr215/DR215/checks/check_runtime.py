#!/usr/bin/env python3
"""Reprove every DR215 whole-tape primitive contract, or audit its receipt.

The proof engine uses literal rows, unary-length induction, and finite-list
induction. It is ordinary mathematical verification, not a kernel theorem.
"""
from pathlib import Path
import gzip
import hashlib
import json
import time

import symbolic_runtime as sy
import independent_runtime as ir


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def inputs(root):
    table = ir.table(root / 'machine/dr215.native.tm')
    source = json.loads((root / 'source/dr215.sites.json').read_text())
    mapping = {int(k): int(v) for k, v in json.loads(
        (root / 'inputs/native-to-legacy.json').read_text()).items()}
    for q in sorted({q for q, b in table} | {z for w, d, z in table.values()}):
        if q not in mapping:
            mapping[q] = max(mapping.values()) + 1
    assert len(set(mapping.values())) == len(mapping)
    assert mapping[84] == 96 and mapping[254] == 254
    mapped = {(mapping[q], b): (w, d, mapping[z])
              for (q, b), (w, d, z) in table.items()}
    return mapped, source


def audit(root, work):
    """Audit finite metadata; this does not rederive the symbolic proofs."""
    table, source = inputs(root)
    report = json.loads((root / 'evidence/runtime.json').read_text())
    with gzip.open(root / 'evidence/runtime_cases.json.gz', 'rt') as f:
        cases = json.load(f)
    assert report['table_sha256'] == sha(root / 'machine/dr215.native.tm')
    assert report['source_sha256'] == sha(root / 'source/dr215.sites.json')
    assert report['checker_sha256'] == sha(root / 'checks/symbolic_runtime.py')
    assert report['helper_sha256'] == sha(root / 'checks/independent_runtime.py')
    assert report['legacy_map_sha256'] == sha(root / 'inputs/native-to-legacy.json')
    assert report['status'] == 'PASS' and not report['failures']
    expected = [(i, p) for i, site in enumerate(source)
                for p in ([False, True] if site[1] == 'CD' else [False])]
    assert [(c['site_index'], c['positive']) for c in cases] == expected
    assert len(cases) == report['cases'] == report['expected_cases'] == 6151
    rows = {tuple(r) for c in cases for r in c['rows']}
    assert rows == set(table)
    assert len(rows) == report['rows_covered'] == 430
    assert sum(c['symbolic_steps'] for c in cases) == report['symbolic_rules'] == 1618678
    for c in cases:
        assert len(c['duration']) == len(c['motion']) == 13
        assert c['duration'][0] > 0 and all(x >= 0 for x in c['duration'])
        assert sum(c['kinds'].values()) == c['symbolic_steps']
        assert set(c['kinds']) <= {'literal', 'unary', 'list'}
    assert min(c['duration'][0] for c in cases) == report['min_duration'] == 5
    assert report['append'] == 0 and report['states'] == 215
    assert report['sourceleaves'] == 4732
    _, blocks = sy.prove_blocks(table)
    assert json.loads(json.dumps(blocks)) == report['blocks']
    result = {'status': 'SAVED_CERTIFICATE_AUDIT_PASS', 'cases': len(cases),
              'rows': len(rows), 'four_block_schemas_reproved': True,
              'scope': 'Case metadata audited; use --runtime to rederive all cases.'}
    (work / 'runtime_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def run(root, work):
    paths = [root / p for p in ('machine/dr215.native.tm', 'source/dr215.sites.json',
             'checks/symbolic_runtime.py', 'checks/independent_runtime.py',
             'inputs/native-to-legacy.json')]
    hashes_before = {str(p.relative_to(root)): sha(p) for p in paths}
    table, source = inputs(root)
    started = time.monotonic()
    lemmas, blocks = sy.prove_blocks(table)
    cases, rows = [], set()
    for i, site in enumerate(source):
        for positive in ([False, True] if site[1] == 'CD' else [False]):
            ans = sy.case(table, lemmas, site, positive, append=0)
            rows.update(ans['rows'])
            ans['rows'] = sorted(ans['rows'])
            ans.pop('trace')
            cases.append({'site_index': i, 'positive': positive, **ans})
        if i % 500 == 0:
            print(f'Runtime: {len(cases)} cases, source ordinal {i}', flush=True)
    with gzip.open(root / 'evidence/runtime_cases.json.gz', 'rt') as f:
        saved = json.load(f)
    assert json.loads(json.dumps(cases)) == saved, 'Fresh case receipts differ'
    saved_report = json.loads((root / 'evidence/runtime.json').read_text())
    assert json.loads(json.dumps(blocks)) == saved_report['blocks']
    assert rows == set(table)
    assert {str(p.relative_to(root)): sha(p) for p in paths} == hashes_before
    result = {'status': 'FRESH_UNIVERSAL_RUNTIME_PASS', 'cases': len(cases),
              'rows_covered': len(rows),
              'symbolic_rules': sum(c['symbolic_steps'] for c in cases),
              'min_duration': min(c['duration'][0] for c in cases),
              'every_case_equals_saved': True, 'append': 0,
              'table_sha256': sha(root / 'machine/dr215.native.tm'),
              'source_sha256': sha(root / 'source/dr215.sites.json'),
              'input_hashes_before_and_after': hashes_before,
              'inputs_unchanged_during_run': True,
              'seconds': time.monotonic() - started}
    (work / 'runtime_fresh.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
