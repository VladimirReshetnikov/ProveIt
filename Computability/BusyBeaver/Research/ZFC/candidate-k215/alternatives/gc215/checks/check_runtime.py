#!/usr/bin/env python3
"""Audit saved metadata or rederive every arbitrary-natural primitive contract.

The inherited proof engine uses literal transitions, induction on unary lengths,
and induction on finite lists. This is not a proof-assistant kernel endpoint.
"""
from pathlib import Path
import gzip
import hashlib
import json
import time

import independent_runtime as ir
import symbolic_runtime as sy


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs(root):
    table = ir.table(root / 'machine/gc215.native.tm')
    source = json.loads((root / 'source/gc215.sites.json').read_text())
    mapping = {int(k): int(v) for k, v in json.loads(
        (root / 'reference/native-to-legacy.json').read_text()).items()}
    for q in sorted({q for q, b in table} | {z for w, d, z in table.values()}):
        if q not in mapping:
            mapping[q] = max(mapping.values()) + 1
    assert len(set(mapping.values())) == len(mapping)
    assert mapping[84] == 96 and mapping[254] == 254
    mapped = {(mapping[q], b): (w, d, mapping[z])
              for (q, b), (w, d, z) in table.items()}
    return mapped, source


def audit(root, work):
    table, source = inputs(root)
    report = json.loads((root / 'evidence/runtime.json').read_text())
    with gzip.open(root / 'evidence/runtime_cases.json.gz', 'rt') as stream:
        cases = json.load(stream)
    assert report['table_sha256'] == sha(root / 'machine/gc215.native.tm')
    assert report['source_sha256'] == sha(root / 'source/gc215.sites.json')
    assert report['status'] == 'PASS' and not report['failures']
    expected = [(i, p) for i, site in enumerate(source)
                for p in ([False, True] if site[1] == 'CD' else [False])]
    assert [(c['site_index'], c['positive']) for c in cases] == expected
    assert len(cases) == report['cases'] == report['expected_cases'] == 6151
    rows = {tuple(row) for c in cases for row in c['rows']}
    assert rows == set(table) and len(rows) == report['rows_covered'] == 430
    assert sum(c['symbolic_steps'] for c in cases) == report['symbolic_rules']
    for c in cases:
        assert len(c['duration']) == len(c['motion']) == 13
        assert c['duration'][0] > 0 and all(x >= 0 for x in c['duration'])
        assert sum(c['kinds'].values()) == c['symbolic_steps']
        assert set(c['kinds']) <= {'literal', 'unary', 'list'}
    assert min(c['duration'][0] for c in cases) == report['min_duration'] == 5
    assert report['append'] == 0 and report['states'] == 215
    assert report['source_leaves'] == len(source) == 4732
    _, blocks = sy.prove_blocks(table)
    assert json.loads(json.dumps(blocks)) == report['blocks']
    result = {'status': 'SAVED_METADATA_AUDIT_PASS', 'cases': len(cases),
              'rows': len(rows), 'block_schemas_reproved': True,
              'symbolic_rules': report['symbolic_rules'],
              'scope': 'Metadata audit; use --runtime to rederive every case.'}
    (work / 'runtime_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def run(root, work):
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
            print(f'Universal runtime: source {i}/{len(source)}, {len(cases)} cases', flush=True)
    with gzip.open(root / 'evidence/runtime_cases.json.gz', 'rt') as stream:
        saved = json.load(stream)
    assert json.loads(json.dumps(cases)) == saved, 'Fresh case receipts differ'
    saved_report = json.loads((root / 'evidence/runtime.json').read_text())
    assert json.loads(json.dumps(blocks)) == saved_report['blocks']
    assert rows == set(table)
    result = {'status': 'FRESH_UNIVERSAL_RUNTIME_PASS', 'cases': len(cases),
              'rows_covered': len(rows),
              'symbolic_rules': sum(c['symbolic_steps'] for c in cases),
              'minimum_duration_constant': min(c['duration'][0] for c in cases),
              'every_case_equals_saved': True,
              'table_sha256': sha(root / 'machine/gc215.native.tm'),
              'source_sha256': sha(root / 'source/gc215.sites.json'),
              'seconds': time.monotonic() - started}
    (work / 'runtime_fresh.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
