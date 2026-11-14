#!/usr/bin/env python3
"""Reconstruct all 5,084 universal unary/list-inductive runtime contracts.

The induction engine and source-language utilities are retained byte-for-byte
from the exact direct-transfer U213 parent. This wrapper binds U212 and checks
the complete stored result, rather than trusting a saved success field.
"""
import argparse
import gzip
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code/vendor'))
import symbolic_runtime as s
import source_language as sl
from build import parse, validate, need, digest, NATIVE_SHA, SOURCE_SHA

def run(output, compare_saved=True):
    need(__debug__ and not sys.flags.optimize, 'Python assertions must remain enabled')
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    table_raw = (ROOT / 'machine/u212.native.tm').read_bytes()
    source_raw = (ROOT / 'machine/sites.json').read_bytes()
    need(digest(table_raw) == NATIVE_SHA and digest(source_raw) == SOURCE_SHA,
         'runtime input identity')
    table = parse(table_raw)
    states = validate(table, 212, 254)
    sites = json.loads(source_raw)
    tree = sl.tree(sites)
    need(sl.metrics(tree) == {'dag_nodes': 197, 'leaf_occurrences': 3909,
                             'maximum_depth': 42, 'maximum_zero_run': 6}, 'source metrics')
    graph, count = sl.graph_arithmetic(sites)
    need(count == 5084 and graph == sl.graph_intervals(sites), 'guarded source graph')
    mapping = {int(k): int(v) for k, v in json.loads(
        (ROOT / 'inputs/legacy_mapping.json').read_text()).items()}
    for q in states | {254}:
        mapping.setdefault(q, q + 1000)
    need(len({mapping[q] for q in states | {254}}) == 213, 'legacy map bijection')
    renamed = {(mapping[q], b): (w, d, mapping[target])
               for (q, b), (w, d, target) in table.items()}
    need(s.HEADER_BASE == 56 and s.r.PHY == (6, 2, 0, 4, 3, 7, 8, 5, 1),
         'runtime frame convention')
    start = time.monotonic()
    lemmas, blocks = s.prove_blocks(renamed)
    cases, used = [], set()
    for i, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            answer = s.case(renamed, lemmas, site, positive)
            used.update(answer['rows'])
            answer['rows'] = sorted(answer['rows'])
            answer.pop('trace')
            cases.append({'site_index': i, 'positive': positive, **answer})
        if (i + 1) % 1000 == 0:
            print(f'Proved {len(cases)} guarded contracts', flush=True)
    for block in blocks:
        for event in block['trace']:
            used.add(tuple(event[1][:2]))
    need(len(cases) == 5084 and used == set(renamed), 'complete case/row coverage')
    need(all(len(c['duration']) == 13 and c['duration'][0] > 0
             and all(n >= 0 for n in c['duration']) for c in cases),
         'positive simulation duration')
    cases = json.loads(json.dumps(cases))
    if compare_saved:
        with gzip.open(ROOT / 'evidence/runtime_cases.json.gz', 'rt') as stream:
            need(cases == json.load(stream), 'fresh runtime derivations differ')
    result = {'status': 'UNIVERSAL_MATHEMATICAL_PASS', 'states': 212, 'rows': 424,
              'cases': len(cases), 'row_coverage': len(used),
              'source_primitives': len(sites), 'header_base': 56,
              'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
              'minimum_duration_constant': min(c['duration'][0] for c in cases),
              'table_sha256': digest(table_raw), 'source_sha256': digest(source_raw),
              'checker_sha256': digest(Path(s.__file__).read_bytes()),
              'blocks': blocks, 'seconds': time.monotonic() - start,
              'scope': 'All natural registers, gap and nonempty finite spare list; '
                       'unary/list induction in Python, not a proof-assistant kernel.'}
    if compare_saved:
        saved = json.loads((ROOT / 'evidence/runtime.json').read_text())
        for key in ['states', 'rows', 'cases', 'row_coverage', 'symbolic_steps',
                    'minimum_duration_constant', 'header_base', 'table_sha256',
                    'source_sha256', 'checker_sha256']:
            need(result[key] == saved[key], 'runtime receipt mismatch: ' + key)
    (output / 'runtime.json').write_text(json.dumps(result, indent=2) + '\n')
    with gzip.GzipFile(filename=str(output / 'runtime_cases.json.gz'), mode='wb',
                       mtime=0) as stream:
        stream.write((json.dumps(cases, separators=(',', ':')) + '\n').encode())
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.output)
    print(json.dumps({k: v for k, v in result.items() if k != 'blocks'}, indent=2))
