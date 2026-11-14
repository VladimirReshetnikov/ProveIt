#!/usr/bin/env python3
"""Fresh universal primitive contracts on the literal U208 table.

This invokes the unchanged inherited unary/list induction engine. It is
executable mathematical evidence, not a proof-assistant kernel certificate.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import sys
import time
from check_local import need, read_table

ROOT = Path(__file__).resolve().parents[1]
PINS = {'symbolic_runtime.py':
        '61b9c66272e8fd149829177cc384013814aea3c6b3b6b6f48e462d3913ea2022',
        'independent_runtime.py':
        'd490397a2b31be4f7f62461a3d9bcd88faf9093de904e43eea1b865561e7b7ee'}


def check(output):
    need(__debug__ and not sys.flags.optimize, 'Universal replay requires assertions')
    for name, digest in PINS.items():
        need(hashlib.sha256((ROOT / 'code' / name).read_bytes()).hexdigest() == digest,
             'Inherited induction engine changed')
    import symbolic_runtime as engine
    table = read_table(ROOT / 'machine/u208.native.tm')
    states = {q for q, _ in table}
    need(len(states) == 208 and len(table) == 416, 'Candidate census')
    sites = json.loads((ROOT / 'machine/sites.json').read_text())
    mapping = {int(k): int(v) for k, v in
               json.loads((ROOT / 'machine_parent/legacy_mapping.json').read_text()).items()}
    for q in states | {254}:
        mapping.setdefault(q, q + 1000)
    need(len({mapping[q] for q in states | {254}}) == 209, 'Runtime relabeling')
    inverse = {mapping[q]: q for q in states | {254}}
    literal = {(mapping[q], b): (w, d, mapping[z])
               for (q, b), (w, d, z) in table.items()}
    need(mapping[84] == 96 and mapping[254] == 254 and engine.HEADER_BASE == 56,
         'Dispatcher/frame convention')
    started = time.monotonic()
    lemmas, blocks = engine.prove_blocks(literal)
    cases, used = [], set()
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            result = engine.case(literal, lemmas, site, positive)
            used.update(result['rows'])
            result['rows'] = sorted((inverse[q], b) for q, b in result['rows'])
            result.pop('trace')
            cases.append({'site_index': index, 'positive': positive, **result})
        if (index + 1) % 1000 == 0:
            print(f'Rederived {len(cases)} arbitrary-value contracts', flush=True)
    for block in blocks:
        for event in block['trace']:
            used.add(tuple(event[1][:2]))
    need(len(sites) == 3909 and len(cases) == 5084 and used == set(literal),
         'Universal case and row coverage')
    need(all(len(c['duration']) == 13 and c['duration'][0] > 0 and
             all(n >= 0 for n in c['duration']) for c in cases),
         'Positive affine durations')
    inferences = sum(c['symbolic_steps'] for c in cases)
    need(inferences == 1251865, 'Inference census changed')
    cases = json.loads(json.dumps(cases))
    with gzip.open(ROOT / 'evidence/runtime_cases.json.gz', 'rt') as stream:
        need(cases == json.load(stream), 'Fresh cases differ from first independent run')
    result = {'status': 'FULL_UNIVERSAL_RUNTIME_PASS', 'working_states': 208,
              'rows': 416, 'source_primitives': 3909, 'cases': len(cases),
              'row_coverage': len(used), 'symbolic_inferences': inferences,
              'minimum_duration_constant': min(c['duration'][0] for c in cases),
              'arbitrary_primary_registers': 9, 'arbitrary_natural_gap': True,
              'arbitrary_nonempty_finite_spare_list': True,
              'fresh_cases_equal_frozen': True, 'engine_sha256': PINS,
              'seconds': time.monotonic() - started, 'blocks': blocks}
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    print('FULL_UNIVERSAL_RUNTIME_PASS: 5084 contracts, all 416 rows, 1251865 inferences')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    check(parser.parse_args().output)
