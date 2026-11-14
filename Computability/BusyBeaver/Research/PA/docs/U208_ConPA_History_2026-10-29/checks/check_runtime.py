#!/usr/bin/env python3
"""Fresh whole-tape unary/list induction for the literal U208 table.

The inference engine is retained byte-for-byte from the Plain U209 packet.
This adapter changes input paths and records identities, not its proof rules.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'checks/runtime'))
from check_local import require, read, census
import source_language as source

PINS = {
    'symbolic_runtime.py':
        '61b9c66272e8fd149829177cc384013814aea3c6b3b6b6f48e462d3913ea2022',
    'independent_runtime.py':
        'd490397a2b31be4f7f62461a3d9bcd88faf9093de904e43eea1b865561e7b7ee',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(output, compare_saved=True):
    require(__debug__ and not sys.flags.optimize,
            'Full runtime induction requires assertions; do not use -O.')
    for name, expected in PINS.items():
        require(sha(ROOT / 'checks/runtime' / name) == expected,
                'Changed induction-engine module: ' + name)
    import symbolic_runtime as engine
    table = read(ROOT / 'machine/u208.native.tm', 208)
    states = census(table, 208, 254)
    sites = json.loads((ROOT / 'machine/sites.json').read_text())
    require((ROOT / 'machine/sites.json').read_bytes() ==
            (ROOT / 'inputs/u209.sites.json').read_bytes(), 'Source changed')
    tree = source.tree(sites)
    require(source.graph_arithmetic(sites)[0] == source.graph_intervals(sites),
            'Independent source resolvers disagree')
    mapping = {int(k): int(v) for k, v in
               json.loads((ROOT / 'inputs/legacy_mapping.json').read_text()).items()}
    for state in states | {254}:
        mapping.setdefault(state, state + 1000)
    require(len({mapping[q] for q in states | {254}}) == 209,
            'Runtime-label conjugacy is not injective')
    require(mapping[84] == 96 and mapping[254] == 254,
            'Dispatcher or halt conjugacy changed')
    literal = {(mapping[q], b): (w, d, mapping[z])
               for (q, b), (w, d, z) in table.items()}
    began = time.monotonic()
    lemmas, blocks = engine.prove_blocks(literal)
    cases, used = [], set()
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            result = engine.case(literal, lemmas, site, positive)
            used.update(result['rows'])
            result['rows'] = sorted(result['rows'])
            result.pop('trace')
            cases.append(dict(site_index=index, positive=positive, **result))
        if (index + 1) % 1000 == 0:
            print(f'Rederived {len(cases)} arbitrary-value contracts', flush=True)
    for block in blocks:
        for event in block['trace']:
            used.add(tuple(event[1][:2]))
    require(len(sites) == 3909 and len(cases) == 5084, 'Contract census')
    require(used == set(literal), 'Incomplete literal-row coverage')
    require(all(len(c['duration']) == 13 and c['duration'][0] > 0 and
                all(n >= 0 for n in c['duration']) for c in cases),
            'Nonpositive or malformed affine duration')
    cases = json.loads(json.dumps(cases))
    if compare_saved:
        with gzip.open(ROOT / 'evidence/runtime_cases.json.gz', 'rt') as stream:
            require(cases == json.load(stream), 'Fresh case records changed')
    output.mkdir(parents=True, exist_ok=True)
    result = {
        'status': 'FULL_U208_UNIVERSAL_RUNTIME_PASS',
        'working_states': 208, 'literal_rows': 416,
        'cases': len(cases), 'row_coverage': len(used),
        'symbolic_inferences': sum(c['symbolic_steps'] for c in cases),
        'minimum_duration_constant': min(c['duration'][0] for c in cases),
        'all_duration_coefficients_nonnegative': True,
        'source_metrics': source.metrics(tree),
        'arbitrary_primary_registers': 9, 'arbitrary_natural_gap': True,
        'arbitrary_nonempty_finite_spares': True, 'header_base': engine.HEADER_BASE,
        'blocks': blocks, 'case_rows_use_legacy_labels': True,
        'legacy_to_native': {mapping[q]: q for q in states | {254}},
        'sha256': {name: sha(ROOT / 'machine' / name)
                   for name in ['u208.native.tm', 'u208.tm', 'sites.json']},
        'engine_sha256': PINS,
        'saved_cases_match_fresh': compare_saved,
        'seconds': time.monotonic() - began,
        'scope': 'Executable unary/list induction over arbitrary natural values '
                 'and whole-tape endpoints; not a proof-assistant kernel certificate.',
    }
    (output / 'runtime.json').write_text(json.dumps(result, indent=2) + '\n')
    with gzip.GzipFile(filename=str(output / 'runtime_cases.json.gz'),
                       mode='wb', mtime=0) as stream:
        stream.write((json.dumps(cases, separators=(',', ':')) + '\n').encode())
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'build/runtime')
    parser.add_argument('--fresh-only', action='store_true',
                        help='Derive new records without comparing a saved receipt.')
    args = parser.parse_args()
    answer = check(args.output, not args.fresh_only)
    print(json.dumps({k: v for k, v in answer.items()
                      if k not in ('blocks', 'legacy_to_native')}, indent=2))
