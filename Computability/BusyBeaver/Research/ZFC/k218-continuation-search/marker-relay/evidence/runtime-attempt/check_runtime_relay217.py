#!/usr/bin/env python3
"""Replay every unbounded primitive-interface proof for the exact relay217 table.

The native table and source bytes are pinned below. The unchanged symbolic
runtime implementation and its helper are supplied by the bundled K221 parent.
The finite loops bound proof construction only: the proved register values,
extra blank gap, first spare value, and remaining finite spare list are arbitrary.

This is executable mathematical evidence, not proof-assistant kernel checking.
Source equivalence and blank startup are separate certificates in the packet.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

EXPECTED_TABLE = '73deb3f0e1a6159646dcb153ad5082eddb6656f3cabbbba40e86bbef971b9111'
EXPECTED_SITES = 'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9'
EXPECTED_STATES = 217
EXPECTED_CASES = 6167
DEPENDENCIES = {
    'portable/build221.py': '3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
    'portable/source_language.py': '4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
    'portable/runtime/vendor/symbolic_runtime.py': 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
    'portable/runtime/vendor/independent_runtime.py': '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
    'portable/runtime/reference_results/legacy_mapping.json': '26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True,
                        help='Extracted K221_Construction_2026-10-20 directory')
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True,
                        help='Output directory for runtime.json and cases.json')
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize,
            'Assertions must be enabled; do not use Python -O or PYTHONOPTIMIZE.')
    base = args.baseline.resolve()
    checked_dependencies = {}
    for name, expected in DEPENDENCIES.items():
        actual = sha((base / name).read_bytes())
        require(actual == expected, 'Dependency hash mismatch: ' + name)
        checked_dependencies[name] = actual

    # No source code is changed. Import only the pinned parent implementations.
    sys.path.insert(0, str(base / 'portable'))
    import build221 as builder
    import source_language as source
    sys.path.insert(0, str(base / 'portable/runtime/vendor'))
    import symbolic_runtime as runtime

    table_bytes = args.table.read_bytes()
    sites_bytes = args.sites.read_bytes()
    require(sha(table_bytes) == EXPECTED_TABLE, 'Unexpected relay217 table bytes')
    require(sha(sites_bytes) == EXPECTED_SITES, 'Unexpected relay217 source bytes')
    table = builder.read_table(table_bytes)
    sites = json.loads(sites_bytes)
    tree = source.tree(sites)
    require(source.sites(tree) == sites, 'Source ordinal order changed')
    metrics = source.metrics(tree)
    require(metrics == {'dag_nodes': 205, 'leaf_occurrences': 4744,
                        'maximum_depth': 38, 'maximum_zero_run': 6},
            'Source metrics changed')
    working = {q for q, bit in table}
    require(len(working) == EXPECTED_STATES and len(table) == 434,
            'Expected 217 working states and 434 rows')
    require(0 in working and 84 in working and 254 not in working,
            'Native start/dispatch/halt labels changed')
    require(set(table) == {(q, bit) for q in working for bit in (0, 1)},
            'The table is not total on its working states')
    require({target for w, d, target in table.values()} - working == {254},
            'Unexpected halting target')

    mapping_file = base / 'portable/runtime/reference_results/legacy_mapping.json'
    mapping = {int(q): int(z) for q, z in json.loads(mapping_file.read_text()).items()}
    for q in working | {254}:
        if q not in mapping:
            mapping[q] = q + 1000
    require(len(set(mapping.values())) == len(mapping), 'Legacy map is not injective')
    require(mapping[84] == 96 and mapping[254] == 254,
            'Legacy dispatch/halt convention changed')
    legacy = {(mapping[q], bit): (w, d, mapping[z])
              for (q, bit), (w, d, z) in table.items()}
    require(len(legacy) == len(table), 'Legacy relabelling is not bijective')
    expected_cases = sum(2 if op == 'CD' else 1 for pc, op, arg in sites)
    require(expected_cases == EXPECTED_CASES, 'Guarded case census changed')
    args.output.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    lemmas, blocks = runtime.prove_blocks(legacy)
    print('Proved four exact-table block schemas; checking 6167 unbounded cases', flush=True)

    cases = []
    used_rows = set()
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            try:
                answer = runtime.case(legacy, lemmas, site, positive)
            except Exception as error:
                failure = {'status': 'NOT_PROVED', 'index': index, 'site': site,
                           'positive': positive, 'reason': str(error),
                           'prior_cases': len(cases),
                           'seconds': time.monotonic() - started}
                dump(args.output / 'runtime.json', failure)
                print(json.dumps(failure), flush=True)
                return 1
            used_rows.update(answer.pop('rows'))
            answer.pop('trace')
            cases.append({'index': index, 'positive': positive, **answer})
            if len(cases) % 500 == 0:
                print('PROVED', len(cases), 'seconds',
                      round(time.monotonic() - started, 1), flush=True)

    require(len(cases) == EXPECTED_CASES, 'Incomplete proof census')
    inverse = {value: key for key, value in mapping.items()}
    native_rows = sorted((inverse[q], bit) for q, bit in used_rows)
    receipt = {
        'status': 'ALL_PRIMITIVE_INTERFACES_PROVED',
        'working_states': EXPECTED_STATES,
        'transition_rows': 434,
        'source_metrics': metrics,
        'cases': len(cases),
        'expected_cases': EXPECTED_CASES,
        'symbolic_steps': sum(case['symbolic_steps'] for case in cases),
        'minimum_actual_steps': min(case['duration'][0] for case in cases),
        'seconds': time.monotonic() - started,
        'table_sha256': EXPECTED_TABLE,
        'sites_sha256': EXPECTED_SITES,
        'driver_sha256': sha(Path(__file__).read_bytes()),
        'dependencies': checked_dependencies,
        'proof_scope': (
            'Every source leaf and both decrement guards; independent arbitrary natural '
            'primary register values, arbitrary natural extra gap, arbitrary first spare '
            'value and arbitrary finite remaining spare list; complete tape and positive '
            'finite duration. Mathematical symbolic checking, not proof-assistant kernel '
            'verification.'),
        'bounds_scope': '4000 bounds proof construction, not actual runtime or values.',
        'external_certificates': ['Ordinal source-word and complete control-flow equivalence', 'Blank startup'],
        'block_schemas': blocks,
        'directly_used_native_rows': native_rows,
        'python_version': sys.version,
        'debug_enabled': __debug__,
    }
    dump(args.output / 'cases.json', cases)
    dump(args.output / 'runtime.json', receipt)
    print(json.dumps({key: value for key, value in receipt.items()
                      if key not in ('block_schemas', 'directly_used_native_rows')}, indent=2),
          flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
