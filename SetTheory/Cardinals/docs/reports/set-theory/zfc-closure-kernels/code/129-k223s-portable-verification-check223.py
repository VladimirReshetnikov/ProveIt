#!/usr/bin/env python3
"""Independent source-interface, blank-startup, and universal runtime audit of K223.

The compiler is not imported. Its generated table and source are read as data.
The pinned predecessor supplies the retained arithmetic/list induction engine.
No finite bound on register values, padding, or the spare list is introduced.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import sys
import time

TABLE_SHA = '7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef'
SOURCE_SHA = 'df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c'
PINS = {
    'check224.py': 'bd65fb0f8e89935f8b3651d7e76f01e0e378b4cb995af9d5f46ab11d5ffef393',
    'vendor/symbolic_runtime.py': 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
    'vendor/independent_runtime.py': '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
    'results/renumbering224.json': 'ae12c54b71d8c3f6def9c14f2526b3f483ae4151ed24e21535b0228db659db24',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def canonical_check(C, rows, states, table_path, map_path):
    canonical, start, halt, canonical_states = C.parse(table_path)
    data = json.loads(map_path.read_text())
    mapping = {int(q): int(v) for q, v in data.get('k_to_canonical', data).items()}
    need(set(mapping) == states | {254}, 'Canonical map domain differs')
    need(set(mapping.values()) == set(range(224)) and len(mapping) == 224,
         'Canonical map is not a bijection')
    need((mapping[0], mapping[254], start, halt) == (0, 223, 0, 223),
         'Canonical initial or halting state differs')
    need(canonical_states == set(range(223)), 'Canonical working labels differ')
    expected = {(mapping[q], b): (w, d, mapping[z])
                for (q, b), (w, d, z) in rows.items()}
    need(canonical == expected, 'Canonical table is not the literal conjugate')
    order = [0]
    discovered = {0}
    for q in order:
        for b in (0, 1):
            z = canonical[q, b][2]
            if z != 223 and z not in discovered:
                discovered.add(z)
                order.append(z)
    need(order == list(range(223)), 'Canonical numbering is not breadth-first')
    return {'status': 'ALL_446_ROWS_CONJUGATE', 'table_sha256': sha(table_path),
            'map_sha256': sha(map_path), 'working_states': 223, 'rows': 446,
            'start': 0, 'halt': 223, 'breadth_first_order': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-machine-dir', type=Path, required=True,
                    help='Extracted K224 portable/machine directory')
    ap.add_argument('--table', type=Path, required=True,
                    help='Frozen table in inherited K labels, with halt254')
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--canonical-table', type=Path)
    ap.add_argument('--canonical-map', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--skip-runtime', action='store_true',
                    help='Check structure, labels and complete startup only')
    a = ap.parse_args()
    a.output.mkdir(parents=True, exist_ok=True)
    report = {'status': 'IN_PROGRESS', 'checker_sha256': sha(Path(__file__)),
              'table_file': a.table.name, 'source_file': a.sites.name,
              'proof_status': 'Executable ordinary mathematical induction; no new proof-assistant endpoint.'}
    try:
        need(__debug__ and not sys.flags.optimize, 'Assertions must be enabled')
        base = a.baseline_machine_dir.resolve()
        for name, expected in PINS.items():
            need(sha(base / name) == expected, 'Pinned dependency differs: ' + name)
        report['dependency_sha256'] = PINS
        need(sha(a.table) == TABLE_SHA and sha(a.sites) == SOURCE_SHA,
             'The frozen K223 table or source changed')
        report.update(table_sha256=TABLE_SHA, source_sha256=SOURCE_SHA)
        sys.path.insert(0, str(base / 'vendor'))
        sys.path.insert(0, str(base))
        E = importlib.import_module('symbolic_runtime')
        C = importlib.import_module('check224')
        need(sha(Path(E.__file__)) == PINS['vendor/symbolic_runtime.py'],
             'A different symbolic engine was already imported')
        need(sha(Path(C.__file__)) == PINS['check224.py'],
             'A different structure/startup helper was already imported')
        need(sha(Path(E.r.__file__)) == PINS['vendor/independent_runtime.py'],
             'A different arithmetic runtime helper was already imported')
        table, start, halt, states = C.parse(a.table)
        need((start, halt, len(states), len(table)) == (0, 254, 223, 446),
             'Incorrect K223 literal table census')
        legacy = {int(k): int(v) for k, v in json.loads(
            (base / 'results/renumbering224.json').read_text())['k_to_legacy'].items()}
        need(states | {254} <= set(legacy), 'A new uncalibrated engine label appears')
        legacy = {q: legacy[q] for q in states | {254}}
        need(len(set(legacy.values())) == len(legacy), 'Legacy map is not injective')
        lt = {(legacy[q], b): (w, d, legacy[z]) for (q, b), (w, d, z) in table.items()}
        sites, graph, metrics = C.source_graph(a.sites)
        expected_cases = sum(2 if op == 'CD' else 1 for pc, op, arg in sites)
        need((len(sites), expected_cases, metrics['maximum_depth'],
              metrics['maximum_zero_run']) == (4962, 6449, 37, 6),
             'Unexpected source census')
        leaves = {pc: (op, arg) for pc, op, arg in sites}
        subtrees = set()
        def source_tree(pc):
            node = leaves[pc] if pc in leaves else (source_tree(pc + '0'), source_tree(pc + '1'))
            subtrees.add(node)
            return node
        source_tree('')
        need(len(subtrees) == 209, 'Distinct source-subtree census differs')
        metrics['distinct_source_subtrees'] = 209
        report.update(states=223, rows=446, expected_cases=6449,
                      source_metrics=metrics, k_to_legacy=legacy)
        need(bool(a.canonical_table) == bool(a.canonical_map),
             'Both canonical table and map must be supplied together')
        if a.canonical_table:
            report['canonical'] = canonical_check(C, table, states,
                                                   a.canonical_table, a.canonical_map)
        q, h, ones, used = C.execute(table, 0, 254, 409835)
        want, logical, physical = C.expected_frame()
        need((q, h, ones) == (84, -5, want), 'Complete blank startup differs')
        report['startup'] = {'status': 'EXACT_COMPLETE_BLANK_STARTUP_PASS',
            'steps': 409835, 'state_k': 84, 'head': -5, 'one_cells': sorted(ones),
            'all_other_cells': 0, 'logical_registers': logical,
            'physical_registers': physical, 'extra_gap': 117, 'spares': [1] * 167,
            'used_rows': sorted(used)}
        print('223 states; 446 rows; complete blank startup and source interface PASS', flush=True)
        if a.skip_runtime:
            report['status'] = 'STRUCTURE_LABELS_AND_STARTUP_PASS'
        else:
            begun = time.monotonic()
            seen = set()
            cases = []
            lemmas, blocks = E.prove_blocks(lt)
            report['induction_blocks'] = blocks
            for i, site in enumerate(sites):
                for positive in ((False, True) if site[1] == 'CD' else (False,)):
                    answer = E.case(lt, lemmas, site, positive)
                    seen.update(answer.pop('rows'))
                    answer.pop('trace')
                    cases.append({'site_index': i, 'positive': positive, **answer})
                    if len(cases) % 1000 == 0:
                        print('Proved', len(cases), 'of 6449 cases', flush=True)
            need(len(cases) == 6449 and seen == set(lt), 'Incomplete source or row coverage')
            need(all(len(x['duration']) == 13 and all(type(v) is int and v >= 0
                 for v in x['duration']) and x['duration'][0] >= 13 for x in cases),
                 'Missing universal positive-duration certificate')
            save(a.output / 'cases.json', cases)
            report.update(status='UNIVERSAL_RUNTIME_PASS', cases=len(cases),
                seconds=time.monotonic() - begun, used_legacy_rows=sorted(seen),
                all_rows_used=True, symbolic_steps=sum(x['symbolic_steps'] for x in cases),
                minimum_duration=min(x['duration'][0] for x in cases),
                maximum_symbolic_steps=max(x['symbolic_steps'] for x in cases),
                cases_file='cases.json', cases_sha256=sha(a.output / 'cases.json'),
                quantifiers='Nine independent natural registers, arbitrary natural extra gap, arbitrary natural first spare, arbitrary finite remaining spare list, and complete blank exterior.',
                bound_scope='The 4000 symbolic-rule derivation limit bounds proof search only, not concrete values or execution time.')
            need(report['symbolic_steps'] == 1566562 and report['maximum_symbolic_steps'] == 400,
                 'Fresh exact-table derivation differs from the first independent replay')
        need(sha(a.table) == TABLE_SHA and sha(a.sites) == SOURCE_SHA,
             'Input changed during audit')
        save(a.output / 'audit.json', report)
        print(report['status'], flush=True)
        return 0
    except Exception as error:
        report.update(status='FAILED', error=repr(error),
                      site_index=locals().get('i'), site=locals().get('site'),
                      positive=locals().get('positive'), cases_completed=len(locals().get('cases', [])))
        save(a.output / 'audit.json', report)
        print('FAILED:', repr(error), flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
