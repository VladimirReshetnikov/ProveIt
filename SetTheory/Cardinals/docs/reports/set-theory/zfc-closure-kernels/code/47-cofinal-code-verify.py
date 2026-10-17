#!/usr/bin/env python3
"""Read-only quick verification for the research archive (Python standard library).

Checks literal finite facts and record integrity. It is not a replacement for
the unbounded simulation, consistency interpretation, or a Lean/Coq rebuild.
Run without Python's -O option: deliberate assertions are part of this checker.
"""
from __future__ import annotations

import gzip
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
CANONICAL_SHA = '8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797'
OLD_SHA = '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(relative: str):
    return json.loads((ROOT / relative).read_text(encoding='utf-8'))


def read_table(path: Path):
    table, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, bit, write, move, target = line.split()
            key = int(q), int(bit)
            assert key not in table
            assert int(bit) in (0, 1) and int(write) in (0, 1)
            assert move in ('L', 'R')
            table[key] = int(write), move, int(target)
    assert start is not None
    states = {q for q, _ in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    terminals = {t for _, _, t in table.values()} - states
    assert len(terminals) == 1 and start in states
    return table, start, terminals.pop()


def check_reference_machine():
    canonical = ROOT / 'machines/zfc_permutation252.tm'
    old = ROOT / 'machines/zfc_permutation252_old.tm'
    assert digest(canonical) == CANONICAL_SHA
    assert digest(old) == OLD_SHA
    table, start, halt = read_table(canonical)
    old_table, old_start, old_halt = read_table(old)
    assert (len(table), start, halt) == (504, 0, 252)
    assert (len(old_table), old_start, old_halt) == (504, 64, 254)
    assert {q for q, _ in table} == set(range(252))
    assert sum(t == halt for _, _, t in table.values()) == 1
    renaming = read_json('data/renumbering.json')
    mapping = {int(k): v for k, v in renaming['old_to_canonical'].items()}
    mapping[254] = 252
    for (q, bit), (write, move, target) in old_table.items():
        assert table[mapping[q], bit] == (write, move, mapping[target])

    # Independent extraction of all 504 actions from the pinned Lean source.
    lean = (ROOT / 'references/lean/TablePerm252.lean').read_text()
    source = lean.split('def rawTablePerm252', 1)[1].split(']')[0]
    actions = re.findall(r'\((false|true), \.(left|right), (\d+)\)', source)
    assert len(actions) == 504
    for i, (write, direction, target) in enumerate(actions):
        assert table[i // 2, i % 2] == (
            int(write == 'true'), 'L' if direction == 'left' else 'R', int(target))

    boot = renaming['blank_prefix']
    state, head, ones = start, 0, set()
    for _ in range(boot['steps']):
        write, direction, state = table[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        assert state != halt
    assert (state, head) == (boot['state_canonical'], boot['head']) == (94, 2)
    assert ones == set(boot['all_one_positions'])
    values = boot['primary'] + boot['spares']
    assert len(values) == 74 and values[:9] == [0] * 9
    assert boot['spares'] == [int(i == 8) for i in range(65)]
    painted = {1, 42}
    cursor = 43
    for value in values:
        painted.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    assert painted == ones and len(ones) == 77
    return {'states': 252, 'rows': 504, 'Lean_rows_match': 504,
            'blank_steps': boot['steps'], 'state': state, 'head': head,
            'complete_one_cell_count': len(ones)}


def check_sources():
    count = 0
    for folder in ('lean', 'coq'):
        manifest = read_json('references/' + folder + '/source_manifest.json')
        for row in manifest['sources']:
            path = ROOT / 'references' / folder / row['local_file']
            assert path.stat().st_size == row['bytes'], path
            assert digest(path) == row['sha256'], path
            count += 1
    vendor_count = 0
    for row in read_json('data/pinned_blob_metadata.json'):
        path = ROOT / 'vendor/proveit' / row['path']
        data = path.read_bytes()
        assert len(data) == row['size'], path
        git_blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        assert hashlib.sha1(git_blob).hexdigest() == row['sha'], path
        vendor_count += 1
    return {'reference_files': count, 'pinned_vendor_blobs': vendor_count}


def check_logical_diagnostics():
    spec = importlib.util.spec_from_file_location('cofinal_diagnostic',
                                                ROOT / 'code/cofinal_countermodel.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    record = read_json('data/cofinal_countermodel_results.json')
    rows = [module.logical_checks(0), module.logical_checks(1)]
    padding = module.padding_checks()
    gaps = module.exact_gap_checks()
    assert rows == record['logical_countermodels']
    assert padding == record['padding']
    assert gaps == record['exact_gap_enumeration']
    return {'row_and_assignment_evaluations': sum(
                sum(r['row_evaluations'].values()) for r in rows),
            'padding_triples': padding['valid_old_triples'],
            'gap_emissions': gaps['generated_triples_checked'],
            'permitted_triples_below_10': gaps['distinct_permitted_triples_covered_below_bound']}


def check_search_record():
    summary = read_json('data/incoming_action_results.json')
    manifest = read_json('data/incoming_action_manifest.json')
    assert digest(ROOT / 'data/incoming_action_results.json') == manifest['results_sha256']
    assert digest(ROOT / 'code/incoming_action_search.py') == manifest['driver_sha256']
    archive = ROOT / 'data/incoming_action_journal.jsonl.gz'
    assert digest(archive) == manifest['journal_compressed_sha256']
    assert archive.stat().st_size == manifest['journal_compressed_bytes']
    strict = ROOT / 'vendor/proveit/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    prog = ROOT / 'vendor/proveit/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    assert digest(strict) == summary['input_sha256']['strict']
    assert digest(prog) == summary['input_sha256']['Prog254']
    expected = ((q, r, e, d) for q in summary['eligible_deletions']
                for r in summary['working_states_old'] if r != q
                for e, d in summary['mutation_order'])
    hasher, byte_count, recipes, reasons = hashlib.sha256(), 0, 0, Counter()
    with gzip.open(archive, 'rb') as stream:
        for line, recipe in itertools.zip_longest(stream, expected):
            assert line is not None and recipe is not None
            hasher.update(line)
            byte_count += len(line)
            entry = json.loads(line)
            assert tuple(entry[k] for k in ('deleted', 'replacement', 'flip_write', 'flip_move')) == recipe
            assert 0 <= entry['first_failure_case'] < 8391
            reasons[entry['reason']] += 1
            recipes += 1
    assert hasher.hexdigest() == manifest['journal_uncompressed_sha256']
    assert byte_count == manifest['journal_uncompressed_bytes']
    assert recipes == summary['planned_recipes'] == summary['completed_recipes'] == 166413
    assert reasons == summary['failure_reasons'] == manifest['failure_reasons']
    assert summary['status'] == 'completed'
    assert summary['affine_survivors'] == summary['whole_boot_survivors'] == []
    return {'journal_recipes': recipes, 'recorded_affine_checks': summary['affine_checks'],
            'first_stop_categories': dict(reasons), 'affine_runs_reexecuted': False}


def check_compiler_records():
    base = ROOT / 'experiments/cofinal_gate'
    results = json.loads((base / 'results.json').read_text())
    assert results['helper_tests'] == {'cleanup': 729, 'shift_fixed_cg': 729, 'shift_general': 729}
    measured = {'original': results['original']}
    for variant, data in results['variants'].items():
        assert len(data['candidates']) == results['seeds'] == 32
        assert data['best']['total_states'] == min(x['total_states'] for x in data['candidates'])
        for which in ('unshared', 'best'):
            measured[variant + '/' + which] = data[which]
    for relative, record in measured.items():
        path = base / relative / 'machine.tm'
        table, start, halt = read_table(path)
        assert digest(path) == record['machine_sha256']
        assert len(table) == record['transition_rows'] == 2 * record['total_states']
        assert record['decision_states'] + record['framework_states'] == record['total_states']
        assert (start, halt) == (0, record['total_states'])
    return {key: r['total_states'] for key, r in measured.items()}


def main():
    if not __debug__:
        raise SystemExit('Run this verifier without -O: assertions must be enabled.')
    result = {'reference_machine': check_reference_machine(),
              'source_integrity': check_sources(),
              'logical_diagnostics': check_logical_diagnostics(),
              'search_record_integrity': check_search_record(),
              'compiler_table_integrity': check_compiler_records(),
              'scope': 'Finite replay, syntax and record integrity only; no Lean/Coq rebuild or consistency proof execution.'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
