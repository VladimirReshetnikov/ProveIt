#!/usr/bin/env python3
"""Quick, read-only verification of the delivered research bundle.

Run from any directory with Python 3.10 or later. No third-party packages,
network connection, Lean build, or complete mutation-search rerun is needed.
The inherited affine baseline audit is conditional on its four Box contracts;
these checks do not establish a new consistency-equivalent Turing machine.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
ZFC = 'upstream/Computability/BusyBeaver/Research/ZFC'
PROG = 'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
STRICT = ('upstream/SetTheory/Cardinals/docs/reports/set-theory/'
          'zfc-closure-kernels/code/'
          '27-variant-experiments-machine_search-grammar_search-strict_affine.py')
EXPECTED_INPUTS = {
    f'{ZFC}/candidate-permutation252/zfc_permutation252_old.tm':
        '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713',
    f'{ZFC}/candidate-permutation252/zfc_permutation252.tm':
        '8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797',
    'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm':
        'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb',
    PROG: '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
    'binary_experiments/Prog254.v':
        '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746',
    STRICT: 'da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce',
    'binary_experiments/strict_affine.py':
        'da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce',
}
EXCLUDED = [8202, 8203, 8204, 8358, 8359, 8360]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    answer = hashlib.sha256()
    with path.open('rb') as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b''):
            answer.update(chunk)
    return answer.hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def bundle_path(root, name):
    relative = PurePosixPath(name)
    require(not relative.is_absolute() and '..' not in relative.parts,
            f'Nonrelative bundle path: {name}')
    path = (root / str(relative)).resolve()
    require(path.is_relative_to(root), f'Path leaves bundle: {name}')
    return path


def check_manifest(root):
    path = root / 'MANIFEST.sha256'
    require(path.is_file(), 'MANIFEST.sha256 is missing')
    entries = {}
    for number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if not line:
            continue
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, f'Malformed manifest line {number}')
        expected, name = match.groups()
        require(name not in entries and name != 'MANIFEST.sha256',
                f'Duplicate or self-referential manifest entry: {name}')
        source = bundle_path(root, name)
        require(source.is_file(), f'Manifest file is missing: {name}')
        require(digest(source) == expected, f'Checksum mismatch: {name}')
        entries[name] = expected
    require(entries, 'The checksum manifest is empty')
    return {'status': 'PASS', 'checked_files': len(entries),
            'manifest_sha256': digest(path),
            'scope': 'Every listed file matches; later runtime files are not attested.'}, entries


def check_inputs(root):
    for name, expected in EXPECTED_INPUTS.items():
        source = bundle_path(root, name)
        require(source.is_file(), f'Pinned input is missing: {name}')
        require(digest(source) == expected, f'Pinned input checksum mismatch: {name}')
    manifest = read_json(root / 'binary_experiments/MANIFEST.json')
    require(manifest['pinned_commit'] == '43026ff42f0939f09b9e95495248cfadcad38e38',
            'Unexpected repository commit')
    for entry in manifest['inputs'] + manifest['files']:
        source = bundle_path(root, entry['path'])
        require(digest(source) == entry['sha256'],
                f'Binary investigation input/file mismatch: {entry["path"]}')
    regressions = read_json(root / 'proof_audit/oracle_regression_results.json')
    for name, expected in regressions['source_sha256'].items():
        require(digest(bundle_path(root, name)) == expected,
                f'Regression source identity mismatch: {name}')
    return {'status': 'PASS', 'fixed_inputs': len(EXPECTED_INPUTS),
            'commit': manifest['pinned_commit'],
            'binary_manifest_records': len(manifest['inputs']) + len(manifest['files'])}


def child(root, arguments, label):
    completed = subprocess.run([sys.executable, '-B', *map(str, arguments)],
                               cwd=root, text=True, capture_output=True)
    if completed.returncode:
        details = (completed.stdout + '\n' + completed.stderr)[-12000:]
        raise RuntimeError(f'{label} failed (exit {completed.returncode}):\n{details}')
    return completed.stdout


def baseline(root, scratch):
    target = scratch / 'baseline.json'
    work = scratch / 'baseline_work'
    child(root, [root / ZFC / 'candidate252_independent_audit.py',
                 '--repo', root / 'upstream', '--scratch', work,
                 '--source-table', root / ZFC / 'candidate-permutation252/zfc_permutation252_old.tm',
                 '--output', target], 'Inherited baseline audit')
    fresh = read_json(target)
    recorded = read_json(root / 'root_experiments/baseline_audit.json')
    omitted = {'command', 'scratch'}
    require({k: v for k, v in fresh.items() if k not in omitted} ==
            {k: v for k, v in recorded.items() if k not in omitted},
            'Fresh baseline audit differs from the recorded finite facts')
    require((fresh['working_states'], fresh['total_rows'],
             fresh['literal_boot_steps'], fresh['affine_audit']['passed_cases']) ==
            (252, 504, 82552, 8391), 'Unexpected baseline counts')
    require(len(fresh['literal_productive_instruction_trace']) == 64,
            'Expected 64 literal instruction replays')
    return {'status': 'PASS', 'working_states': 252, 'transitions': 504,
            'literal_blank_steps': 82552, 'affine_cases': 8391,
            'literal_instruction_replays': 64,
            'scope': ('Finite table/blank-run facts and universal affine instruction checks '
                      'conditional on the four attributed Box contracts; not a Lean build '
                      'or a fresh proof of the ZFC endpoint.')}


def lazy_partition(root, scratch):
    target = scratch / 'lazy_partition.json'
    child(root, [root / 'binary_experiments/audit_lazy_partition.py',
                 '--manifest', root / 'binary_experiments/lazy_context_complete_results.json',
                 '--journal', root / 'binary_experiments/lazy_context_complete_nodes.jsonl',
                 '--table', root / ZFC / 'candidate-permutation252/zfc_permutation252_old.tm',
                 '--output', target], 'Lazy assignment partition replay')
    fresh = read_json(target)
    recorded = read_json(root / 'binary_experiments/lazy_context_partition_audit.json')
    require(fresh == recorded, 'Fresh lazy partition replay differs from its record')
    require((fresh['concrete_assignments'], fresh['journal_entries'],
             fresh['survivor_assignments'], fresh['remaining_assignments']) ==
            (2898046, 185033, 0, 0), 'Unexpected lazy partition dimensions')
    return {'status': 'PASS', 'assignments': 2898046, 'journal_entries': 185033,
            'branch_entries': 737, 'prune_entries': 184296, 'remaining_frontier': 0,
            'scope': 'Independent complete assignment-partition replay; symbolic TM traces are not rerun.'}


def dbm_certificates(root, scratch):
    files = [root / f'proof_audit/relational_dbm_threshold{n}.json'
             for n in (2, 8, 32, 128)]
    target = scratch / 'dbm.json'
    child(root, [root / 'proof_audit/check_dbm_certificate.py', *files,
                 '--output', target], 'Independent DBM certificate checks')
    fresh = read_json(target)
    require(len(fresh) == 4, 'Expected four DBM certificate checks')
    for entry in fresh:
        require(entry['guards'] == 8391 and entry['sites'] == 6460 and
                entry['postfix_edges'] == 8384 and entry['excluded_guards'] == EXCLUDED,
                f'DBM certificate dimensions disagree: {entry["certificate"]}')
    return {'status': 'PASS', 'certificates': 4, 'guards_per_certificate': 8391,
            'nonhalting_edges_per_certificate': 8384,
            'excluded_guards': EXCLUDED,
            'scope': 'Independent standard-library integer checker; no NumPy search rerun.'}


ORACLE_CHILD = r'''
import importlib.util, json, sys
from pathlib import Path
root = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location(
    'bundle_oracle_regression', root / 'proof_audit/oracle_regressions.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
result = {'algebra': module.algebra_checks(),
          'interval_scheduler': module.scheduler_checks(),
          'prepared_literal_boxes': module.prepared_box_checks()}
Path(sys.argv[2]).write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
'''


def oracle_regressions(root, scratch):
    target = scratch / 'oracle.json'
    # Import the functions in an isolated interpreter. The module's output-writing
    # __main__ block never executes, and -B suppresses local bytecode creation.
    child(root, ['-c', ORACLE_CHILD, root, target], 'Oracle regression suite')
    fresh = read_json(target)
    recorded = read_json(root / 'proof_audit/oracle_regression_results.json')
    require(fresh == {k: recorded[k] for k in fresh},
            'Fresh oracle regression results differ from their record')
    return {'status': 'PASS',
            'algebra_checks': fresh['algebra']['checks'],
            'scheduler_contracts': fresh['interval_scheduler']['finite_sequence_contracts'],
            'concrete_comparisons': fresh['interval_scheduler']['independent_concrete_comparisons'],
            'prepared_box_excursions': fresh['prepared_literal_boxes']['prepared_excursions'],
            'literal_box_transitions': fresh['prepared_literal_boxes']['literal_binary_transitions'],
            'scope': 'Algebra controls, finite scheduler regressions, and individual prepared literal box excursions.'}


def check_fold_ledger(root, name, cases, expected_checks):
    path = root / f'binary_experiments/{name}.json'
    result = read_json(path)
    require(result['baseline_cases'] == cases and result['planned'] == 55471 and
            result['completed'] == 55471 and result['checks'] == expected_checks and
            result['survivors'] == [], f'Uniform-fold counts disagree: {name}')
    groups = result['groups']
    require(len(groups) == 221 and len({g['deleted'] for g in groups}) == 221,
            f'Unexpected deletion-source family: {name}')
    states = set(range(254)) - {5, 8}
    by_case = Counter()
    failures = Counter()
    total = 0
    journal = path.with_suffix('.jsonl')
    require(digest(journal) == result['journal_sha256'], f'Fold journal hash mismatch: {name}')
    with journal.open(encoding='utf-8') as stream:
        for group in groups:
            dead = group['deleted']
            require([f[0] for f in group['failures']] == sorted(states - {dead}),
                    f'Incomplete or reordered destinations for {name}/{dead}')
            for replacement, case, reason in group['failures']:
                require(0 <= case < cases and isinstance(reason, str) and reason,
                        f'Invalid first-failure record: {name}')
                row = json.loads(next(stream))
                require(row == {'deleted': dead, 'replacement': replacement,
                                'failure': [case, reason]}, f'Journal/summary mismatch: {name}')
                by_case[str(case)] += 1
                failures[reason.split("'", 2)[1] if "'" in reason else reason] += 1
                total += 1
        require(not stream.read().strip(), f'Unaccounted journal entries: {name}')
    require(total == 55471 and dict(by_case) == result['failures_by_case'] and
            dict(failures) == result['failures'], f'Fold aggregate mismatch: {name}')
    return result


def source_loop_certificates(root, scratch):
    target = scratch / 'countdown_catalogue.json'
    child(root, [root / 'proof_audit/countdown_loops.py', '--output', target],
          'Independent countdown source catalogue')
    fresh = read_json(target)
    recorded = read_json(root / 'proof_audit/countdown_loop_catalogue.json')
    require(fresh == recorded, 'Independent countdown catalogue differs from its record')
    summary = fresh['summary']
    require(summary['simple_countdown_loops'] == 1433 and
            summary['all_nonhalting_control_edges_cross_checked'] == 8390 and
            summary['regression_controls']['probes'] == 5732 and
            summary['regression_controls']['successful_source_steps'] == 45556,
            'Unexpected source-loop catalogue dimensions')
    independent = {entry['head_site']: entry for entry in fresh['loops']}
    projection_target = scratch / 'loop_projection.json'
    child(root, [root / 'proof_audit/check_loop_projection.py',
                 '--output', projection_target], 'Independent matrix projection controls')
    projection = read_json(projection_target)
    require(projection == read_json(root / 'proof_audit/loop_projection_audit.json') and
            projection['loop_catalogue_entries_compared'] == 1433 and
            projection['exact_equality_projection_controls'] == 48,
            'Independent signed matrix-projection controls disagree')
    expected_journal = '1167e5fb920c362b0e7b230936c1e9c496573fa4de206f78fc718a030c1cf1bc'
    reference_path = root / 'compiler_experiments/reference_block_halt_results'
    reference = read_json(reference_path / 'results.json')
    require(reference['completed_all'] and reference['completed'] == 55471 and
            reference['checks'] == 127788 and reference['survivors'] == [] and
            digest(reference_path / 'journal.jsonl') == expected_journal,
            'Fixed-prefix reference search dimensions or journal disagree')
    checked_fields = ['loop_count', 'gap_growth_rejected', 'loop_catalogue',
                      'summary_counts', 'catalogue_uses', 'new_target_records',
                      'target_sets_equal_previous_fixed_prefix_targets',
                      'target_count_histogram', 'hop_limit']
    for directory, dbm in [('final', False), ('dbm_projection', True)]:
        original = root / 'loop_experiments' / directory
        regenerated = scratch / f'frontier_{directory}'
        arguments = [root / 'loop_experiments/affine_reference_loops.py',
                     '--frontiers-only', '--hop-limit', '64', '--output', regenerated]
        if dbm:
            arguments.append('--dbm-projection')
        child(root, arguments, f'Countdown reference frontiers ({directory})')
        new = read_json(regenerated / 'source_frontiers.json')
        old = read_json(original / 'source_frontiers.json')
        require({k: new[k] for k in checked_fields} ==
                {k: old[k] for k in checked_fields},
                f'Regenerated source frontiers differ: {directory}')
        require(new['target_sets_equal_previous_fixed_prefix_targets'] and
                new['new_target_records'] == [] and
                new['summary_counts']['loop_summaries'] == 25952 and
                new['summary_counts']['unbounded_loop_summaries'] == 25589 and
                new['summary_counts']['non_offset_intermediate_matrices'] == 44706,
                f'Unexpected source-frontier summary: {directory}')
        require(new['summary_counts'].get('dbm_additional_offset_conversions', 0) == 0,
                'Unexpected DBM-only matrix projection')
        for key, entry in new['loop_catalogue'].items():
            other = independent[int(key)]
            require((entry['path'], entry['counter'], entry['body_sites'],
                     entry['body_increments'], entry['cycle_source_steps'],
                     entry['exit_site'], entry['exit_pc'], entry['exit_gap_increment'],
                     entry['cycle_gap_increment']) ==
                    (other['head_path'], other['counter'], other['body_sites'],
                     other['increments_per_positive_cycle'], other['positive_cycle_source_steps'],
                     other['zero_exit_site'], other['zero_exit_normalized_pc'],
                     other['zero_exit_gap_increment'], other['positive_cycle_gap_increment']),
                    f'Search/independent loop catalogue mismatch: {key}')
        result = read_json(original / 'results.json')
        require(result['completed_all'] and result['planned'] == result['completed'] == 55471 and
                result['checks'] == 127788 and result['survivors'] == [] and
                result['new_source_block_matches'] == [] and
                result['dbm_projection'] == dbm and
                result['journal_sha256'] == expected_journal and
                digest(original / 'journal.jsonl') == expected_journal,
                f'Completed countdown-fold search disagrees: {directory}')
    return {'status': 'PASS', 'independent_loops': 1433,
            'independent_source_edges': 8390, 'source_probes': 5732,
            'successful_source_steps_in_probes': 45556,
            'signed_matrix_projection_controls': 48,
            'regenerated_frontier_modes': ['singleton', 'DBM exact equalities'],
            'loop_summary_applications_per_mode': 25952,
            'additional_binary_targets': 0,
            'scope': ('Independent source-loop catalogue and concrete controls; both source '
                      'frontier modes regenerated; completed fold journal identities checked. '
                      'No binary-loop or new-machine proof is implied.')}


def binary_countdown_diagnostics(root, scratch):
    directory = root / 'binary_loop_experiments'
    manifest_path = directory / 'MANIFEST.json'
    manifest = read_json(manifest_path)
    require(manifest['upstream_commit'] == '43026ff42f0939f09b9e95495248cfadcad38e38',
            'Unexpected binary countdown repository commit')
    entries = manifest['files']
    require(isinstance(entries, dict) and entries,
            'The binary countdown manifest has no file records')
    for name, entry in entries.items():
        source = bundle_path(root, name)
        require(source.is_file(), f'Binary countdown manifest file is missing: {name}')
        require(source.stat().st_size == entry['bytes'] and
                digest(source) == entry['sha256'],
                f'Binary countdown manifest size/checksum mismatch: {name}')
    target = scratch / 'binary_countdown_diagnostics.json'
    child(root, [directory / 'verify_diagnostics.py', '--output', target],
          'Binary countdown diagnostic replay')
    fresh = read_json(target)
    recorded = read_json(directory / 'verification.json')
    require({k: v for k, v in fresh.items() if k != 'seconds'} ==
            {k: v for k, v in recorded.items() if k != 'seconds'},
            'Fresh binary countdown diagnostic replay differs from its recorded stable fields')
    require(fresh['status'] == 'PASS' and
            fresh['baseline_observer_equivalence_cases'] == 8391 and
            fresh['replayed_prefix_body_exit_source_contracts'] == 181 and
            fresh['initial_new_contracts'] + fresh['additional_new_contracts'] == 181 and
            len(fresh['verified_contract_identities']) == 181 and
            len({tuple(row) for row in fresh['verified_contract_identities']}) == 181 and
            fresh['whole_machine_survivors'] == 0,
            'Unexpected binary countdown replay dimensions or survivor count')
    return {'status': 'PASS', 'manifest_records': len(entries),
            'manifest_sha256': digest(manifest_path),
            'observer_comparisons': 8391, 'replayed_source_contracts': 181,
            'whole_machine_survivors': 0,
            'scope': ('Checks every binary countdown manifest entry and replays the observer '
                      'and all new source contracts against their receipts. Ordinary symbolic '
                      'verification conditional on protected Box contracts; no search rerun '
                      'or new whole-machine theorem.')}


def literal_binary_countdown(root, scratch):
    target = scratch / 'binary_countdown_literal.json'
    child(root, [root / 'proof_audit/binary_countdown_literal.py',
                 '--output', target], 'Continuous literal binary countdown controls')
    fresh = read_json(target)
    recorded = read_json(root / 'proof_audit/binary_countdown_literal.json')
    require(fresh == recorded, 'Fresh literal binary countdown receipt differs from its record')
    require(fresh['status'] == 'PASS continuous literal full-tape regression controls' and
            (fresh['controls'], fresh['literal_binary_steps'],
             fresh['successful_source_steps'], fresh['omitted_spare_negative_controls']) ==
            (16, 42008, 128, 12) and fresh['all_observed_heads_preserved'],
            'Unexpected literal binary countdown control dimensions')
    return {'status': 'PASS', 'prepared_frame_probes': 16,
            'literal_binary_transitions': 42008, 'successful_source_steps': 128,
            'omitted_spare_negative_controls': 12,
            'all_observed_heads_preserved': True,
            'scope': ('Continuous execution of literal binary rows on complete prepared tapes, '
                      'compared with exact source execution and complete final tapes. '
                      'Finite regression controls, not an unbounded or blank-start proof.')}


def recorded_search_counts(root):
    universal = check_fold_ledger(root, 'multieffect_fold_results', 8391, 127868)
    phase = check_fold_ledger(root, 'multieffect_phase_results', 8385, 127788)
    require(phase['source_case_ids'] == [i for i in range(8391) if i not in EXCLUDED],
            'Source-case remapping disagrees')
    inv = phase['source_invariant']
    require((inv['cap'], inv['period'], inv['enabled_cases'], inv['transfer_edges']) ==
            (32, 1, 8385, 8384) and inv['excluded_cases'] == EXCLUDED,
            'Source-interval result dimensions disagree')
    split = read_json(root / 'root_experiments/split_guard_fold_results.json')
    selected = [(g['deleted'], dst, i) for g in universal['groups']
                for dst, i, reason in g['failures'] if 'undetermined sequential guard' in reason]
    require(selected == [(r['deleted'], r['replacement'], r['first_old_failure'])
                         for r in split['results']], 'Guard-split selection disagrees')
    require(len(selected) == split['selected_recipes'] == 22923 and
            split['baseline_cases'] == 8391 and split['survivors'] == [] and
            split['first_contract_newly_passed'] == 0, 'Guard-split counts disagree')
    require(all(r['first_new_failure'] == r['first_old_failure'] and r['reason'] is not None
                for r in split['results']), 'Unexpected guard-split survivor')
    require(sum(r['splits'] for r in split['results']) ==
            split['stats']['exhaustive_splits'] == 46844, 'Guard-split total disagrees')
    replays = 8391 + sum(r['splits'] + r['passed_branches'] + 1 for r in split['results'])
    require(replays == split['stats']['trace_restarts'] == 78645,
            'Guard-split replay accounting disagrees')
    delimiter = read_json(root / 'binary_experiments/delimiter_repair_results.json')
    require(delimiter['recipes'] == 7 * 2 * (4 * 251 - 1) == 14042 and
            sum(delimiter['failures'].values()) == 14042 and
            delimiter['survivors'] == [] and len(delimiter['best']) == 23,
            'Delimiter search accounting disagrees')
    specialized = read_json(root / 'root_experiments/specialized_fold_results.json')
    require((specialized['recipes'], specialized['cases'], specialized['enabled_cases']) ==
            (55471, 127788, 8385) and specialized['survivors'] == [] and
            sum(specialized['failures'].values()) == 55471,
            'Specialized fold accounting disagrees')
    lazy = read_json(root / 'binary_experiments/lazy_context_complete_results.json')
    require(lazy['status'] == 'completed' and lazy['affine_checks'] == 558510 and
            lazy['full_recheck_affine_checks'] == 0 and lazy['remaining_frontier'] == [] and
            lazy['affine_survivors'] == [] and lazy['whole_boot_survivors'] == [],
            'Lazy search totals disagree')
    return {'status': 'PASS', 'uniform_fold_recipes_per_family': 55471,
            'guard_split_recipes': 22923, 'guard_splits': 46844,
            'guard_trace_replays': 78645, 'delimiter_recipes': 14042,
            'lazy_affine_checks_recorded': 558510,
            'scope': 'Recorded summaries and complete fold ledgers agree; full mutation searches are not rerun.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT,
                        help='Bundle root; normally the directory containing this script.')
    parser.add_argument('--skip-manifest', action='store_true',
                        help='Preassembly checks only: skip the top-level checksum manifest.')
    parser.add_argument('--output', type=Path,
                        help='Optional NEW JSON result file; existing files are never overwritten.')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Do not run with -O: inherited certificate checkers require assertions.')
    if sys.version_info < (3, 10):
        parser.error('Python 3.10 or later is required.')
    root = args.root.resolve()
    if args.output and args.output.exists():
        parser.error('--output must name a new file; bundled results are read-only.')
    begun = time.monotonic()
    report = {'status': 'RUNNING', 'scope': __doc__, 'checks': {}}
    checks = report['checks']
    try:
        if args.skip_manifest:
            checks['manifest'] = {'status': 'SKIPPED by --skip-manifest'}
        else:
            checks['manifest'], _ = check_manifest(root)
        print('Checksum/input checks...', flush=True)
        checks['pinned_inputs'] = check_inputs(root)
        with tempfile.TemporaryDirectory(prefix='permutation252-bundle-verify-') as temporary:
            scratch = Path(temporary)
            for label, function in [('conditional_baseline', baseline),
                                    ('lazy_partition', lazy_partition),
                                    ('dbm_certificates', dbm_certificates),
                                    ('oracle_regressions', oracle_regressions),
                                    ('source_loop_certificates', source_loop_certificates),
                                    ('binary_countdown_diagnostics', binary_countdown_diagnostics),
                                    ('literal_binary_countdown', literal_binary_countdown)]:
                print(f'Checking {label}...', flush=True)
                checks[label] = function(root, scratch)
            print('Checking recorded search ledgers...', flush=True)
            checks['recorded_search_counts'] = recorded_search_counts(root)
        report['status'] = 'PASS'
    except (OSError, ValueError, KeyError, AssertionError, RuntimeError, StopIteration) as error:
        report['status'] = 'FAIL'
        report['error'] = f'{type(error).__name__}: {error}'
    report['elapsed_seconds'] = round(time.monotonic() - begun, 3)
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        with args.output.open('x', encoding='utf-8') as destination:
            destination.write(text)
    print(text, end='')
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
