#!/usr/bin/env python3
"""Replay the delivered exact certificates in an isolated temporary copy.

Python 3.10+ standard library only. No network, optimizer, compiler, or proof
assistant is invoked. Expensive search histories are not rerun by this command.
Passing means the documented certificates and finite witnesses pass; it does
not mean a machine below 245 states or a new formal endpoint has been found.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check(root):
    entries = []
    for line in (root / 'MANIFEST.sha256').read_text().splitlines():
        expected, name = line.split('  ', 1)
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        path = root / relative
        assert path.is_file() and not path.is_symlink(), name
        assert digest(path) == expected, ('SHA256 mismatch', name)
        entries.append(name)
    assert len(entries) == len(set(entries))
    return len(entries)


def read_table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        assert b in (0, 1) and w in (0, 1) and direction in ('L', 'R')
        assert (q, b) not in result
        result[q, b] = w, direction, target
    return result


def check_tables(root):
    specs = [
        ('inputs/routing245-canonical.tm', 245, 0, 245),
        ('inputs/routing245-original-labels.tm', 245, 95, 254),
        ('experiments/scanner/rejected-short-scanner-244.tm', 244, 95, 254),
        ('experiments/shared_loop/rejected-gm-delete-244.tm', 244, 95, 254),
        ('experiments/foundations/routing_KSP_best/machine/ksp_250.tm', 250, 0, 250),
        ('experiments/machine_search/results/hg-swap/hg245.tm', 245, 95, 254),
    ]
    answer = []
    for name, count, start, halt in specs:
        path = root / name
        tab = read_table(path)
        states = {q for q, b in tab}
        assert len(states) == count and len(tab) == 2 * count
        assert start in states and halt not in states
        assert set(tab) == {(q, b) for q in states for b in (0, 1)}
        assert {v[2] for v in tab.values()} <= states | {halt}
        answer.append(dict(file=name, working_states=count, rows=len(tab),
                           start=start, halt=halt, sha256=digest(path)))
    baseline = read_table(root / specs[1][0])
    for name, removed, incoming, target in [
        (specs[2][0], 58, (41, 0), (0, 'L', 84)),
        (specs[3][0], 142, (119, 1), (1, 'R', 72)),
    ]:
        altered = dict(baseline)
        altered[incoming] = target
        del altered[removed, 0], altered[removed, 1]
        assert read_table(root / name) == altered
    return answer


def check_shared_boot(root):
    directory = root / 'experiments/scanner'
    sys.path.insert(0, str(directory))
    try:
        spec = importlib.util.spec_from_file_location('independent_blank_audit',
                                                     directory / 'blank_scanner_audit.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        path = root / 'experiments/shared_loop/rejected-gm-delete-244.tm'
        tab = module.read_table(path)
        q, head, ones = module.dense_replay(tab, 234805)
        frame = module.parse_frame(q, head, set(ones))
        assert frame is not None and frame['pc'] == ''
        assert frame['registers'] == [3, 0, 0, 0, 3, 0, 35, 0, 0]
        assert frame['head'] == -5 and frame['header'] == 106
        assert frame['distance'] == 111
        recorded = json.loads((root / 'experiments/shared_loop/rejected-gm-delete-boot.json').read_text())
        assert head == recorded['head'] and frame['registers'] == recorded['logical_registers']
        assert frame['spares'] == recorded['spare_values']
        assert ones == recorded['all_one_positions']
        return dict(status='FINITE_DIRTY_BOOT_REPLAY_PASS', binary_steps=234805,
                    logical_registers=frame['registers'], head=head,
                    header=frame['header'], gap=frame['distance'],
                    validates_source_edit=False)
    finally:
        sys.path.pop(0)


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Do not use python -O: assertions are part of the checks.')
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--complete-productions', action='store_true',
                        help='Additionally check every possible split over the serialized LP words.')
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--output', type=Path, help='Optional JSON summary destination.')
    args = parser.parse_args()
    count = manifest_check(ROOT)
    result = dict(manifest_files_checked=count, tables=check_tables(ROOT), checks={})
    if args.manifest_only:
        result['status'] = 'MANIFEST_AND_LITERAL_TABLES_PASS'
    else:
        with tempfile.TemporaryDirectory(prefix='zfc245-certificate-replay-') as temp:
            base = Path(temp) / 'package'
            shutil.copytree(ROOT, base, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            out = base / '_replay'
            out.mkdir()
            env = dict(os.environ)
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            env.pop('PYTHONOPTIMIZE', None)
            env.pop('PYTHONPATH', None)

            def run(name, cwd, argv, filename=None, expected_status=None):
                print('Checking ' + name + ' ...', file=sys.stderr, flush=True)
                started = time.monotonic()
                process = subprocess.run([sys.executable, *argv], cwd=base / cwd,
                                         env=env, capture_output=True, text=True)
                if process.returncode:
                    raise RuntimeError(name + '\n' + process.stdout + '\n' + process.stderr)
                data = (json.loads((base / filename).read_text()) if filename
                        else json.loads(process.stdout))
                if expected_status:
                    assert data['status'] == expected_status, (name, data)
                result['checks'][name] = dict(result=data,
                                              seconds=round(time.monotonic()-started, 3))
                return data

            run('finite_propositional_matrix', 'experiments/logic_matrices',
                ['verify_matrix.py'], expected_status='PASS_EXACT_FINITE_MATRIX')
            scanner = run('scanner_counterexample', 'experiments/scanner',
                ['blank_scanner_audit.py', '--table', '../../inputs/routing245-original-labels.tm',
                 '--sites', '../../inputs/routing245-sites-logical.json', '--shorten',
                 '--output', '../../_replay/scanner.json'], '_replay/scanner.json',
                'ACTUAL_BLANK_REACHABLE_CONTRACT_FAILURE')
            assert scanner['exit_binary_steps'] == 348237
            assert scanner['completed_source_steps'] == 259
            assert scanner['expected_frame']['pc'] == '111100001'
            assert scanner['actual_frame']['pc'] == '1111001'
            assert scanner['independent_dense_blank_replay'] is True
            baseline = run('baseline_blank_prefix', 'experiments/scanner',
                ['blank_scanner_audit.py', '--table', '../../inputs/routing245-original-labels.tm',
                 '--sites', '../../inputs/routing245-sites-logical.json', '--instructions', '274',
                 '--output', '../../_replay/baseline.json'], '_replay/baseline.json',
                'FINITE_PREFIX_PASS')
            assert baseline['binary_steps'] == 891107
            run('shared_loop_source_counterexample', 'experiments/shared_loop',
                ['deadloop_counterexample.py', '--output', '../../_replay/shared.json'],
                '_replay/shared.json', 'EXACT_SOURCE_COUNTEREXAMPLE_VERIFIED')
            result['checks']['shared_loop_dirty_boot'] = check_shared_boot(base)
            trace_args = ['verify_trace_results.py', '--package', 'pinned_inputs',
                '--reordering', 'baseline_trace.json', '--model', 'trace_lp20.lp_model.json.gz',
                '--certificate', 'trace_lp20.lp_certificate.json', '--positive-control',
                'trace128.json', '--output', '../../_replay/trace.json']
            if args.complete_productions:
                trace_args.append('--complete-productions')
            trace = run('exact_trace_certificates', 'experiments/trace_grammar',
                        trace_args, '_replay/trace.json')
            assert [x['status'] for x in trace] == ['SOURCE_TRACE_CERTIFICATES_PASS',
                'EXACT_INTEGER_DUAL_PASS', 'SOURCE_GRAMMAR_POSITIVE_CONTROL_PASS']
            assert trace[1]['grammar_lower_bound'] == trace[2]['grammar_rules'] == 128
            run('logical_translations_and_KSP250', 'experiments/foundations', ['verify.py'],
                'experiments/foundations/portable_verification.json', 'PASS_WITH_STATED_SCOPE')
            run('finite_fixture_reconstruction', 'experiments/machine_search',
                ['code/rebuild_fixtures.py'], expected_status='PASS_EXACT_FINITE_FIXTURE_REBUILD')
            for key, source, witness in [
                ('fine_grammar', 'inputs/fine/input.json', 'results/fine/result.json'),
                ('expanded_fine_grammar', 'inputs/fine/expanded-input.json', 'results/fine/expanded-result.json'),
            ]:
                data = run(key, 'experiments/machine_search',
                           ['code/check_fine.py', source, witness],
                           expected_status='PASS_FINITE_FINE_GRAMMAR_ONLY')
                assert data['total_grammar_rules'] == 128
            data = run('coarse_grammar', 'experiments/machine_search',
                ['code/check_route_grammar.py', 'results/new-zero6-k127.json', '--inputs', 'inputs',
                 '--bootstrap-lock', 'inputs/bootstrap-lock54.txt'], expected_status='PASS_ABSTRACT_ONLY')
            assert data['rules_count'] == 128
            hg = run('sound_hg245', 'experiments/machine_search',
                ['code/audit_hg_swap.py', '--affine', '--output', '../../_replay/hg.json'],
                '_replay/hg.json', 'PASS_SOUND_SOURCE_SWAP_AND_FINITE_BLANK_AUDIT')
            assert hg['guarded_instruction_cases'] == 8391 and hg['working_states'] == 245
            assert hg['conditional_universal_affine_audit']['cases'] == 8391
            result['status'] = 'ALL_REPLAY_CHECKS_PASS_WITH_STATED_SCOPES'
    result['outcome'] = 'No validated sub-245 consistency machine; no new compiled proof-assistant endpoint.'
    result['scope'] = ('Replayed exact finite certificates, finite literal executions, and conditional '
        'affine obligations. Expensive mutation and heuristic search histories are retained, not rerun.')
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
