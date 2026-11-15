#!/usr/bin/env python3
"""Replay the portable PA194SEL/PA194AX11GH release certificates.

Python 3.10+, standard library only, assertions enabled. Every builder and
checker runs on a temporary copy, so the delivered tables and certificates
are not overwritten. The default mode includes the AX11GH construction
replay; --full additionally runs its independent literal-tape replay.
Only the requested release JSON receipt is written outside the temporary
directory. No checkout, network access, C++ compiler or proof assistant is
needed. These are certificate checks, not an absolute PA/iPRA calibration.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'SEL': '5121f0b417ea025af140804b59e50a9d2fc3c461612e98b2f0ac86742c76a75b',
    'AX11GH': '513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1',
}
CORE_FILES = {
    'SEL': ('pa194sel.tm', 'pa194sel.native.tm', 'pa194sel.labels.json'),
    'AX11GH': ('machine.tm', 'machine.native.tm', 'raw.native.tm', 'labels.json',
               'nodes.json', 'grammar.tree.json', 'folds.json', 'local_folds.json',
               'sites.json', 'instructions.json'),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def machine_hashes(root):
    result = {}
    for family, names in CORE_FILES.items():
        for name in names:
            path = root / 'machines' / family / 'machine' / name
            result[str(path.relative_to(root))] = sha(path)
    return result


def run_check(name, relative_cwd, arguments, work, receipt):
    print(f'Checking {name} ...', flush=True)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['PYTHONHASHSEED'] = '0'
    env.pop('PYTHONOPTIMIZE', None)
    start = time.monotonic()
    result = subprocess.run([sys.executable, *arguments],
                            cwd=work / relative_cwd, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, encoding='utf-8', errors='replace')
    elapsed = round(time.monotonic() - start, 3)
    record = {
        'name': name,
        'cwd': relative_cwd or '.',
        'command': ['python3', *arguments],
        'return_code': result.returncode,
        'seconds': elapsed,
        'stdout': result.stdout.replace(str(work), '<temporary-package>'),
        'stderr': result.stderr.replace(str(work), '<temporary-package>'),
        'status': 'PASS' if result.returncode == 0 else 'FAIL',
    }
    receipt['checks'].append(record)
    print(f"  {record['status']} ({elapsed:.3f} seconds)", flush=True)
    if result.returncode:
        tail = (result.stderr or result.stdout)[-5000:]
        raise RuntimeError(f'{name} exited with {result.returncode}: {tail}')


def verify(work, full, receipt):
    frozen = machine_hashes(ROOT)
    require(frozen['machines/SEL/machine/pa194sel.tm'] == EXPECTED['SEL'],
            'The delivered SEL table does not have the pinned release hash.')
    require(frozen['machines/AX11GH/machine/machine.tm'] == EXPECTED['AX11GH'],
            'The delivered AX11GH table does not have the pinned release hash.')
    ignore = shutil.ignore_patterns('__pycache__', '*.pyc', '*.pyo')
    for folder in ('machines', 'comparison'):
        shutil.copytree(ROOT / folder, work / folder, ignore=ignore)
    (work / 'verification').mkdir()

    run_check('SEL reconstruction', 'machines/SEL', ['build.py'], work, receipt)
    for name in CORE_FILES['SEL']:
        relative = 'machines/SEL/machine/' + name
        require(sha(work / relative) == frozen[relative], 'SEL rebuild differs: ' + name)
    run_check('SEL finite simulation certificate', 'machines/SEL',
              ['verification/check.py', '--output', 'verification/replayed.json'], work, receipt)
    run_check('SEL independent reconstruction and whole startup', 'machines/SEL',
              ['verification/independent_check.py', '--old', 'inputs/primary.native.tm',
               '--new', 'machine/pa194sel.native.tm', '--output', 'verification/replayed_independent.json',
               '--write-new', 'verification/independently_rebuilt.native.tm'], work, receipt)
    sel = read_json(work / 'machines/SEL/verification/replayed.json')
    independent_sel = read_json(work / 'machines/SEL/verification/replayed_independent.json')
    require(sel['status'] == independent_sel['status'] == 'PASS', 'SEL receipt did not pass.')
    require(sel['working_states'] == 194 and sel['transition_rows'] == 388,
            'SEL state/transition count differs.')
    require(sel['ordinary_cases'] == 380 and len(sel['local_cases']) == 8,
            'SEL certificate has incomplete finite coverage.')
    require(sel['complete_seed_tape_equal'] and sel['new_startup_steps'] == 58208,
            'SEL startup checkpoint differs.')
    require(sha(work / 'machines/SEL/verification/independently_rebuilt.native.tm')
            == frozen['machines/SEL/machine/pa194sel.native.tm'],
            'Independent SEL reconstruction differs from the delivered native bytes.')

    run_check('110-class exact graph census and two-candidate novelty', '',
              ['comparison/census.py', 'verify', 'machines/SEL/machine/pa194sel.tm',
               'machines/AX11GH/machine/machine.tm', '--out', 'comparison',
               '--receipt', 'verification/replayed_novelty.json'], work, receipt)
    novelty = read_json(work / 'verification/replayed_novelty.json')
    require(novelty['status'] == 'PASS', 'Graph census did not pass.')
    require(novelty['historical_classes'] == novelty['historical_strong_classes'] == 110,
            'Expected 110 distinct historical classes under both comparison conventions.')
    results = novelty['candidate_results']
    require(len(results) == 2, 'Expected exactly two candidate graph results.')
    require({r['sha256'] for r in results} == set(EXPECTED.values()),
            'The novelty check did not examine both pinned release candidates.')
    require(all(r['working_states'] == r['quotient_states'] == 194
                and r['new_under_state_renaming'] and r['new_under_all_symmetries']
                for r in results), 'A candidate failed state count, quotient or novelty checks.')
    require(len({r['canonical_class'] for r in results}) == 2
            and len({r['strong_class'] for r in results}) == 2,
            'The two delivered candidates coincide under an allowed graph symmetry.')

    axcwd = 'machines/AX11GH'
    run_check('AX11GH reconstruction and 4778 construction contracts', axcwd,
              ['build.py'], work, receipt)
    for name in CORE_FILES['AX11GH']:
        relative = 'machines/AX11GH/machine/' + name
        require(sha(work / relative) == frozen[relative], 'AX11GH rebuild differs: ' + name)
    build = read_json(work / axcwd / 'machine/receipt.json')
    require(build['working_states'] == 194 and build['transitions'] == 388,
            'AX11GH state/transition count differs.')
    require(build['source_sites'] == 3671 and build['source_outcomes'] == 4778
            and build['local_fold_cases'] == 28, 'AX11GH construction coverage differs.')
    require(build['runtime']['ok'] and build['runtime']['contracts'] == 4778,
            'AX11GH construction replay was skipped or failed.')
    require(build['startup']['steps'] == 57922 and build['startup']['complete_tape_equality'],
            'AX11GH complete startup differs.')
    run_check('AX11GH source splice', axcwd, ['check_source.py'], work, receipt)
    run_check('AX11GH exact emitter and four-field codec', axcwd, ['check_emitter.py'], work, receipt)
    run_check('AX11GH universal command-word cases', axcwd,
              ['check_words.py', '--output', 'machine/replayed_words.json'], work, receipt)
    run_check('AX11GH independent source Shift and exact costs', axcwd,
              ['audit_shift.py', '--output', 'machine/replayed_shift.json'], work, receipt)
    run_check('Native restricted-rho/MP exchange certificate', axcwd,
              ['exchange/check_native_exchange.py', '--output', 'exchange/replayed.json'], work, receipt)
    run_check('Independent native exchange certificate', axcwd,
              ['exchange/check_exchange_independent.py', 'exchange/native_exchange.json',
               '--output', 'exchange/replayed_independent.json'], work, receipt)
    words = read_json(work / axcwd / 'machine/replayed_words.json')
    shift = read_json(work / axcwd / 'machine/replayed_shift.json')
    exchange = read_json(work / axcwd / 'exchange/replayed.json')
    exchange_independent = read_json(work / axcwd / 'exchange/replayed_independent.json')
    require(words['status'] == shift['status'] == exchange['status']
            == exchange_independent['status'] == 'PASS', 'An AX11GH audit receipt failed.')
    require(words['checked_identities'] == 31 and words['shift_guard'] == 'h=1',
            'AX11GH command cases or halt guard differ.')
    require(shift['cases'] == shift['exact_cost_checks'] == 4096,
            'The independent Shift audit has different finite coverage.')
    require(exchange['proof_lines'] == exchange_independent['proof_lines'] == 18897
            and exchange['K_or_S_axioms'] == exchange_independent['K_or_S_axioms'] == 0,
            'The exchange proof count or primitive rule inventory differs.')
    literal = None
    if full:
        run_check('AX11GH independent literal-tape 4778-outcome replay', axcwd,
                  ['independent/check.py', 'machine', '--output', 'replayed_literal'], work, receipt)
        literal = read_json(work / axcwd / 'replayed_literal/PA194AX11GH/receipt.json')
        require(literal['status'] == 'PASS' and literal['source_outcomes'] == 4778
                and literal['source_sites'] == 3671 and literal['states'] == 194
                and literal['rows'] == 388, 'Independent literal coverage differs.')
        require(literal['box_oracles'] is False and literal['list_lemmas_from_literal_table'] == 4
                and literal['independent_source_resolvers_agree']
                and literal['dense_native_conjugacy'] and literal['all_states_graph_reachable']
                and literal['whole_blank_startup'] and literal['startup_steps'] == 57922
                and literal['minimum_positive_duration_constant'] >= 1,
                'Independent literal proof-interface checks failed.')
        frozen_literal = read_json(ROOT / axcwd / 'verification/PA194AX11GH/receipt.json')
        require(literal['contracts_sha256'] == frozen_literal['contracts_sha256'],
                'Independent literal replay differs from the frozen complete contract receipt.')

    require(machine_hashes(ROOT) == frozen, 'Delivered machine artifacts changed during verification.')
    receipt['machine_artifacts_unchanged'] = True
    receipt['rebuilt_machine_artifacts_equal'] = frozen
    receipt['results'] = {
        'SEL': {'working_states': 194, 'transition_rows': 388, 'ordinary_cases': 380,
                'exceptional_cases': 8, 'startup_steps': 58208,
                'independent_reconstruction_equal': True},
        'AX11GH': {'working_states': 194, 'transition_rows': 388, 'source_sites': 3671,
                   'source_outcomes': 4778, 'local_fold_cases': 28, 'startup_steps': 57922,
                   'command_identities': 31, 'source_cost_audit_cases': 4096,
                   'construction_runtime': build['runtime'], 'independent_literal_receipt': literal},
        'novelty': novelty,
        'exchange': {'proof_lines': 18897, 'native_checker': exchange,
                     'independent_checker': exchange_independent},
    }
    receipt['independent_literal_replay_performed'] = full
    receipt['checks_passed'] = len(receipt['checks'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true',
                        help='Also replay all 4778 independent literal-tape outcomes (the slowest check).')
    parser.add_argument('--output', type=Path, default=ROOT / 'verification/release_receipt.json',
                        help='Release JSON receipt; defaults to verification/release_receipt.json.')
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        raise SystemExit('Python 3.10 or newer is required.')
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Assertions must be enabled. Run without -O, -OO or PYTHONOPTIMIZE.')
    receipt = {
        'status': 'RUNNING', 'mode': 'full' if args.full else 'quick',
        'source_commit': '603c58ca3bd6bf3222fcfc4e308e6b079f65d573',
        'python_version': list(sys.version_info[:3]), 'checks': [],
        'scope': 'Portable finite and symbolic certificates and exact graph novelty. '
                 'No new absolute iPRA/PA consistency calibration or proof-assistant endpoint is asserted.',
    }
    started = time.monotonic()
    code = 0
    try:
        with tempfile.TemporaryDirectory(prefix='pa194-release-') as temporary:
            verify(Path(temporary), args.full, receipt)
        receipt['status'] = 'PASS'
    except Exception as exc:
        receipt['status'] = 'FAIL'
        receipt['error'] = f'{type(exc).__name__}: {exc}'
        code = 1
        print(receipt['error'], file=sys.stderr, flush=True)
    receipt['total_seconds'] = round(time.monotonic() - started, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': receipt['status'], 'mode': receipt['mode'],
                      'checks_passed': receipt.get('checks_passed', 0),
                      'independent_literal_replay_performed': receipt.get('independent_literal_replay_performed', False),
                      'machine_artifacts_unchanged': receipt.get('machine_artifacts_unchanged', False),
                      'total_seconds': receipt['total_seconds'], 'receipt': str(args.output)}, indent=2), flush=True)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
