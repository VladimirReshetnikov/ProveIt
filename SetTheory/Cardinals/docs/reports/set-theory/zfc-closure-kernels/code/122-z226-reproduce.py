#!/usr/bin/env python3
"""Offline reproduction of the K226 construction and mathematical certificates.

Quick mode audits the stored unbounded-runtime receipts. --full additionally
rederives every unbounded instruction case for pinned K230 and final K226.
Neither mode invokes or claims a new Rocq kernel check.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
ENGINE_HASH = 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_HASH = '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def equal_file(actual, expected):
    require(actual.read_bytes() == expected.read_bytes(),
            f'Rebuilt bytes differ: {actual.name} versus {expected}')


def audit_runtime_receipt(path, cases_path, table, sites, count, rows):
    """Integrity/arithmetic checks only; a fresh proof needs --full."""
    report = json.loads(path.read_text())
    cases = json.loads(cases_path.read_text())
    require(report['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Incomplete stored runtime receipt')
    require(report['table_sha256'] == sha(table) and report['sites_sha256'] == sha(sites),
            'Runtime input pins')
    require(report['engine_sha256'] == ENGINE_HASH and report['helper_sha256'] == HELPER_HASH,
            'Runtime engine pins')
    require(report['cases_sha256'] == sha(cases_path), 'Runtime case-array hash')
    require(report['cases'] == report['expected_cases'] == len(cases) == count, 'Runtime case census')
    require(report['rows'] == rows and report['working_states'] * 2 == rows, 'Runtime row census')
    require(not report['unused_rows'] and len(report['used_rows']) == rows, 'Runtime row coverage')
    seen = set()
    source_rows = json.loads(sites.read_text())
    expected = set()
    for index, row in enumerate(source_rows):
        op = row[1].split()[0] if len(row) == 2 else row[1]
        expected.add((index,False))
        if op in ('CD','EDecnz'):
            expected.add((index,True))
    for case in cases:
        key = case['site_index'], case['positive']
        require(key not in seen and key in expected, 'Duplicate/unexpected runtime case')
        seen.add(key)
        duration = case['duration']
        require(len(duration) == 13 and all(type(x) is int and x >= 0 for x in duration)
                and duration[0] > 0, 'Nonpositive symbolic duration')
        require(0 < case['symbolic_steps'] < 4000, 'Symbolic proof-construction count')
    require(seen == expected, 'Missing runtime case')
    require(sum(c['symbolic_steps'] for c in cases) == report['symbolic_steps'], 'Rule sum')
    require(min(c['duration'][0] for c in cases) == report['minimum_actual_steps'], 'Minimum duration')
    return dict(cases=count, rows=rows, case_array_sha256=sha(cases_path),
                symbolic_rules=report['symbolic_steps'], minimum_actual_steps=report['minimum_actual_steps'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    require(sys.version_info >= (3,10), 'Python 3.10 or newer is required')
    require(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),
            'Run with assertions enabled and PYTHONOPTIMIZE unset')
    out = args.output_dir.resolve()
    require(out != ROOT and out not in (ROOT/'source', ROOT/'machines', ROOT/'vendor',
                                        ROOT/'verification', ROOT/'construction', ROOT/'evidence'),
            'Choose a separate replay directory')
    out.mkdir(parents=True, exist_ok=True)
    logs = out/'logs'
    logs.mkdir(exist_ok=True)
    result = dict(status='IN_PROGRESS', mode='full' if args.full else 'quick',
                  fresh_local_Rocq_build=False, started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
                  phases=[])
    started = time.monotonic()

    def save():
        result['seconds'] = time.monotonic()-started
        (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')

    def run(label, script, *arguments):
        print(label, flush=True)
        command = [sys.executable, '-B', str(ROOT/script), *map(str,arguments)]
        log = logs/(label+'.log')
        with log.open('w') as handle:
            process = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT)
        require(process.returncode == 0,
                f'{label} failed (exit {process.returncode}); see {log}\n'+log.read_text()[-2500:])
        result['phases'].append(dict(phase=label,status='PASS',log='logs/'+log.name))
        save()

    try:
        manifest_path = ROOT/'manifest.json'
        manifest = json.loads(manifest_path.read_text())
        for relative, expected in manifest['files'].items():
            p = Path(relative)
            require(not p.is_absolute() and '..' not in p.parts, 'Unsafe manifest path')
            require(sha(ROOT/p) == expected, 'Manifest mismatch: '+relative)
        result['manifest_files_checked'] = len(manifest['files'])
        result['manifest_sha256'] = sha(manifest_path)
        require(sha(ROOT/'verification/engine/symbolic_runtime.py') == ENGINE_HASH and
                sha(ROOT/'verification/engine/independent_runtime.py') == HELPER_HASH,
                'Inherited runtime engine changed')
        run('upstream', 'verification/audit_upstream.py', '--output', out/'upstream.json')
        run('machine-build', 'build_machine226.py', '--k230', ROOT/'vendor/k230-rocq/machine/k230.tm',
            '--source-certificate', ROOT/'source/source_rotations.json', '--output-dir', out/'machine')
        for entry in json.loads((ROOT/'construction/machine_artifacts.json').read_text()):
            name = entry['path']
            require(sha(ROOT/'construction'/name) == entry['sha256'], 'Stored construction hash')
            if name.endswith('.json'):
                require(json.loads((out/'machine'/name).read_text()) ==
                        json.loads((ROOT/'construction'/name).read_text()), 'Construction JSON changed: '+name)
            else:
                equal_file(out/'machine'/name, ROOT/'construction'/name)
        equal_file(out/'machine/k226.tm', ROOT/'machines/k226.tm')
        equal_file(out/'machine/k226_old.tm', ROOT/'machines/k226_old.tm')
        run('source-build', 'replay_k230_source.py', '--input-source', ROOT/'vendor/k230-rocq/machine/sites230.json',
            '--rotations', ROOT/'source/source_rotations.json', '--output', out/'source')
        equal_file(out/'source/sites_logical.json', ROOT/'source/sites226.json')
        equal_file(out/'source/sites_normalized.json', ROOT/'source/sites_logical.json')
        run('independent-source', 'verification/audit_k230_transports.py', '--source-only',
            '--upstream-root', ROOT/'vendor/k230-rocq', '--source-root', ROOT/'source',
            '--equivalent-source', out/'source/sites_logical.json', '--output', out/'source-audit.json')
        run('canonical-table', 'verification/audit_machine.py', '--old-table', out/'machine/k226_old.tm',
            '--canonical', out/'machine/k226.tm', '--renumbering', out/'machine/renumbering226.json',
            '--output', out/'machine-audit.json')
        run('sparse-bootstrap', 'verification/check_boot.py', ROOT/'vendor/k230-rocq/machine/k230.tm',
            out/'machine/k226_old.tm', '--output', out/'bootstrap.json')
        boot = json.loads((out/'bootstrap.json').read_text())
        require([x['steps'] for x in boot['tables']] == [408419,409835], 'Exact startup counts')
        run('dense-bootstrap', 'verification/audit_dense_boot.py', '--table', out/'machine/k226.tm',
            '--steps', '409835', '--dispatcher', '82', '--output', out/'dense-bootstrap.json')
        run('e639-codec', 'supplement/e639/build_e639.py', '--out', out/'e639',
            '--baseline-bits', ROOT/'supplement/inherited_formalisms/e663/generated/E663.bits')
        for name in ('E639.bits','E639.bin','E639.bitlength','E639.equations','E639.json','masking_recipe.json'):
            equal_file(out/'e639'/name, ROOT/'supplement/e639/generated'/name)

        records = [('runtime230', ROOT/'vendor/k230-rocq/machine/k230.tm',
                    ROOT/'vendor/k230-rocq/machine/sites230.json',6660,460),
                   ('runtime226', out/'machine/k226_old.tm',out/'source/sites_logical.json',6656,452)]
        result['stored_runtime_receipts'] = {}
        for name,table,sites,count,rows in records:
            result['stored_runtime_receipts'][name] = audit_runtime_receipt(
                ROOT/'evidence'/(name+'.json'), ROOT/'evidence'/(name+'_cases.json'), table,sites,count,rows)
        if args.full:
            result['fresh_runtime_derivations'] = {}
            for name,table,sites,count,rows in records:
                run('derive-'+name, 'verification/verify_runtime.py', '--table', table, '--sites', sites,
                    '--output', out/(name+'.json'))
                fresh = audit_runtime_receipt(out/(name+'.json'), out/(name+'_cases.json'),table,sites,count,rows)
                equal_file(out/(name+'_cases.json'), ROOT/'evidence'/(name+'_cases.json'))
                result['fresh_runtime_derivations'][name] = fresh
        result.update(status='FULL_REPLAY_PASS' if args.full else 'QUICK_REPLAY_PASS',
                      candidate_working_states=226, candidate_rows=452, source_leaves=5121,
                      bootstrap_steps=409835,
                      scope=('New ordinary mathematical transports checked; pinned upstream Rocq CI '
                             'receipts audited as external evidence. No new local kernel build.'))
        save()
        print(json.dumps(result,indent=2),flush=True)
    except Exception as error:
        result.update(status='FAIL',error=repr(error))
        save()
        raise


if __name__ == '__main__':
    main()
