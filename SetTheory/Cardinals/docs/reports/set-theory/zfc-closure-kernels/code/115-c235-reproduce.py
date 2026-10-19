#!/usr/bin/env python3
"""Offline replay of the complete235-state construction and its evidence.

The default rebuilds the exact bytes, rechecks source, fold, initialization
and equational packet certificates, audits the complete delivered runtime
receipts, and replays the inherited236 quick suite. --full additionally
constructs both unbounded runtime certificates again. All outputs go to a
new directory; supplied artifacts and evidence are never overwritten.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent
ARCHIVE_SHA256 = '540305f4e805165e818290e82c5a6cba5faed25b5abb946fd9c750f6c45db9f5'
PYTHON = [sys.executable, '-B']


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def manifest():
    path = ROOT/'SHA256SUMS'
    require(path.is_file(), 'Missing package manifest')
    seen = set()
    for line in path.read_text().splitlines():
        digest, name = line.split('  ', 1)
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and name not in seen,
                'Unsafe or repeated manifest path')
        seen.add(name)
        require(sha(ROOT/name) == digest, f'Package byte mismatch: {name}')
    mandatory = {
        'README.md', 'report.tex', 'report.pdf', 'build_zfc235.py', 'reproduce.py',
        'machines/zfc235.tm', 'machines/zfc235_old.tm', 'machines/zfc_rotated236_old.tm',
        'machines/renumbering235.json', 'source/sites_logical.json',
        'source/source_rotation_certificate.json', 'verification/verify_runtime.py',
        'verification/check_fold235.py', 'verification/audit_fold74.py',
        'verification/verify_state_fold.py', 'verification/audit_source_graph.py',
        'verification/check_startup235.py', 'evidence/runtime_basis236.json',
        'evidence/runtime_basis236_cases.json', 'evidence/runtime_zfc235.json',
        'evidence/runtime_zfc235_cases.json', 'formalisms/build_e667.py',
        'formalisms/e663/build_e663.py', 'formalisms/e663/generated/E663.bits',
        'formalisms/e663/generated/E663.json', 'vendor/zfc236.zip',
    }
    require(mandatory <= seen, 'Manifest omits mandatory deliverables')
    return {'status': 'PASS', 'files': len(seen), 'manifest_sha256': sha(path)}


def command(label, arguments, output_dir, cwd=ROOT):
    log = output_dir/(label+'.log')
    began = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run([str(x) for x in arguments], cwd=cwd,
                                stdout=stream, stderr=subprocess.STDOUT)
    require(result.returncode == 0, f'{label} failed; see {log}')
    seconds = time.monotonic()-began
    print(label, 'PASS', round(seconds, 2), 'seconds', flush=True)
    return {'status': 'PASS', 'seconds': seconds, 'log': log.name}


def runtime_audit(prefix, table_path, source_path, baseline_dir, evidence_dir):
    receipt_path = evidence_dir/(prefix+'.json')
    receipt = read(receipt_path)
    require(receipt['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Incomplete runtime receipt')
    require(receipt['table_sha256'] == sha(table_path), 'Runtime table pin mismatch')
    require(receipt['sites_sha256'] == sha(source_path), 'Runtime source pin mismatch')
    require(receipt['driver_sha256'] == sha(ROOT/'verification/verify_runtime.py'),
            'Runtime driver pin mismatch')
    require(receipt['source_audit_sha256'] == sha(ROOT/'verification/audit_source_graph.py'),
            'Source auditor pin mismatch')
    engine_dir = baseline_dir/'upstream/zfc237/verification'
    require(receipt['engine_sha256'] == sha(engine_dir/'symbolic_runtime.py') and
            receipt['helper_sha256'] == sha(engine_dir/'independent_runtime.py'),
            'Runtime induction engine pin mismatch')
    cases_path = evidence_dir/receipt['cases_file']
    require(receipt['cases_file'] == prefix+'_cases.json' and
            receipt['cases_sha256'] == sha(cases_path), 'Case array pin mismatch')
    cases, sites = read(cases_path), read(source_path)
    expected = [(i, positive) for i, site in enumerate(sites)
                for positive in ((False, True) if site[1] == 'CD' else (False,))]
    require([(x['site_index'], x['positive']) for x in cases] == expected,
            'Missing, duplicated or reordered guarded cases')
    require(len(cases) == receipt['cases'] == 8386, 'Wrong guarded case count')
    for case in cases:
        require(type(case['positive']) is bool and len(case['duration']) == 13,
                'Malformed symbolic case')
        require(all(type(n) is int and n >= 0 for n in case['duration']) and
                case['duration'][0] > 0, 'Nonpositive symbolic duration')
        require(0 < case['symbolic_steps'] < 4000, 'Invalid proof-construction length')
    require(receipt['symbolic_steps'] == sum(x['symbolic_steps'] for x in cases),
            'Symbolic step total mismatch')
    require(receipt['maximum_symbolic_steps'] == max(x['symbolic_steps'] for x in cases),
            'Maximum proof-construction length mismatch')
    require(receipt['minimum_actual_steps'] == min(x['duration'][0] for x in cases) == 13,
            'Duration minimum mismatch')
    rows = set()
    for line in table_path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, *_ = line.split()
            rows.add((int(q), int(b)))
    require(set(map(tuple, receipt['used_rows'])) == rows and receipt['all_rows_used'],
            'Literal row coverage mismatch')
    require([(b['entry'], b['direction'], b['before'], b['after'])
             for b in receipt['list_induction_blocks']] ==
            [(73, 1, 'B', 'B'), (95, 1, 'B', 'C'), (48, -1, 'B', 'B'), (112, -1, 'C', 'B')],
            'Wrong list induction schemas')
    return {'status': 'PASS_COMPLETE_RUNTIME_EVIDENCE_AUDIT',
            'cases': len(cases), 'symbolic_steps': receipt['symbolic_steps'],
            'rows': len(rows), 'minimum_actual_steps': 13,
            'cases_sha256': sha(cases_path),
            'scope': 'Pins, exhaustive guarded-case inventory and certificate arithmetic. '
                     'Use --full to rederive the actual unbounded symbolic proofs.'}


def main():
    require(__debug__ and not sys.flags.optimize, 'Run without -O/-OO')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--full', action='store_true')
    args = ap.parse_args()
    dest = args.output_dir.resolve()
    require(not dest.exists() or (dest.is_dir() and not any(dest.iterdir())),
            'Choose a new or empty output directory')
    began = time.monotonic()
    manifest_result = manifest()
    dest.mkdir(parents=True, exist_ok=True)
    archive = ROOT/'vendor/zfc236.zip'
    require(sha(archive) == ARCHIVE_SHA256, 'Wrong retained236 archive')
    dependency = dest/'dependency'
    with zipfile.ZipFile(archive) as source:
        for item in source.infolist():
            path = PurePosixPath(item.filename)
            require(not path.is_absolute() and '..' not in path.parts, 'Unsafe dependency path')
            require((item.external_attr >> 16) & 0o170000 != 0o120000, 'Symlink in dependency')
        source.extractall(dependency)
    baseline = dependency/'zfc236-research-20261019'
    require((baseline/'README.md').is_file(), 'Unexpected dependency root')
    jobs = {}
    jobs['construction'] = command('construction', PYTHON+[ROOT/'build_zfc235.py',
        '--baseline-dir', baseline, '--output-dir', dest/'rebuilt'], dest)
    rebuilt = dest/'rebuilt'
    locations = {**{name: ROOT/'machines'/name for name in
                   ('zfc_rotated236_old.tm', 'zfc235_old.tm', 'zfc235.tm', 'renumbering235.json')},
                 **{name: ROOT/'source'/name for name in
                    ('sites_logical.json', 'source_rotation_certificate.json')},
                 'construction235.json': ROOT/'evidence/builder_construction235.json',
                 'startup235.json': ROOT/'evidence/builder_startup235.json'}
    for name, delivered in locations.items():
        require((rebuilt/name).read_bytes() == delivered.read_bytes(), f'Rebuilt bytes differ: {name}')
    basis, machine, sites = (rebuilt/name for name in
                            ('zfc_rotated236_old.tm', 'zfc235_old.tm', 'sites_logical.json'))
    finite_jobs = [
        ('source', [ROOT/'verification/audit_source_graph.py', baseline/'source/sites_logical.json',
                    sites, '--output', dest/'source.json']),
        ('fold', [ROOT/'verification/check_fold235.py', '--basis', basis, '--candidate', machine,
                  '--output', dest/'fold.json']),
        ('fold_independent', [ROOT/'verification/audit_fold74.py', basis, machine,
                              '--output', dest/'fold_independent.json']),
        ('fold_generic', [ROOT/'verification/verify_state_fold.py', basis, machine,
                          '--keep', '74', '--drop', '193', '--output', dest/'fold_generic.json']),
        ('startup', [ROOT/'verification/check_startup235.py', '--reference',
                     baseline/'machines/zfc236_old.tm', '--basis', basis, '--candidate', machine,
                     '--output', dest/'startup.json', '--canonical-output', dest/'canonical.tm']),
        ('E667', [ROOT/'formalisms/build_e667.py', '--reference', ROOT/'formalisms/reference',
                  '--out', dest/'E667']),
        ('E663', [ROOT/'formalisms/e663/build_e663.py', '--out', dest/'E663']),
    ]
    for label, arguments in finite_jobs:
        jobs[label] = command(label, PYTHON+arguments, dest)
    require((dest/'canonical.tm').read_bytes() == (ROOT/'machines/zfc235.tm').read_bytes(),
            'Independent canonicalization mismatch')
    for name, folder in [('E667', ROOT/'formalisms/generated'),
                         ('E663', ROOT/'formalisms/e663/generated')]:
        for suffix in ['.bits', '.bin', '.json', '.equations', '.bitlength']:
            require((dest/name/(name+suffix)).read_bytes() == (folder/(name+suffix)).read_bytes(),
                    f'Equational packet mismatch: {name+suffix}')
    if (ROOT/'discovery/replay_counterexamples.py').is_file():
        jobs['rejected_controls'] = command('rejected_controls', PYTHON+[
            ROOT/'discovery/replay_counterexamples.py', '--baseline-dir', baseline,
            '--output-dir', dest/'rejected_controls'], dest)
    audits = {name: runtime_audit(name, table, sites, baseline, ROOT/'evidence')
              for name, table in [('runtime_basis236', basis), ('runtime_zfc235', machine)]}
    jobs['inherited236_quick'] = command('inherited236_quick', PYTHON+[
        baseline/'reproduce.py', '--output-dir', dest/'inherited236'], dest, baseline)
    if args.full:
        fresh = dest/'fresh_runtime'
        fresh.mkdir()
        def full_job(name, table):
            command(name, PYTHON+[ROOT/'verification/verify_runtime.py',
                '--baseline-dir', baseline, '--table', table, '--sites', sites,
                '--output', fresh/(name+'.json')], dest)
            result = runtime_audit(name, table, sites, baseline, fresh)
            require((fresh/(name+'_cases.json')).read_bytes() ==
                    (ROOT/'evidence'/(name+'_cases.json')).read_bytes(), 'Fresh case array differs')
            return result
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures = {name: pool.submit(full_job, name, table) for name, table in
                       [('runtime_basis236', basis), ('runtime_zfc235', machine)]}
            fresh_results = {name: future.result() for name, future in futures.items()}
    else:
        fresh_results = {}
    result = {'status': 'PASS_FULL_REPLAY' if args.full else 'PASS_QUICK_REPLAY',
              'full': args.full, 'manifest': manifest_result, 'jobs': jobs,
              'runtime_evidence': audits, 'fresh_runtime': fresh_results,
              'working_states': 235, 'canonical_sha256': sha(ROOT/'machines/zfc235.tm'),
              'seconds': time.monotonic()-began,
              'proof_boundary': 'Ordinary mathematical proofs with exact finite and symbolic '
                                'certificates; inherited logical calibration; no new kernel endpoint.'}
    (dest/'replay.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
