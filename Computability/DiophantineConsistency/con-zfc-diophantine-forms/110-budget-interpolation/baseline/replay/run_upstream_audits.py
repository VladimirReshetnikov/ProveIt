#!/usr/bin/env python3
"""Replay reviewed upstream audit entry points without modifying their releases.

Run from any directory. Defaults are relative to this script; --baseline and
--output may point to a relocated package. No network, installation, or external
absolute imports are used. This is finite artifact replay, not a semantic proof.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT_FUSION = Path('ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24')
PARITY = Path('con-zfc-parity-norms-2026-10-23/con-zfc-parity-norms-2026-10-23')
AUDITORS = ['audit.py', 'audit_norm_family.py', 'audit_shift.py',
            'audit_compact_kernel.py', 'independent_checks.py',
            'independent_graph_audit.py', 'independent_compact_audit.py']

def digest(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    return {str(p.relative_to(root)): digest(p.read_bytes())
            for p in sorted(root.rglob('*')) if p.is_file()
            and '__pycache__' not in p.parts}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent/'results')
    parser.add_argument('--parity-root', type=Path, help='Explicit retained parity source; defaults to baseline/PARITY')
    parser.add_argument('--rootfusion-root', type=Path, help='Explicit retained rootfusion source; defaults to baseline/ROOT_FUSION')
    args = parser.parse_args()
    baseline = args.baseline.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    source_roots = {ROOT_FUSION:(args.rootfusion_root.resolve() if args.rootfusion_root else baseline/ROOT_FUSION),
                    PARITY:(args.parity_root.resolve() if args.parity_root else baseline/PARITY)}
    before = {str(p): inventory(source_roots[p]) for p in (ROOT_FUSION, PARITY)}
    tasks = [('rootfusion_normal', ROOT_FUSION, False),
             ('rootfusion_optimized', ROOT_FUSION, True),
             ('parity_normal', PARITY, False),
             ('parity_optimized', PARITY, True)]

    def run(task):
        label, source, optimized = task
        results = []
        destination = out/label
        destination.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='wave13-reviewed-upstream-') as tmp:
            work = Path(tmp)/'release'
            shutil.copytree(source_roots[source], work,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            if source == ROOT_FUSION:
                commands = [('release', 'verification/verify_release.py',
                             ['--output', str(destination/'release.json')], 0)]
            elif not optimized:
                commands = [('release', 'verify_release.py',
                             ['--output', str(destination/'release.json')], 0)]
            else:
                commands = [('driver_policy', 'verify_release.py', [], 1)]
                commands += [(Path(s).stem, s, [], 0) for s in AUDITORS]
            for stage, script, extra, expected in commands:
                command = [sys.executable, '-B'] + (['-O'] if optimized else []) + [script] + extra
                tick = time.monotonic()
                process = subprocess.run(command, cwd=work, env={**os.environ,
                    'PYTHONDONTWRITEBYTECODE':'1'}, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE)
                stdout = destination/(stage+'.stdout.txt')
                stderr = destination/(stage+'.stderr.txt')
                stdout.write_bytes(process.stdout)
                stderr.write_bytes(process.stderr)
                policy_ok = (expected == 1 and process.returncode != 0 and
                    b'run this release verifier without -O' in process.stderr)
                ok = policy_ok if expected else process.returncode == 0
                record = {'stage':stage, 'script':script,
                    'python_flags':['-B'] + (['-O'] if optimized else []),
                    'returncode':process.returncode, 'expected_policy_rejection':bool(expected),
                    'status':'EXPECTED_REJECTION' if policy_ok else ('PASS' if ok else 'FAIL'),
                    'seconds':round(time.monotonic()-tick,3),
                    'stdout_sha256':digest(process.stdout), 'stderr_sha256':digest(process.stderr)}
                results.append(record)
                print(label,stage,record['status'],record['seconds'],flush=True)
                if not ok:
                    break
            if source == PARITY and optimized:
                for name in ('AUDIT.json','NORM_FAMILY_AUDIT.json','SHIFT_AUDIT.json',
                             'COMPACT_KERNEL_AUDIT.json','GRAPH_AUDIT.json',
                             'COMPACT_INDEPENDENT_AUDIT.json'):
                    if (work/name).is_file():
                        shutil.copy2(work/name, destination/name)
        receipt = {'source':str(source), 'python_optimized':optimized,
                   'stages':results, 'status':'PASS' if all(r['status'] in
                   ('PASS','EXPECTED_REJECTION') for r in results) else 'FAIL',
                   'scope':'Full release for rootfusion both modes and parity normal; parity optimized driver rejects by policy, then seven standalone algebraic auditors are run.'}
        (destination/'summary.json').write_text(json.dumps(receipt,indent=2)+'\n')
        return label,receipt

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        receipts = dict(pool.map(run,tasks))
    after = {str(p):inventory(source_roots[p]) for p in (ROOT_FUSION,PARITY)}
    unchanged = before == after
    result = {'status':'PASS' if unchanged and all(x['status']=='PASS' for x in receipts.values()) else 'FAIL',
              'repository_commit':'7e533c33819ee1f703b69f2778a767cdc069940d',
              'python':sys.version, 'source_releases_unchanged':unchanged,
              'source_files':{p:len(v) for p,v in before.items()},
              'receipts':receipts, 'elapsed_seconds':round(time.monotonic()-started,3),
              'scope':'Finite exact arithmetic, source binding, literal rebuilds and corruption diagnostics. No whole-repository build, no Lean or internal-ZFC certificate, no search for consistency-polynomial zeros.'}
    (out/'REPLAY_SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'seconds':result['elapsed_seconds'],
                      'source_releases_unchanged':unchanged}))
    if result['status']!='PASS':
        raise SystemExit(1)

if __name__ == '__main__':
    main()
