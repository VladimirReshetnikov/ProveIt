#!/usr/bin/env python3
"""Replay the packaged, explicitly scoped Lean checks against the pinned checkout.

This does not apply the patches or change repository source.  It checks proposed
files separately against the repository's built imports.  See README.txt.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

COMMIT = '60e9c5d620c6c387d932876cfa2d9376f64ea56c'
MATHLIB = '81a5d257c8e410db227a6665ed08f64fea08e997'


def audited_axioms(output, name):
    start = re.escape("'" + name + "'")
    found = re.search(start + r' depends on axioms:\s*\[([^]]*)\]', output)
    if found:
        return sorted(x.strip() for x in found.group(1).split(',') if x.strip())
    if re.search(start + r' does not depend on any axioms', output):
        return []
    raise SystemExit('Missing axiom audit for ' + name)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repository', type=Path)
    ap.add_argument('--level', choices=['core', 'prototypes', 'full'], default='full')
    ap.add_argument('--build-prerequisites', action='store_true',
                    help='Run lake build for the listed original imports before checks.')
    ap.add_argument('--include-optional', action='store_true',
                    help='Also replay the compact coefficient and fused decoder tradeoffs.')
    ap.add_argument('--logs', type=Path, default=Path('replay-logs'))
    args = ap.parse_args()
    bundle = Path(__file__).resolve().parents[1]
    repo = args.repository.resolve()
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    plan = json.loads((bundle / 'evidence/verification-plan.json').read_text())
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != COMMIT:
        raise SystemExit('Wrong ProveIt revision: expected ' + COMMIT + ', got ' + head)
    if (repo / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.32.0':
        raise SystemExit('Unexpected lean-toolchain')
    lock = json.loads((repo / 'lake-manifest.json').read_text())
    if next(p['rev'] for p in lock['packages'] if p['name'] == 'mathlib') != MATHLIB:
        raise SystemExit('Unexpected mathlib lock revision')
    if not shutil.which('lake'):
        raise SystemExit('lake must be on PATH (normally provided by elan).')
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=repo, text=True)
    if not re.search(r'version 4\.32\.0\b', version):
        raise SystemExit('The active compiler is not Lean 4.32.0: ' + version)
    (logs / 'compiler-version.txt').write_text(version)
    # Check every reviewed maintained source, not just the branch name.
    inventory = json.loads((bundle / 'evidence/source-inventory.json').read_text())
    for row in inventory['files']:
        p = repo / 'Computability/DiophantineConsistency' / row['path']
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest() != row['sha256']:
            raise SystemExit('Source changed or missing: ' + str(p))
    subprocess.run(['git', '-C', str(repo), 'apply', '--check'] +
                   [str(bundle / p) for p in plan['recommended_patches']], check=True)
    if args.include_optional:
        # The fused decoder is an alternative to decoder-options, not additive.
        for patch in plan.get('optional_patches', []):
            subprocess.run(['git', '-C', str(repo), 'apply', '--check', str(bundle / patch)],
                           check=True)
    ranks = {'core': 0, 'prototypes': 1, 'full': 2}
    selected = [c for c in plan['checks'] if ranks[c['level']] <= ranks[args.level]
                and (args.include_optional or not c.get('optional', False))]
    if args.build_prerequisites:
        targets = {t for c in selected for t in c.get('prerequisites', [])}
        if args.level == 'full':
            targets.update(plan.get('overlay_prerequisites', []))
        targets = sorted(targets)
        if targets:
            with (logs / 'prerequisites.log').open('w') as stream:
                subprocess.run(['lake', 'build'] + targets, cwd=repo, stdout=stream,
                               stderr=subprocess.STDOUT, check=True)
    results = []
    for check in selected:
        path = bundle / check['file']
        if hashlib.sha256(path.read_bytes()).hexdigest() != check['sha256']:
            raise SystemExit('Packaged file checksum mismatch: ' + check['file'])
        name = check['id']
        logpath = logs / (name + '.log')
        command = ['lake', 'env', 'lean'] + check.get('lean_args', ['-j1']) + [str(path)]
        start = time.monotonic()
        with logpath.open('w') as stream:
            run = subprocess.run(command, cwd=repo, stdout=stream, stderr=subprocess.STDOUT)
        output = logpath.read_text()
        bad = re.search(r'\b(?:sorryAx|Lean\.ofReduceBool)\b', output)
        success = run.returncode == 0 and not bad and not re.search(r'(?m)^.*\berror:', output)
        row = {'id': name, 'file': check['file'], 'exit_code': run.returncode,
               'passed': bool(success), 'seconds_single_run': round(time.monotonic()-start, 3),
               'command': command, 'log': logpath.name}
        results.append(row)
        print(('PASS ' if success else 'FAIL ') + name, flush=True)
        if not success:
            (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            raise SystemExit('See ' + str(logpath))
    completed = {row['id'] for row in results}
    for comparison in plan.get('identical_audit_outputs', []):
        a, b = comparison
        pa, pb = logs / (a + '.log'), logs / (b + '.log')
        if a in completed and b in completed:
            if pa.read_bytes() != pb.read_bytes():
                raise SystemExit('Axiom-output comparison differs: ' + a + ' versus ' + b)
            print('IDENTICAL AUDIT OUTPUT ' + a + ' / ' + b, flush=True)
    for comparison in plan.get('axiom_set_comparisons', []):
        old, new = comparison['original'], comparison['replacement']
        # Only compare checks selected and completed in this invocation.
        if old['check'] in completed and new['check'] in completed:
            a = audited_axioms((logs / (old['check'] + '.log')).read_text(), old['constant'])
            b = audited_axioms((logs / (new['check'] + '.log')).read_text(), new['constant'])
            if a != b or a != sorted(comparison['expected_axioms']):
                raise SystemExit('Axiom set differs: ' + old['constant'] + ' / ' + new['constant'])
            print('MATCHING AXIOMS ' + new['constant'], flush=True)
    if args.level == 'full':
        subprocess.run(['lake', 'env', sys.executable,
                        str(bundle / 'scripts/verify_shared_patch.py'),
                        '--repo', str(repo), '--logs', str(logs / 'residual-overlay')],
                       cwd=repo, check=True)
    (logs / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('Selected checks passed. This is not a full downstream build of the applied patches.')


if __name__ == '__main__':
    main()
