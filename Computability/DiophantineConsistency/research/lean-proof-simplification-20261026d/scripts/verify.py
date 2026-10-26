#!/usr/bin/env python3
"""Replay the supplied proof refactors without changing a ProveIt source file.

Requires the pinned checkout and already built baseline dependency modules.
No package installation, network access, or full-project build is performed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

BASE = '60e9c5d620c6c387d932876cfa2d9376f64ea56c'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repository', type=Path)
    ap.add_argument('--lake-workspace', type=Path,
                    help='Existing Lake workspace; defaults to repository.')
    ap.add_argument('--lake', default='lake', help='Lake executable on PATH or absolute path.')
    ap.add_argument('--output', type=Path, help='New replay evidence directory.')
    args = ap.parse_args()
    bundle = Path(__file__).resolve().parent.parent
    repo = args.repository.resolve()
    workspace = (args.lake_workspace or repo).resolve()
    out = (args.output or bundle/'validation/replay').resolve()
    out.mkdir(parents=True, exist_ok=True)
    objects = out/'objects'
    (objects/'ProofSimplification').mkdir(parents=True, exist_ok=True)

    def query(command, cwd=workspace):
        return subprocess.check_output(command, cwd=cwd, text=True).strip()

    actual = query(['git', 'rev-parse', 'HEAD'], repo)
    if actual != BASE:
        raise SystemExit(f'Expected commit {BASE}; found {actual}.')
    pinned_manifest = json.loads((repo/'lake-manifest.json').read_text())
    mathlib_pin = next(p['rev'] for p in pinned_manifest['packages']
                      if p['name'] == 'mathlib')
    active_manifest = json.loads((workspace/'lake-manifest.json').read_text())
    mathlib_dir = workspace/active_manifest.get('packagesDir', '.lake/packages')/'mathlib'
    mathlib_actual = query(['git', 'rev-parse', 'HEAD'], mathlib_dir)
    if mathlib_actual != mathlib_pin:
        raise SystemExit(f'Expected mathlib {mathlib_pin}; found {mathlib_actual}.')
    prefix = query([args.lake, 'env', 'lean', '--print-prefix'])
    lean = str(Path(prefix)/'bin/lean')
    lean_path = query([args.lake, 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ)
    env['LEAN_PATH'] = str(objects) + os.pathsep + lean_path
    version = query([lean, '--version'])
    if not re.search(r'Lean \(version 4\.32\.0[,)]', version):
        raise SystemExit(f'Expected Lean 4.32.0; found {version}')
    records = []

    def run(tag, command, source=None, cwd=workspace, check_axioms=False):
        started = time.perf_counter()
        proc = subprocess.run(command, cwd=cwd, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.perf_counter() - started
        log = out/(tag+'.log')
        log.write_text(proc.stdout)
        axiom_sets = [set(x.strip() for x in group.split(',') if x.strip())
                      for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]',
                                              proc.stdout, re.S)]
        unexpected = sorted(set().union(*axiom_sets)-ALLOWED_AXIOMS) if axiom_sets else []
        success = proc.returncode == 0 and not unexpected and 'sorryAx' not in proc.stdout
        if check_axioms and 'depends on axioms:' not in proc.stdout and 'does not depend on any axioms' not in proc.stdout:
            success = False
        record = dict(tag=tag, command=command, cwd=str(cwd), exit_code=proc.returncode,
                      elapsed_seconds=elapsed, success=success, log=log.name,
                      log_sha256=digest(log), unexpected_axioms=unexpected,
                      axiom_sets=[sorted(group) for group in axiom_sets],
                      axiom_free_reports=proc.stdout.count('does not depend on any axioms'))
        if source is not None:
            record.update(source=str(source), source_sha256=digest(source))
        records.append(record)
        (out/'validation.json').write_text(json.dumps(dict(base_commit=BASE,
            lean_version=version, mathlib_commit=mathlib_actual,
            note='Individual elapsed times are not a controlled benchmark.',
            runs=records), indent=2)+'\n')
        print(f'{tag}: {"PASS" if success else "FAIL"} ({elapsed:.2f}s)', flush=True)
        if not success:
            print(proc.stdout, file=sys.stderr)
            raise SystemExit(f'Replay failed: {tag}; see {log}')

    for patch in sorted((bundle/'patches').glob('*.patch')):
        run('patch-'+patch.stem, ['git', 'apply', '--check', str(patch)], patch, repo)

    names = ['ArithmeticRefactors', 'FinitePushforward', 'ScannerCore',
             'RepresentationNaturality', 'ListLookup', 'RotationRefactors']
    for name in names:
        source = bundle/'Lean/ProofSimplification'/(name+'.lean')
        output = objects/'ProofSimplification'/(name+'.olean')
        run(name, [lean, '-M6000', '-j1', '-R', str(bundle/'Lean'),
                   '-o', str(output), str(source)], source, check_axioms=True)

    audits = {
        'Representation': ['DiophantineConsistency.Rep.reindex',
                           'DiophantineConsistency.Rep.conjunction',
                           'DiophantineConsistency.Rep.disjunction'],
        'NativeCoefficientBounds': [
            'DiophantineConsistency.NativeCoefficientBounds.abs_rowCoefficient_le_envelope',
            'DiophantineConsistency.NativeCoefficientBounds.weighted_rowCoefficient_lt_published'],
    }
    for name, declarations in audits.items():
        source = bundle/'patched'/(name+'.lean')
        audit = out/(name+'Audit.lean')
        audit.write_text(source.read_text()+'\n'+''.join(
            '#print axioms '+declaration+'\n' for declaration in declarations))
        run(name+'-complete-module', [lean, '-M6000', '-j1', str(audit)],
            source, check_axioms=True)
    print('All supplied checks passed; no repository source was changed.', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
