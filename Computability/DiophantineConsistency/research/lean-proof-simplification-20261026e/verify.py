#!/usr/bin/env python3
"""Verify the delivered archive's bytes and static evidence, not Lean proofs."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def fail(message):
    raise SystemExit(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_manifest():
    expected = json.loads((ROOT / 'MANIFEST.json').read_text())
    actual = {p.relative_to(ROOT).as_posix(): digest(p)
              for p in ROOT.rglob('*') if p.is_file()
              and p.relative_to(ROOT).as_posix() != 'MANIFEST.json'
              and '__pycache__' not in p.parts}
    if actual != expected:
        fail('Artifact integrity mismatch: missing, changed, or unlisted files')
    return len(expected)

def main():
    sealed = check_manifest()
    baseline = ROOT / 'baseline'
    expected = json.loads((ROOT / 'evidence/inventory.json').read_text())
    rows = [r for r in expected['files'] if '/Lean/' in r['path']]
    for row in rows:
        p = baseline / row['path']
        if not p.is_file() or digest(p) != row['sha256']:
            fail('Pinned Lean baseline mismatch: ' + row['path'])
    commands = [
        [sys.executable, '-B', str(ROOT / 'algebra_examples/audit_candidates.py'),
         '--baseline', str(baseline)],
        [sys.executable, '-B', str(ROOT / 'prototypes/native/check_native_regressions.py')],
    ]
    results = []
    for command in commands:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            fail(result.stdout + result.stderr)
        result_json = json.loads(result.stdout)
        results.append({'script': Path(command[2]).name, 'exit_code': 0,
                        'output': result_json})
    patch = ROOT / 'checker_examples/standard_library_cleanup.patch'
    result = subprocess.run(['git', 'apply', '--check', str(patch)], cwd=baseline,
                            capture_output=True, text=True)
    if result.returncode:
        fail(result.stdout + result.stderr)
    results.append({'script': 'git apply --check standard_library_cleanup.patch',
                    'exit_code': 0})
    check_manifest()
    print(json.dumps({'status': 'PASS', 'sealed_files_unchanged': sealed,
                      'pinned_Lean_files_checked': len(rows),
                      'checks': results,
                      'scope': 'Archive integrity, exact source/patch audits, and finite sanity '
                               'checks only. This command does not run Lean or validate proofs.'},
                     indent=2))

if __name__ == '__main__':
    main()
