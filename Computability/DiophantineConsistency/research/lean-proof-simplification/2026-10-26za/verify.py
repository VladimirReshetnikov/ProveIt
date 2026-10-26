#!/usr/bin/env python3
"""Offline, read-only artifact/source/finite replay. Never invokes Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PREFIX = 'Computability/DiophantineConsistency/Lean/'

def require(ok, reason):
    if not ok:
        raise RuntimeError(reason)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def integrity():
    expected = json.loads((ROOT / 'MANIFEST.json').read_text(encoding='utf-8'))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in ROOT.rglob('*')
              if p.is_file() and p.relative_to(ROOT).as_posix() != 'MANIFEST.json'
              and '__pycache__' not in p.parts}
    require(actual == expected, 'Artifact integrity mismatch: changed, missing, or unlisted file')
    return len(expected)

def main():
    sealed = integrity()
    inventory = json.loads((ROOT / 'evidence/inventory.json').read_text(encoding='utf-8'))
    sources = [r for r in inventory['files'] if r['path'].startswith(PREFIX)]
    require(len(sources) == 608, 'Unexpected source census')
    for row in sources:
        require(sha(ROOT / 'baseline' / row['path']) == row['sha256'],
                'Pinned source mismatch: ' + row['path'])
    checks = []
    for script in ['strip/verify_static.py', 'row/audit_receiver_causality.py',
                   'row/audit_combined_row.py', 'machine/audit.py',
                   'audit/verify_integrated.py']:
        command = [sys.executable, '-X', 'utf8', '-B']
        if sys.flags.optimize:
            command.append('-O')
        command.append(str(ROOT / script))
        result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                text=True, encoding='utf-8')
        require(result.returncode == 0, script + '\n' + result.stdout + result.stderr)
        checks.append({'script': script, 'exit_code': 0,
                       'output': json.loads(result.stdout)})
    integrity()
    print(json.dumps({'status': 'PASS_STATIC_REPLAY_NOT_LEAN',
                      'optimized_python': bool(sys.flags.optimize),
                      'sealed_files_unchanged': sealed,
                      'pinned_main_Lean_files_checked': len(sources),
                      'successful_stages': len(checks), 'checks': checks,
                      'scope': 'Archive integrity, textual source/patch checks and finite models. '
                               'No elaboration, kernel validation, axiom comparison or benchmark.'},
                     indent=2))

if __name__ == '__main__':
    main()
