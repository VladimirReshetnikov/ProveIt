#!/usr/bin/env python3
"""Offline read-only source, patch, accounting and finite-model replay. Not Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def integrity():
    expected = json.loads((ROOT/'MANIFEST.json').read_text(encoding='utf-8'))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in ROOT.rglob('*')
              if p.is_file() and p.relative_to(ROOT).as_posix() != 'MANIFEST.json'
              and '__pycache__' not in p.parts}
    require(actual == expected, 'Integrity mismatch: changed, missing, or unlisted file')
    return len(expected)

def main():
    sealed = integrity()
    binding = json.loads((ROOT/'evidence/git_source_bindings.json').read_text(encoding='utf-8'))
    require(binding['count'] == len(binding['files']) == 702, 'Wrong main-source census')
    for row in binding['files']:
        raw = (ROOT/'baseline'/row['path']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == row['sha256'], 'Wrong source: '+row['path'])
        blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob == row['git_blob_sha1'], 'Wrong Git source binding: '+row['path'])
    results = []
    for script in ['safety/verify_safety.py', 'population/checks/audit_population.py',
                   'rephase/verify.py', 'audit/check_integrated.py']:
        command = [sys.executable, '-X', 'utf8', '-B']
        if sys.flags.optimize:
            command.append('-O')
        command.append(str(ROOT/script))
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, encoding='utf-8')
        require(run.returncode == 0, script+'\n'+run.stdout+run.stderr)
        results.append({'script': script, 'result': json.loads(run.stdout)})
    integrity()
    print(json.dumps({'status':'PASS_STATIC_FINITE_REPLAY_NOT_LEAN',
                      'optimized_python':bool(sys.flags.optimize),
                      'sealed_files_unchanged':sealed, 'main_sources_checked':702,
                      'stages':len(results), 'checks':results,
                      'not_run':['Lean elaboration','kernel checking','axiom comparison','performance benchmarks']},
                     indent=2))

if __name__ == '__main__':
    main()
