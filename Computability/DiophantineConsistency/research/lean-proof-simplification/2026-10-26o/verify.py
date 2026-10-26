#!/usr/bin/env python3
"""Read-only release replay: source/patch/finite checks, never Lean compilation."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PREFIX = 'Computability/DiophantineConsistency/Lean/'

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def integrity():
    expected = json.loads((ROOT / 'MANIFEST.json').read_text())
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in ROOT.rglob('*')
              if p.is_file() and p.relative_to(ROOT).as_posix() != 'MANIFEST.json'
              and '__pycache__' not in p.parts}
    require(actual == expected, 'Release integrity mismatch: changed, missing, or unlisted file')
    return len(expected)

def run_script(relative, *args):
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O')
    command += [str(ROOT / relative), *map(str, args)]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    require(result.returncode == 0, relative + ': ' + result.stdout + result.stderr)
    return {'script': relative, 'exit_code': result.returncode,
            'output': json.loads(result.stdout)}

def main():
    sealed = integrity()
    inventory = json.loads((ROOT / 'evidence/inventory.json').read_text())
    baseline = ROOT / 'baseline'
    sources = [r for r in inventory['files'] if r['path'].startswith(PREFIX)]
    require(len(sources) == 574, 'Unexpected source census')
    for row in sources:
        require(sha(baseline / row['path']) == row['sha256'],
                'Pinned source mismatch: ' + row['path'])
    # Reference reports are evidence of prior proposals, not new results.
    ledger = json.loads((ROOT / 'catalog/exclusion_ledger.json').read_text())
    for doc in ledger['documents']:
        require(sha(ROOT / 'catalog' / doc['path']) == doc['sha256'],
                'Prior manuscript source mismatch: ' + doc['path'])
    late = json.loads((ROOT / 'catalog/late9bd/late_exclusion_ledger.json').read_text())
    for doc in late['documents']:
        for kind in ('tex', 'pdf'):
            require(sha(ROOT / 'catalog/late9bd' / doc[kind]) == doc[kind + '_sha256'],
                    'Late manuscript mismatch: ' + doc[kind])
    stages = [
        run_script('cyclic/regression.py'),
        run_script('cyclic/test_regression_controls.py'),
        run_script('wang/validation/measure_boundary_fibers.py', '--baseline', baseline),
        run_script('wang/validation/check_boundary_fibers.py', '--baseline', baseline),
        run_script('wang/validation/selftest_validators.py', '--baseline', baseline),
        run_script('audit/audit_static.py', '--baseline', baseline),
        run_script('audit/arithmetic_spotchecks.py'),
    ]
    integrity()
    print(json.dumps({'status': 'PASS_STATIC_REPLAY', 'optimized_python': bool(sys.flags.optimize),
                      'sealed_files_unchanged': sealed, 'pinned_Lean_sources_checked': len(sources),
                      'stages': stages, 'successful_stages': len(stages),
                      'scope': 'Artifact integrity, exact source/patch audits and finite sanity checks. '
                               'No Lean elaboration, kernel validation or performance benchmark.'}, indent=2))

if __name__ == '__main__':
    main()
