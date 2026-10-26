#!/usr/bin/env python3
"""Check the four standalone Lean modules; no network or installation steps."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lean', default=shutil.which('lean'))
parser.add_argument('--out-dir', type=Path, default=root / 'evidence' / 'checks')
args = parser.parse_args()
if not args.lean:
    parser.error('Lean was not found. Install Lean 4.32.0 or pass --lean.')
version = subprocess.run([args.lean, '--version'], text=True, capture_output=True, check=True).stdout.strip()
if 'version 4.32.0,' not in version:
    parser.error('Expected Lean 4.32.0; found: ' + version)
args.out_dir.mkdir(parents=True, exist_ok=True)
result = {'compiler': version, 'scope': 'standalone Std-only kernels; no ProveIt build', 'files': []}
failed = False
for path in sorted((root / 'lean').glob('*.lean')):
    source = path.read_text(encoding='utf-8')
    # Our source comments are nonnested; this scan is an additional audit only.
    code = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    forbidden = re.findall(r'\b(?:sorry|admit|native_decide|unsafe)\b|^\s*axiom\s', code, flags=re.M)
    if forbidden:
        raise SystemExit(f'Forbidden declaration/tactic in {path.name}: {forbidden}')
    proc = subprocess.run([args.lean, str(path)], cwd=root, capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    (args.out_dir / (path.stem + '.log')).write_text(output, encoding='utf-8')
    entry = {'file': str(path.relative_to(root)),
             'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
             'exit_code': proc.returncode,
             'axiom_output': [line for line in output.splitlines() if 'axioms' in line],
             'log': path.stem + '.log'}
    result['files'].append(entry)
    print(f'{path.name}: exit {proc.returncode}')
    if proc.returncode:
        failed = True
        print(output)
result['all_passed'] = not failed
(args.out_dir / 'lean_verification.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
raise SystemExit(1 if failed else 0)
