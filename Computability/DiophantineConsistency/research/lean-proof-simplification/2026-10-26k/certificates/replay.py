#!/usr/bin/env python3
"""Compile the standalone certificate, its checks, and optionally check the patch."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--lean', required=True, type=Path)
parser.add_argument('--repo', type=Path)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
here = Path(__file__).resolve().parent
out = (args.output or here / 'replay-results').resolve()
out.mkdir(parents=True, exist_ok=True)
lean = args.lean.resolve()
version = subprocess.run([str(lean), '--version'], capture_output=True, text=True, check=True).stdout.strip()
if 'version 4.32.0' not in version:
    raise SystemExit('Expected Lean 4.32.0, got ' + version)
records = []

def run(label, command, env=None):
    result = subprocess.run(command, capture_output=True, text=True, env=env, cwd=here)
    (out / (label + '.log')).write_text(result.stdout + result.stderr)
    records.append(dict(label=label, command=command, exit_code=result.returncode,
        log=label + '.log'))
    if result.returncode:
        raise RuntimeError(label + ' failed; inspect ' + str(out / (label + '.log')))

try:
    with tempfile.TemporaryDirectory(prefix='arithmetic-certificates-') as directory:
        build = Path(directory)
        module = build / 'DiophantineConsistency/ArithmeticCertificates.olean'
        module.parent.mkdir(parents=True)
        run('helper', [str(lean), '-o', str(module),
            str(here / 'lean/DiophantineConsistency/ArithmeticCertificates.lean')])
        env = dict(os.environ, LEAN_PATH=str(build))
        run('checks', [str(lean), str(here / 'lean/ArithmeticCertificatesChecks.lean')], env)
    if args.repo:
        commit = subprocess.run(['git', '-C', str(args.repo), 'rev-parse', 'HEAD'],
            capture_output=True, text=True, check=True).stdout.strip()
        if commit != '6175dff9a15491497c7a3c1bda4f6a62a6349c74':
            raise RuntimeError('Unexpected source commit: ' + commit)
        run('patch-check', ['git', '-C', str(args.repo), 'apply', '--check',
            str(here / 'patches/arithmetic-certificates.patch')])
finally:
    result = dict(lean_version=version, runs=records,
        scope='Standalone helper and exact-type wrappers; production backend modules not rebuilt.',
        baseline='6175dff9a15491497c7a3c1bda4f6a62a6349c74')
    (out / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
