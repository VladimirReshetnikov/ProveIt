#!/usr/bin/env python3
"""Check the four standalone Lean kernels in a pinned ProveIt/Lake environment.

Usage: python3 scripts/verify_kernels.py /path/to/ProveIt
The supplied checkout is not edited. Its pinned dependencies must be installed.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = 'leanprover/lean4:v4.32.0'
MATHLIB = '81a5d257c8e410db227a6665ed08f64fea08e997'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo', type=Path)
    parser.add_argument('--inside-lake', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    repo = args.repo.resolve()
    if (repo / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise SystemExit('Use the reviewed Lean 4.32.0 environment.')
    manifest = json.loads((repo / 'lake-manifest.json').read_text())
    if next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') != MATHLIB:
        raise SystemExit('Use the reviewed Mathlib revision.')
    if not args.inside_lake:
        subprocess.run(['lake', 'env', sys.executable, str(Path(__file__).resolve()),
                        str(repo), '--inside-lake'], cwd=repo, check=True)
        return
    subprocess.run(['lean', '--version'], cwd=repo, check=True)
    with tempfile.TemporaryDirectory(prefix='proveit-proof-kernels-') as directory:
        output = Path(directory)
        environment = os.environ.copy()
        environment['LEAN_PATH'] = str(output) + os.pathsep + environment.get('LEAN_PATH', '')
        targets = [ROOT/'lean/FixedPointCore.lean', ROOT/'lean/GammaCertificate.lean',
                   ROOT/'lean/ResetLocality.lean', ROOT/'lte/FullLTESpectrum.lean']
        for target in targets:
            command = ['lean', '--root='+str(target.parent), str(target)]
            if target.name == 'FixedPointCore.lean':
                command.extend(['-o', str(output/'FixedPointCore.olean')])
            print('Checking', target.relative_to(ROOT), flush=True)
            result = subprocess.run(command, cwd=repo, env=environment,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(result.stdout, end='', flush=True)
            if result.returncode:
                raise SystemExit(result.returncode)
            if 'sorryAx' in result.stdout or 'declaration uses' in result.stdout:
                raise SystemExit('An admitted proof was detected.')
    print('PASS: all four standalone kernels. Repository adapters were not checked.')


if __name__ == '__main__':
    main()
