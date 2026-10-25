#!/usr/bin/env python3
"""Verify the literal deliverables and their finite source transformations.

This is not a solver and does not replace the unbounded mathematical proofs.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(args):
    done = subprocess.run([sys.executable, '-B', *args], cwd=ROOT, text=True, capture_output=True)
    if done.returncode:
        raise RuntimeError(done.stdout + done.stderr)
    return {'command': args, 'exit_code': done.returncode, 'stdout': done.stdout[-12000:]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    src = ROOT / 'direct/equation/equation.json'
    data = json.loads(src.read_text())
    poly = defaultdict(int)
    for row in data['residuals']:
        for c, a in row['terms']:
            for d, b in row['terms']:
                poly[tuple(sorted(a + b))] += c * d
    poly = {m: c for m, c in poly.items() if c}
    expected = json.loads((src.parent / 'expanded_polynomial.json').read_text())
    if poly != {tuple(m): c for c, m in expected['terms']}:
        raise ValueError('Collected quartic mismatch')
    metrics = {'variables': len(data['variables']), 'rows': len(data['residuals']),
               'degree': max(map(len, poly)), 'monomials': len(poly),
               'height': max(map(abs, poly.values())), 'constant_coefficient': poly.get((), 0)}
    if metrics != {'variables': 245, 'rows': 181, 'degree': 4, 'monomials': 5304, 'height': 128446, 'constant_coefficient': 2348}:
        raise ValueError(('Metrics mismatch', metrics))
    spec = importlib.util.spec_from_file_location('appendix', ROOT / 'report/generate_appendix.py')
    appendix = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(appendix)
    _, tex, text = appendix.generate()
    if tex != (ROOT / 'report/residuals.tex').read_text():
        raise ValueError('Typeset residual specification mismatch')
    if text != (src.parent / 'residuals.txt').read_text():
        raise ValueError('Plaintext residual specification mismatch')
    commands = [run(['direct/code/verify.py']), run(['-O', 'direct/code/verify.py'])]
    if args.rebuild:
        commands.append(run(['direct/code/verify.py', '--rebuild']))
    if (ROOT / 'compact/verify.py').exists():
        commands.append(run(['compact/verify.py']))
        commands.append(run(['-O', 'compact/verify.py']))
    manifest = ROOT / 'MANIFEST_SHA256.json'
    count = 0
    if manifest.exists():
        for path, digest in json.loads(manifest.read_text()).items():
            if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
                raise ValueError('Manifest mismatch: ' + path)
            count += 1
    result = {'status': 'PASS', 'scope': 'finite polynomial, source transformation, printed appendix and file identities',
              'direct_metrics': metrics, 'manifest_files': count, 'component_checks': commands}
    if args.receipt:
        args.receipt.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
