#!/usr/bin/env python3
"""Replay all new finite checks offline in an isolated temporary copy."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        import sympy
    except ImportError as err:
        raise SystemExit('Install requirements.txt before the complete audit; individual norm10 and positive11 verifiers use only the standard library.') from err
    manifest = ROOT / 'MANIFEST.sha256'
    checked = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, rel = line.split('  ', 1)
            path = ROOT / rel
            if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                raise SystemExit('Release file hash mismatch: ' + rel)
            checked += 1
    commands = [
        ('norm10', 'build.py'),
        ('norm10', 'verify.py'),
        ('norm10', 'audit_independent.py'),
        ('integer', 'build.py'),
        ('integer', 'check.py'),
        ('positive11', 'verify.py'),
        ('positive11', 'rebuild_coefficients.py'),
        ('alternative/gadgets', 'build_and_verify.py'),
        ('alternative/selector', 'build_and_verify.py'),
    ]
    results = []
    with tempfile.TemporaryDirectory(prefix='con_zfc_shears_') as temp:
        work = Path(temp)
        for component in ('norm10', 'integer', 'positive11', 'alternative'):
            shutil.copytree(ROOT / component, work / component,
                ignore=shutil.ignore_patterns('__pycache__', '*.pyc', '*.zip'))
        for component, script in commands:
            cmd = [sys.executable] + (['-O'] if args.optimized else []) + [script]
            process = subprocess.run(cmd, cwd=work / component,
                capture_output=True, text=True, timeout=180)
            item = {'component': component, 'script': script, 'returncode': process.returncode}
            results.append(item)
            if process.returncode:
                print(process.stdout[-5000:], file=sys.stderr)
                print(process.stderr[-5000:], file=sys.stderr)
                raise SystemExit('Failed: ' + component + '/' + script)
            print('PASS ' + component + '/' + script, flush=True)
        for component, glob in [('norm10', 'integer10_*.json'), ('integer/forms', '*.json')]:
            for original in (ROOT / component).glob(glob):
                rebuilt = work / component / original.name
                if original.read_bytes() != rebuilt.read_bytes():
                    raise SystemExit('Rebuilt literal differs: ' + str(original.relative_to(ROOT)))
    receipt = {'status': 'PASS', 'optimized': args.optimized,
        'python': sys.version.split()[0], 'sympy': sympy.__version__,
        'manifest_files_verified': checked, 'commands': results,
        'regenerated_norm_and_integer_literals_byte_identical': True,
        'scope': 'Finite exact algebra, coefficients, literal circuits, degree certificates and supplemental diagnostics. The universal semantic theorem is the manuscript with its named inherited dependencies.'}
    if args.output:
        args.output.resolve().write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
