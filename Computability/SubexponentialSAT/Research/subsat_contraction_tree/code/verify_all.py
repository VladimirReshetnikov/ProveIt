#!/usr/bin/env python3
"""Offline exact checks for the released research packet; no SAT solver is run."""
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]

def run_script(name, *extra):
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O')
    command += [str(ROOT / 'code' / name), *map(str, extra)]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(name + ' failed:\n' + result.stdout + result.stderr)
    return json.loads(result.stdout)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--original', type=Path,
                        help='Optional unchanged joint_cauchy.py from the pinned archive.')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    extra = []
    if args.original:
        source = args.original.resolve()
        record = json.loads((ROOT/'provenance/prefix_baseline.json').read_text())
        if hashlib.sha256(source.read_bytes()).hexdigest() != record['member_sha256']:
            raise RuntimeError('Optional original source does not match the pinned SHA-256.')
        extra = ['--original', source]
    prefix = run_script('verify_prefix.py', *extra)
    cached = run_script('check_cached_tree.py')
    binary = run_script('verify_binary_merges.py')
    expected_cached = json.loads((ROOT/'results/cached_tree_checks.json').read_text())
    expected_binary = json.loads((ROOT/'results/binary_merges_verification.json').read_text())
    if cached != expected_cached or binary != expected_binary:
        raise RuntimeError('Replayed exact proof checks differ from the release ledger.')
    expected_prefix = json.loads((ROOT/'results/prefix_verification.json').read_text())
    for key, value in expected_prefix.items():
        if key == 'fraction_feature_values' and not args.original:
            continue
        if prefix.get(key) != value:
            raise RuntimeError('Prefix check mismatch: ' + key)
    result = {'status':'passed', 'prefix':prefix, 'cached_certificate':cached,
              'independent_binary_and_CRT':binary,
              'optional_pinned_rational_baseline_checked':bool(args.original),
              'scope':'Exact local identities, finite interfaces, and schedule certificates; no complete SAT solver.'}
    text = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')

if __name__ == '__main__':
    main()
