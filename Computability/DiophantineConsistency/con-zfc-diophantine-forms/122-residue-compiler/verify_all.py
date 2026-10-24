#!/usr/bin/env python3
"""Verify literal equations and certificates; optionally rebuild from pinned sources.

Python 3.10+ and its standard library are sufficient. This is finite algebraic
verification, not a proof search or a proof-assistant check of the ZFC theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
CODE = ROOT / 'code'
sys.path.insert(0, str(CODE))
from check_independent import check as check_literal
from check_transform import check as check_transform, pell_digits
from check_parity_structure import run as check_parity
from generate_equation_tex import verify_tex


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check():
    path = ROOT / 'MANIFEST.json'
    need(path.is_file(), 'MANIFEST.json is missing')
    data = json.loads(path.read_text())
    entries = data['files']
    for rel, info in entries.items():
        local = ROOT / rel
        need(local.resolve().is_relative_to(ROOT), 'manifest path escapes package')
        need(local.is_file(), 'missing file: ' + rel)
        need(local.stat().st_size == info['bytes'], 'byte-length mismatch: ' + rel)
        need(digest(local) == info['sha256'], 'SHA-256 mismatch: ' + rel)
    return {'status': 'all recorded files match', 'files': len(entries)}


def run_json(arguments):
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['CONZFC_ROUND14_ROOT'] = str(ROOT / 'vendor/round14')
    completed = subprocess.run([sys.executable, '-B'] + list(map(str, arguments)),
                               cwd=ROOT, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if completed.returncode:
        raise RuntimeError('Command failed: ' + ' '.join(map(str, arguments)) +
                           '\n' + completed.stdout + completed.stderr)
    return json.loads(completed.stdout)


def rebuild():
    result = {}
    with tempfile.TemporaryDirectory(prefix='conzfc-residue-rebuild-') as directory:
        target = Path(directory)
        run_json([CODE / 'release_332.py', '--output', target / 'natural332',
                  '--parent', ROOT / 'vendor/round14/architecture/derived16_cantor'])
        run_json([CODE / 'even_architecture.py', '--output', target / 'natural333',
                  '--modular', '--horizon', '12'])
        # These files bind the original graph, projection, collected coefficients,
        # and final coordinate order. Incidental receipt filenames are excluded.
        common = [
            'SUMMARY.json', 'raw/equation.json', 'raw/expanded_polynomial.json',
            'raw/raw_audit_input.json', 'raw/gate_ledger.json',
            'raw/macro_inventory.json', 'raw/local_majorant.json', 'raw/METRICS.json',
            'natural/equation.json', 'natural/expanded_polynomial.json',
            'natural/elimination_certificate.json', 'natural/VERIFICATION.json',
        ]
        for name in ('natural332', 'natural333'):
            selected = common + (['TRANSFORM.json', 'DEPENDENCIES.json']
                                 if name == 'natural332' else ['raw/parity_interface.json'])
            for rel in selected:
                a, b = ROOT / 'equations' / name / rel, target / name / rel
                need(a.read_bytes() == b.read_bytes(), 'rebuild differs: ' + name + '/' + rel)
            result[name] = {'status': 'byte-for-byte identical', 'compared_files': selected}
        # Recheck the sparse regenerated result with the independent routines too.
        check_literal(target / 'natural333')
        check_parity(target / 'natural333')
    return result


def check_printed_equations():
    result = {}
    for n in (332, 333):
        eq = json.loads((ROOT / 'equations' / ('natural' + str(n)) /
                         'natural/equation.json').read_text())
        count = verify_tex((ROOT / ('equation-' + str(n) + '.tex')).read_text(),
                           eq['residuals'])
        result[str(n)] = {'parsed_terms': count, 'status': 'every printed term matches JSON'}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true', help='replay both deterministic producers')
    parser.add_argument('--output', type=Path, help='optional JSON receipt; use a path outside the package')
    parser.add_argument('--skip-manifest', action='store_true', help='release preparation only: check mathematics before making manifest')
    args = parser.parse_args()
    result = {'scope': 'Exact finite algebra, structural checks and optional deterministic reproduction; ordinary unbounded proofs and inherited calibration are separate.'}
    result['manifest'] = {'status': 'skipped by explicit option'} if args.skip_manifest else manifest_check()
    small, sparse = ROOT / 'equations/natural332', ROOT / 'equations/natural333'
    result['natural332'] = check_literal(small, ROOT / 'vendor/round14/architecture/derived16_cantor')
    result['natural332_transform'] = check_transform(small)
    result['natural333'] = check_literal(sparse)
    result['natural333_structure'] = check_parity(sparse)
    result['natural333_separate_interface'] = run_json([CODE / 'audit_parity_interface.py', sparse])
    result['finite_regressions'] = pell_digits()
    result['printed_equations'] = check_printed_equations()
    if args.rebuild:
        result['rebuild'] = rebuild()
    result['status'] = 'passed'
    output = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output)


if __name__ == '__main__':
    main()
