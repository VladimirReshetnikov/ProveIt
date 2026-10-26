#!/usr/bin/env python3
"""Replay all three mathematical components with Python's standard library.

This checks exact finite artifacts. It neither searches for zeros nor proves
the inherited unbounded mathematical calibration by running examples.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CHECKS = (
    ('quartic_coefficients_and_commutation', 'quartic/verify_affine_horizons.py', ()),
    ('compact_positive_equations', 'compact/verify.py', ()),
    ('compact_integer_domain', 'compact/verify_integer.py', ()),
    ('complete_fixed_coefficients', 'compact/rebuild_coefficients.py', ()),
    ('direct_pooling_and_projections', 'direct/verify.py', ()),
    ('printed_quartic_definition', 'report/emit_quartic_appendix.py', ('--check',)),
)


def check_manifest(skip=False):
    manifest = ROOT / 'SHA256SUMS'
    if skip:
        return {'status': 'SKIPPED', 'reason': 'explicit --skip-manifest'}
    if not manifest.is_file():
        return {'status': 'NOT_PRESENT', 'reason': 'manifest not yet created'}
    count = 0
    seen = set()
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, relative = line.split('  ', 1)
        if relative in seen or len(digest) != 64:
            raise ValueError('Malformed manifest')
        seen.add(relative)
        path = (ROOT / relative).resolve()
        if ROOT not in path.parents:
            raise ValueError('Unsafe manifest path')
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError('Manifest mismatch: ' + relative)
        count += 1
    return {'status': 'PASS', 'files': count}


def run_check(spec):
    name, relative, arguments = spec
    script = ROOT / relative
    flags = ['-O'] if sys.flags.optimize else []
    command = [sys.executable, *flags, '-B', str(script), *arguments]
    child = subprocess.run(command, cwd=script.parent, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if child.returncode:
        raise RuntimeError(name + ':\n' + child.stdout + '\n' + child.stderr)
    try:
        receipt = json.loads(child.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(name + ': child did not produce a JSON receipt\n' + child.stdout) from error
    if name == 'compact_positive_equations':
        individual = receipt.get('checks', [])
        if len(individual) != 3 or any(item.get('status') != 'PASS' for item in individual):
            raise RuntimeError(name + ': one of the three positive equations failed')
        receipt['status'] = 'PASS'
    if receipt.get('status') != 'PASS':
        raise RuntimeError(name + ': non-PASS receipt')
    if child.stderr:
        receipt['stderr'] = child.stderr
    return name, receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true',
                        help='Check mathematics after deliberate edits or a local PDF rebuild.')
    parser.add_argument('--receipt', type=Path,
                        help='Write the full JSON receipt to this explicitly chosen path.')
    args = parser.parse_args()
    manifest = check_manifest(args.skip_manifest)
    with ThreadPoolExecutor(max_workers=3) as pool:
        results = dict(pool.map(run_check, CHECKS))
    receipt = {
        'status': 'PASS',
        'optimized_interpreter': bool(sys.flags.optimize),
        'optimized_flag_propagated_to_children': bool(sys.flags.optimize),
        'final_equations': {'quartic': 2, 'compact_positive': 3,
                            'compact_unrestricted_integer': 1, 'direct_pooled': 8},
        'manifest': manifest,
        'checks': results,
        'scope': ('Exact finite coefficients, circuits, transformations, source bindings, '
                  'integer-domain lift, and printed residuals. Unbounded soundness and '
                  'completeness use the ordinary mathematical proofs and named inherited '
                  'calibration; no zero search or new end-to-end proof-assistant check.'),
    }
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps({
        'status': receipt['status'],
        'optimized_interpreter': receipt['optimized_interpreter'],
        'final_equations': receipt['final_equations'],
        'manifest': manifest,
        'checks': {name: result['status'] for name, result in results.items()},
        'scope': receipt['scope'],
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, RuntimeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
