#!/usr/bin/env python3
"""Exercise fail-closed integrity checks on temporary package copies."""
import sys
sys.dontwritebytecode = True
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import verify

ROOT = Path(__file__).resolve().parent


def reseal(root):
    inventory = verify.snapshot(root)
    inventory['files'] = {k: v for k, v in inventory['files'].items()
                          if k not in ('INVENTORY.json', 'INVENTORY.sha256')}
    inventory['schema'] = 'native-degree-law-inventory-v1'
    data = (json.dumps(inventory, indent=2, sort_keys=True) + '\n').encode()
    (root / 'INVENTORY.json').write_bytes(data)
    (root / 'INVENTORY.sha256').write_text(hashlib.sha256(data).hexdigest() + '\n')


def alter(root, name):
    path = root / name
    data = bytearray(path.read_bytes())
    data[len(data) // 2] ^= 1
    path.write_bytes(data)


def missing_pin(root):
    path = root / 'INPUT_PINS.json'
    pins = verify.read(path)
    del pins['native_history_proof.md']
    path.write_text(json.dumps(pins))
    reseal(root)


def false_pin(root):
    path = root / 'INPUT_PINS.json'
    pins = verify.read(path)
    pins['native_history_proof.md'] = '0' * 64
    path.write_text(json.dumps(pins))
    reseal(root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        resolved = args.output.resolve()
        verify.need(resolved != ROOT and ROOT not in resolved.parents,
                    'Output must be outside this reproducibility directory')
    before = verify.snapshot(ROOT)
    verify.verify_integrity(ROOT)
    tests = [
        ('changed_raw_dag', lambda r: alter(r, 'data/native_backend_small_0.bin')),
        ('changed_source_python_data', lambda r: alter(r, 'data/native_history.py.txt')),
        ('missing_native_proof', lambda r: (r / 'data/native_history_proof.md').unlink()),
        ('changed_native_proof', lambda r: alter(r, 'data/native_history_proof.md')),
        ('missing_pin_even_after_inventory_reseal', missing_pin),
        ('false_pin_even_after_inventory_reseal', false_pin),
        ('changed_checker', lambda r: alter(r, 'checks/check_native_law.py')),
        ('changed_reference_certificate', lambda r: alter(r, 'certificates/independent_certificate.json')),
        ('extra_file', lambda r: (r / 'unexpected.txt').write_text('unexpected')),
        ('extra_empty_directory', lambda r: (r / 'unexpected').mkdir()),
        ('symlink', lambda r: (r / 'unexpected-link').symlink_to('README.md')),
        ('bad_inventory_digest', lambda r: alter(r, 'INVENTORY.sha256')),
    ]
    outcomes = []
    with tempfile.TemporaryDirectory(prefix='degree-law-integrity-') as work:
        work = Path(work)
        for label, mutate in tests:
            target = work / label
            shutil.copytree(ROOT, target)
            mutate(target)
            try:
                verify.verify_integrity(target)
            except (RuntimeError, ValueError, KeyError, UnicodeError):
                outcomes.append({'test': label, 'status': 'REJECTED_AS_EXPECTED'})
            else:
                raise RuntimeError('Mutation was not rejected: ' + label)
        empty = work / 'explicit-empty-universal-source'
        empty.mkdir()
        try:
            verify.universal(empty)
        except RuntimeError as exc:
            verify.need('Missing mandatory universal input:' in str(exc), 'Unexpected optional-source failure')
            outcomes.append({'test': 'missing_mandatory_universal_source', 'status': 'REJECTED_AS_EXPECTED'})
        else:
            raise RuntimeError('Missing universal source was not rejected')
    verify.need(verify.snapshot(ROOT) == before, 'Original package changed during mutation tests')
    result = {'status': 'PASS', 'tests': outcomes, 'count': len(outcomes),
              'python_optimized': bool(sys.flags.optimize), 'original_package_unchanged': True}
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc).replace(str(ROOT), '.')}), file=sys.stderr)
        sys.exit(1)
