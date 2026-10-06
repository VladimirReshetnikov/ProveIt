#!/usr/bin/env python3
"""Verify the byte-preserved, original authored sources against freeze receipts."""
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
import verify_manifest as manifest

ROOT = Path(__file__).absolute().parent
EXPECTED = frozenset(('code/check_fixed_permanent.py', 'code/certify_constants.py',
                      'code/test_certified_guards.py', 'code/constant_certificate.json',
                      'certificates/exact_checks.json', 'optional/audit_counts.cpp',
                      'optional/audit_counts.tsv', 'optional/audit_blocks.cpp',
                      'optional/audit_block_counts.tsv'))


def verify(root=ROOT):
    root = manifest.check_directory(root)
    data = manifest.load_json(manifest.read_regular(root/'data/FROZEN_SOURCE_HASHES.json'))
    manifest.need(data.get('frozen_at_utc') == '2026-10-03T22:10:00Z', 'unexpected freeze timestamp')
    files = data.get('files')
    manifest.need(isinstance(files, dict) and set(files) == EXPECTED, 'frozen source inventory mismatch')
    for name, wanted in files.items():
        manifest.safe_name(name)
        path = root/name
        manifest.check_directory(path.parent)
        content = manifest.read_regular(path)
        manifest.need(isinstance(wanted, dict) and set(wanted) == {'bytes', 'sha256'}, 'invalid frozen receipt')
        manifest.need(type(wanted['bytes']) is int and wanted['bytes'] >= 0
                      and len(content) == wanted['bytes'], 'frozen source length differs: '+name)
        manifest.need(hashlib.sha256(content).hexdigest() == wanted['sha256'], 'frozen source hash differs: '+name)
    return {'status': 'PASS', 'frozen_original_files_checked': len(files),
            'freeze_timestamp_utc': data['frozen_at_utc']}


if __name__ == '__main__':
    try:
        print(json.dumps(verify(), sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        sys.exit(1)
