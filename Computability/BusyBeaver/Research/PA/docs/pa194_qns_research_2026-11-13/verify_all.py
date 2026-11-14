#!/usr/bin/env python3
"""Verify the complete PA194QNS delivery without a checkout or network.

Default: both universal physical engines. --quick: exact reconstruction,
fold/startup/source/novelty checks only, with that narrower scope explicit.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def integrity():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for entry in manifest['files']:
        path = ROOT / entry['path']
        data = path.read_bytes()
        assert len(data) == entry['bytes'], ('Length mismatch', entry['path'])
        assert hashlib.sha256(data).hexdigest() == entry['sha256'], ('Hash mismatch', entry['path'])
    return len(manifest['files'])


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Assertions must remain enabled: remove -O / PYTHONOPTIMIZE.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--receipt', type=Path, help='Optional new receipt outside the distributed files.')
    args = parser.parse_args()
    count = integrity()
    print(f'PASS: integrity of {count} distributed files.', flush=True)
    print('Reconstructing and checking PA194QNS' + (' (quick scope).' if args.quick else ' (both universal engines).'), flush=True)
    with tempfile.TemporaryDirectory(prefix='pa194qns-delivery-') as tmp:
        receipt = Path(tmp) / 'construction.json'
        command = [sys.executable, '-B', str(ROOT / 'construction/verify_all.py'), '--receipt', str(receipt)]
        if args.quick:
            command.append('--quick')
        process = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if process.returncode:
            print(process.stdout)
            raise SystemExit(process.returncode)
        construction = json.loads(receipt.read_text())
        assert construction['status'] == 'PASS'
        assert construction['regenerated_bytes_equal']
        spec = importlib.util.spec_from_file_location('exchange_certificate', ROOT / 'proofs/exchange_certificate.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        published = (ROOT / 'proofs/exchange_certificate.json').read_bytes()
        exchange = module.verify(json.loads(published))
        regenerated = (json.dumps(module.make_certificate(), indent=2) + '\n').encode()
        assert regenerated == published, 'Exchange certificate regeneration differs'
        result = dict(
            status='PASS', integrity_files=count,
            full_physical_replay=not args.quick,
            regenerated_principal_table_exact=True,
            dense_sha256=hashlib.sha256((ROOT / 'construction/machine/machine.tm').read_bytes()).hexdigest(),
            source_equivalence=construction['source_equivalence'],
            compared_existing_194_classes=construction['novelty']['compared_same_size_classes'],
            absent_from_corpus=construction['novelty']['absent_from_corpus'],
            exchange_certificate=exchange,
            kernel_checked=False,
            scope='Executable construction and certificates; ordinary PA calibration is the attributed mathematical dependency.')
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
