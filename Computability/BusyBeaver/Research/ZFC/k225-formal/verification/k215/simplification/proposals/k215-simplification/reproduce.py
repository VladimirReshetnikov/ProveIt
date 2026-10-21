#!/usr/bin/env python3
"""Audit released byte identities and replay inexpensive independent checks.

Proof-assistant compilation is intentionally explicit in the subpacket READMEs.
This driver never describes hash checking or Python execution as a kernel proof.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search', action='store_true',
                        help='Also freshly replay all six bounded state searches.')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Run with Python assertions enabled.')
    manifest = json.loads((HERE / 'manifest.json').read_text())
    for entry in manifest['files']:
        path = HERE / entry['path']
        content = path.read_bytes()
        if len(content) != entry['bytes']:
            raise SystemExit('Byte length mismatch: ' + entry['path'])
        if hashlib.sha256(content).hexdigest() != entry['sha256']:
            raise SystemExit('SHA-256 mismatch: ' + entry['path'])
    print(f"PASS: {len(manifest['files'])} released file identities", flush=True)
    search_command = [sys.executable, '-B', str(HERE / 'search214/reproduce.py')]
    if args.search:
        search_command.append('--search')
    subprocess.run(search_command, check=True)
    subprocess.run([sys.executable, '-B',
                    str(HERE / 'evidence/review_normalized_certificate.py')], check=True)
    result = json.loads((HERE / 'cm215/verification/result.json').read_text())
    if result['status'] != 'LEAN_KERNEL_PASS' or not result['repository_bridge_checked']:
        raise SystemExit('Unexpected retained CM215 verification status.')
    if any(m['exit_code'] != 0 for m in result['modules']):
        raise SystemExit('Retained CM215 record contains a failed module.')
    coq = json.loads((HERE / 'evidence/coq-result.json').read_text())
    if coq['status'] != 'COQ_KERNEL_AND_COQCHK_PASS':
        raise SystemExit('Unexpected retained Coq status.')
    normalized = json.loads((HERE / 'source_normalization/kernel_receipt.json').read_text())
    if not normalized['complete'] or any(m['exit_code'] != 0 for m in normalized['modules']):
        raise SystemExit('Unexpected retained normalized-source verification status.')
    print('PASS: retained verification records are internally consistent.')
    print('These checks are file/finite audits, not a fresh proof-assistant build.')
    print('Use the documented Lean and Coq commands for fresh kernel checks.')

if __name__ == '__main__':
    main()
