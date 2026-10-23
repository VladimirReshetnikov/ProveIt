#!/usr/bin/env python3
"""Check packaged source/receipt bindings; do not invoke a proof assistant."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(test, message):
    if not test:
        raise SystemExit(message)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path)
    args = ap.parse_args()
    pins = json.loads((ROOT/'source_bindings.json').read_text())
    for row in pins['files']:
        require(digest((ROOT/row['delivered_path']).read_bytes()) == row['sha256'],
                'Pinned input mismatch: '+row['delivered_path'])
        if args.repo:
            require(digest((args.repo/row['repo_path']).read_bytes()) == row['sha256'],
                    'Repository input mismatch: '+row['repo_path'])
    ncheck = (ROOT/'deps/K215F/NormalizedBisim.v').read_text()
    block = ncheck[ncheck.index('Fixpoint allzero'):ncheck.index('Definition branch_ok')]
    require((ROOT/'PathEq.v').read_text().endswith(block), 'Path utilities changed.')
    require(digest(block.encode()) == pins['path_utilities_sha256'],
            'Path utility binding changed.')

    final = ROOT/'evidence/final'
    receipt = json.loads((final/'result.json').read_text())
    require(receipt['complete'] and receipt['recursive_audit'] == 'passed',
            'Final compiler/audit receipt is not complete.')
    require(receipt['driver_sha256'] == digest((ROOT/'build.py').read_bytes()),
            'Build driver differs from the accepted receipt.')
    for row in receipt['sources']:
        raw = (ROOT/row['delivered']).read_bytes()
        require(digest(raw) == row['delivered_sha256'],
                'Delivered source mismatch: '+row['module'])
        if row['module'] == 'deps/K230/RMEquiv.v' and receipt['compatibility_import']:
            needle = b'From K230 Require Import RM.'
            require(raw.count(needle) == 1, 'Compatibility import ambiguous.')
            raw = raw.replace(needle, needle+b'\nRequire Import Compat818.')
        require(digest(raw) == row['compiled_sha256'],
                'Compiler source binding mismatch: '+row['module'])
    audit_seen = False
    for row in receipt['checks']:
        log = final/'logs'/(row['name'].replace('/', '_')+'.log')
        require(row['exit_code'] == 0, 'Failed record in final selection.')
        require(digest(log.read_bytes()) == row['log_sha256'],
                'Log mismatch: '+row['name'])
        text = log.read_text()
        require(text.count('Closed under the global context') == row['closed_reports'],
                'Assumption count mismatch: '+row['name'])
        if row['name'] == 'recursive_SourceClient':
            audit_seen = True
            require(row['argv'][-1] == 'SourceClient', 'Unexpected recursive target.')
            require('-admit' not in row['argv'] and '-norec' not in row['argv'],
                    'Incomplete recursive audit command.')
    require(audit_seen, 'No recursive concrete-client record.')

    metrics = json.loads((ROOT/'source_metrics.json').read_text())
    selected = metrics['direct_checked_lookup']
    total_bytes = total_lines = 0
    for row in selected['files']:
        name = row['path'].removeprefix('contribution/rocq/')
        raw = (ROOT/name).read_bytes()
        require(digest(raw) == row['sha256'], 'Selected metric source mismatch: '+name)
        total_bytes += len(raw)
        total_lines += len(raw.decode().splitlines())
    require((total_bytes, total_lines) == (selected['bytes'], selected['lines']),
            'Selected source metrics mismatch.')
    print('PASS_SOURCE_AND_EVIDENCE_BINDINGS')
    print('This verifies packaged identities and recorded outcomes, not a new proof-kernel run.')


if __name__ == '__main__':
    main()
