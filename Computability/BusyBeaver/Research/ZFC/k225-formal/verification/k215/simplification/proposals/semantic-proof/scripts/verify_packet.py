#!/usr/bin/env python3
"""Verify delivered hashes and accepted source/log bindings, without compiling.

Run from any directory. An optional pinned --repo additionally checks repository
sources referenced by the accepted ledgers. This is an integrity check, not a
proof-assistant kernel check or a signature establishing artifact authenticity.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def within(root, relative):
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f'Path escapes root: {relative}')
    return path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument('--repo', type=Path)
    args = parser.parse_args()
    packet = args.packet.resolve()
    manifest = packet / 'SHA256SUMS'
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = within(packet, relative)
        require(path.is_file(), f'Missing: {relative}')
        require(sha(path) == expected, f'Digest mismatch: {relative}')
        count += 1

    summary = json.loads((packet/'evidence/verification_summary.json').read_text())
    repo = args.repo.resolve() if args.repo else None
    if repo:
        head = subprocess.check_output(
            ['git','-C',str(repo),'rev-parse','HEAD'], text=True).strip()
        require(head == summary['base_commit'], 'Repository is not at the pinned revision')

    bindings, repository_bindings = 0, 0
    for name, check in summary['checks'].items():
        require(check['status'] == 'PASS', f'Non-passing accepted check: {name}')
        ledger = json.loads(within(packet, check['ledger']).read_text())
        log_map = json.loads(within(packet, check['log_map']).read_text())
        require(ledger['status'] == 'PASS', f'Non-passing ledger: {name}')
        require(len(ledger['modules']) == len(log_map) == check['modules'],
                f'Module count mismatch: {name}')
        for raw, row in zip(ledger['modules'], log_map):
            for key in ['module','status','source_sha256','transitive_source_sha256']:
                require(raw[key] == row[key], f'Ledger binding mismatch: {name}/{key}')
            require(row['status'] in ('PASS','REUSED'), f'Rejected module: {row["module"]}')
            require(sha(within(packet,row['log'])) == row['log_sha256'],
                    f'Log mismatch: {row["module"]}')
            if 'log_sha256' in raw:
                require(raw['log_sha256'] == row['log_sha256'], 'Original log hash mismatch')
            ref = row['source']
            source = None
            if 'packet_path' in ref:
                source = within(packet, ref['packet_path'])
            elif repo:
                source = within(repo, ref['repository_path'])
                repository_bindings += 1
            if source:
                require(sha(source) == row['source_sha256'], f'Source mismatch: {source}')
            bindings += 1
    print(json.dumps({'status':'PASS_INTEGRITY_AND_BINDINGS',
                      'manifest_files':count, 'accepted_module_bindings':bindings,
                      'repository_source_bindings_checked':repository_bindings,
                      'proof_compiler_invoked':False}, indent=2))


if __name__ == '__main__':
    main()
