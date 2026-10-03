#!/usr/bin/env python3
"""Verify the complete merged six-part cubic-boundary research package.

Python 3.10+, standard library only. Needs about 6 GB temporary free space.
No prior archive, producer code, solver, numerical package, or network is used.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def safe_path(name):
    require(isinstance(name, str) and name, 'Empty or non-string path')
    p = PurePosixPath(name)
    require(not p.is_absolute() and '\\' not in name and
            all(x not in ('', '.', '..') for x in name.split('/')),
            'Unsafe member path: ' + name)
    require(p.as_posix() == name, 'Noncanonical member path: ' + name)
    return p


def table(records):
    out = {}
    for row in records:
        name = row['path']
        safe_path(name)
        require(name not in out, 'Duplicate manifest path: ' + name)
        require(type(row['bytes']) is int and row['bytes'] >= 0, 'Bad byte count')
        require(len(row['sha256']) == 64 and all(c in '0123456789abcdef' for c in row['sha256']), 'Bad SHA256')
        out[name] = row
    return out


def verify_file(path, row):
    require(path.is_file() and not path.is_symlink(), 'Missing or nonregular required file: ' + str(path))
    require(path.stat().st_size == row['bytes'], 'Byte count mismatch: ' + str(path))
    require(digest(path) == row['sha256'], 'SHA256 mismatch: ' + str(path))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--output', type=Path, default=Path.cwd() / 'fresh-replay.json')
    ap.add_argument('--temp-dir', type=Path, default=Path.cwd(), help='Parent directory for decoded data; defaults to current directory, not the system temporary volume')
    ap.add_argument('--integrity-only', action='store_true', help='Check complete package integrity, without mathematical replay')
    args = ap.parse_args()
    require(args.workers >= 1, 'Worker count must be positive')
    start = time.monotonic()
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    files = table(manifest['files'])
    for name, row in files.items():
        verify_file(ROOT / name, row)
    require('verify.py' in files and 'data-shards.json' in files and 'proof-data-manifest.json' in files,
            'Incomplete scientific manifest')
    index = json.loads((ROOT / 'data-shards.json').read_text())
    require(digest(ROOT / 'proof-data-manifest.json') == index['source_manifest_sha256'], 'Wrong proof manifest')
    proof = table(json.loads((ROOT / 'proof-data-manifest.json').read_text())['files'])
    inputs = {'cores.txt', 'structural-9608.json', 'preorder-coverage.json'}
    require(inputs <= proof.keys(), 'Missing input metadata')
    expected_cert = set(proof) - inputs
    require(len(proof) == 7904 and len(expected_cert) == 7901, 'Wrong complete proof-file count')
    members = set()
    shard_paths = set()
    for shard in index['shards']:
        name = shard['path']
        require(name not in shard_paths and name in files, 'Duplicate or unmanifested shard')
        shard_paths.add(name)
        require(shard['bytes'] == files[name]['bytes'] and shard['sha256'] == files[name]['sha256'], 'Inconsistent shard identity')
        listed = shard['members']
        require(len(listed) == len(set(listed)) == shard['member_count'], 'Duplicate shard member')
        require(not (members & set(listed)), 'Proof member occurs in two shards')
        require(set(listed) <= expected_cert, 'Unexpected proof member')
        require(sum(proof[n]['bytes'] for n in listed) == shard['uncompressed_bytes'], 'Wrong uncompressed byte count')
        members.update(listed)
    require(members == expected_cert and len(shard_paths) == index['shard_count'] == 6, 'Missing proof-data shard or member')
    require(sum(s['bytes'] for s in index['shards']) == index['compressed_bytes'], 'Wrong compressed total')
    require(sum(proof[n]['bytes'] for n in members) == index['uncompressed_certificate_bytes'], 'Wrong certificate total')
    receipt = {'status': 'PASS', 'integrity_only': args.integrity_only,
               'manifest_sha256': digest(ROOT / 'MANIFEST.json'),
               'integrity_file_count': len(files), 'data_shard_count': len(shard_paths),
               'source_manifest_sha256': index['source_manifest_sha256']}
    print(f'All {len(files)} package files and all six data shards have exact identities', flush=True)
    if not args.integrity_only:
        require(args.temp_dir.is_dir(), 'Temporary parent directory does not exist')
        needed = sum(row['bytes'] for row in proof.values()) + 128 * 1024 * 1024
        require(shutil.disk_usage(args.temp_dir).free >= needed,
                'Not enough temporary free space; choose a larger volume with --temp-dir PATH')
        with tempfile.TemporaryDirectory(prefix='five-core-cubic-replay-', dir=args.temp_dir) as tmp:
            base = Path(tmp)
            source = base / 'source'
            source.mkdir()
            for name in inputs:
                verify_file(ROOT / 'inputs' / name, proof[name])
                shutil.copyfile(ROOT / 'inputs' / name, source / name)
            seen = set()
            for shard in index['shards']:
                allowed = set(shard['members'])
                got = set()
                with tarfile.open(ROOT / shard['path'], mode='r|xz') as tf:
                    for member in tf:
                        name = member.name
                        safe_path(name)
                        require(member.isfile() and not member.issym() and not member.islnk(), 'Nonregular tar member')
                        require(name in allowed and name not in seen, 'Unexpected or duplicated tar member: ' + name)
                        require(member.size == proof[name]['bytes'], 'Wrong tar member size: ' + name)
                        dest = source / name
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        h = hashlib.sha256()
                        count = 0
                        raw = tf.extractfile(member)
                        require(raw is not None, 'Unreadable tar member')
                        with raw, dest.open('xb') as out:
                            for chunk in iter(lambda: raw.read(1024 * 1024), b''):
                                count += len(chunk)
                                h.update(chunk)
                                out.write(chunk)
                        require(count == proof[name]['bytes'] and h.hexdigest() == proof[name]['sha256'], 'Decoded proof bytes changed: ' + name)
                        seen.add(name)
                        got.add(name)
                require(got == allowed, 'Shard is missing declared members')
                print(f'Decoded and verified {shard["path"]}: {len(got)} original certificate files', flush=True)
            require(seen == expected_cert, 'Incomplete extracted proof collection')
            env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
            runs = [
                ('full', 'hybrid_extended.py', [str(source), '--workers', str(args.workers)]),
                ('extended-controls', 'selftest_extended_portable.py', [str(source)]),
                ('multiplier-controls', 'selftest_multiplier_portable.py', [str(source)]),
                ('sharpness', 'check_sharpness_portable.py', []),
            ]
            results = {}
            for label, script, extra in runs:
                output = base / (label + '.json')
                command = [sys.executable, '-B', str(ROOT / 'replay' / script), *extra, '--output', str(output)]
                print('Running ' + script, flush=True)
                subprocess.run(command, check=True, env=env, cwd=base)
                results[label] = json.loads(output.read_text())
                require(results[label]['status'] == 'PASS', 'Replay failed: ' + label)
            fresh = results['full']
            approved = json.loads((ROOT / 'audits' / 'full-hybrid-20261001T164052Z-receipt.json').read_text())
            for key in ('complete_hybrid_domain_verified', 'target', 'variables', 'target_homogeneous_degree',
                        'certificate_homogeneous_degrees', 'multiplier_counts', 'covered_class_count',
                        'missing_class_count', 'missing_class_ids', 'selected_disjoint_ledger_counts',
                        'all_available_certificate_count', 'certificate_overlap_with_structural_or_preorder_count',
                        'positive_rational_square_count', 'positive_remainder_term_count',
                        'all_exact_remainders_coefficientwise_nonnegative',
                        'all_9608_literal_and_hall_support_polynomials_equal',
                        'support_counts_summed_over_all_representatives', 'coverage',
                        'catalog_sha256', 'certificate_manifest_sha256', 'checker_sha256',
                        'polynomial_checker_sha256', 'structural_checker_sha256', 'structural_support_checker_sha256'):
                require(fresh[key] == approved[key], 'Fresh replay differs from approved receipt: ' + key)
            receipt.update({'complete_fresh_mathematical_replay': True, 'original_certificate_files': len(seen),
                            'decoded_proof_data_bytes': sum(r['bytes'] for r in proof.values()),
                            'results': results, 'prior_archives_required_or_replayed': False,
                            'producer_code_or_solver_or_network_used': False})
    receipt['seconds'] = round(time.monotonic() - start, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS in {receipt["seconds"]} seconds; receipt: {args.output}', flush=True)


if __name__ == '__main__':
    main()
