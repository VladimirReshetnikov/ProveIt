#!/usr/bin/env python3
"""Portable replay of two independent, newly authored exact audit checkers.

The original checker bytes and complete audit packet are SHA-256 pinned here.
Only their OUT and SRC assignments are rebased in memory. No author emitter,
author membership program, saved machine program, or physical simulator runs.
The destination must not exist and must be outside the frozen audit packet.
Python 3.9+ standard library only. Run without -O because checkers use asserts.
"""
import argparse
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys

MANIFEST_SHA256 = 'faf598b0cbbce38d618e40642b486f98a36671b48a71284ca9257d4684b5a390'
PINNED = {
    'INDEPENDENT_AUDIT.md': 'b119df1c0be8685078b011c14e3c71decabce343f9ba9041ee6f97b4c58a5226',
    'all_138_local_rule_checks.tsv': '95621369af4eb77b8df700986114315f6c2cf1673e964ae910bdaef1e9273031',
    'audit_exact_algebra.py': '6e0a67b37afad7d139fc005cf6d116d409e07f8df9881f715ac803aadfc5ee53',
    'audit_inert_rules.py': '7ba52322663e048f0d27b1a2551e50556566c87dca5c1d4b68ef269428cde477',
    'exact_algebra_receipt.json': '4576156d03853c41c290173481f0bfe51e81c54ae470f70d9491e387b6b94cf8',
    'exact_algebra_stdout.json': 'adf68833fd10b4755a90e10bb1e48aa956cc25da412373d32a94a2e849139039',
    'inert_rules_receipt.json': 'fdbf73c7b724d5148b3f76b0fd0c587924dd8e7a39ac2b90f4a45a62287bfc14',
    'inert_rules_stdout.json': 'ebab105dc2fd66e6911900802c75a8bcec1fe63b6115c9269cd476af50ebac6d',
    'inert_sources/BOUNDARY_AND_ARITHMETIC.md': '9642699a09f3ebc558fb1268c61370fb514839404e834acf288f9504e3e81b77',
    'inert_sources/GUARDS.txt': 'd8c1dec4945dd4f3dedfdf469d3b6e51ea9991e8234cccb1daf49c0d8cbc6ce9',
    'inert_sources/PROOF.md': '1bea81f8f2e6693d4b7958fb44763eb644663d208fe70c577e0137184e17a725',
    'inert_sources/RULES.json': '0e145aecc4f60685570c41be57d04905eab5b3bfa1a25b185d0b7bcf27e2f2db',
    'inert_sources/rational_membership.py': '14a31600583a89def7f81e27cfa56c9eff187df7c8a4bca31fddca4c7379d33f',
}
OUTPUT_NAMES = (
    'exact_algebra_receipt.json', 'inert_rules_receipt.json',
    'all_138_local_rule_checks.tsv',
    'exact_algebra_stdout.json', 'inert_rules_stdout.json',
)
CHECKERS = (
    ('audit_exact_algebra.py', 'exact_algebra_stdout.json'),
    ('audit_inert_rules.py', 'inert_rules_stdout.json'),
)
REBASE = (
    ('OUT=Path(__file__).parent', 'OUT=Path(__audit_output_dir__)'),
    ("SRC=OUT/'inert_sources'", 'SRC=Path(__audit_input_dir__)'),
)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def packet_bytes(packet, relative):
    path = packet / relative
    if not path.resolve().is_relative_to(packet):
        raise ValueError('Pinned input resolves outside the packet: ' + relative)
    return path.read_bytes()

def verify_packet(packet):
    manifest_bytes = packet_bytes(packet, 'MANIFEST.json')
    if sha(manifest_bytes) != MANIFEST_SHA256:
        raise ValueError('Audit MANIFEST.json hash mismatch')
    manifest = json.loads(manifest_bytes)
    if manifest.get('files_sha256') != PINNED:
        raise ValueError('Pinned manifest contents do not match the adapter')
    data = {}
    for relative, digest in PINNED.items():
        content = packet_bytes(packet, relative)
        if sha(content) != digest:
            raise ValueError('Pinned file hash mismatch: ' + relative)
        data[relative] = content
    return data

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-packet', required=True, type=Path,
                        help='Frozen independent-audit directory containing MANIFEST.json')
    parser.add_argument('--output-dir', required=True, type=Path,
                        help='Brand-new output directory, outside the frozen audit packet')
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise ValueError('Run without -O or PYTHONOPTIMIZE; audit assertions must be enabled')
    packet = args.audit_packet.resolve(strict=True)
    output = args.output_dir.resolve()
    if output.is_relative_to(packet):
        raise ValueError('Output must be outside the frozen audit packet')
    if output.exists() or args.output_dir.is_symlink():
        raise ValueError('Output directory must be brand-new, not existing or a symlink')
    data = verify_packet(packet)
    # Verify all pinned inputs before any output directory is created or code runs.
    output.mkdir(parents=True, exist_ok=False)
    rewritten_hashes = {}
    for checker, stdout_file in CHECKERS:
        source = data[checker].decode('utf-8')
        for old, new in REBASE:
            if source.count(old) != 1:
                raise ValueError('Unexpected path-assignment count in ' + checker)
            source = source.replace(old, new)
        rewritten_hashes[checker] = sha(source.encode('utf-8'))
        namespace = {
            '__name__': '__independent_audit_replay__',
            '__file__': str(packet / checker),
            '__audit_output_dir__': str(output),
            '__audit_input_dir__': str(packet / 'inert_sources'),
        }
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured):
            exec(compile(source, str(packet / checker), 'exec'), namespace)
        (output / stdout_file).write_bytes(captured.getvalue().encode('utf-8'))
    comparisons = {}
    for name in OUTPUT_NAMES:
        content = (output / name).read_bytes()
        if content != data[name] or sha(content) != PINNED[name]:
            raise ValueError('Replayed output differs from frozen receipt: ' + name)
        comparisons[name] = {'byte_identical': True, 'sha256': PINNED[name]}
    # This is an integrity/reproducibility adapter, not a sandbox for arbitrary code.
    # Execution was restricted by exact source hashes and two literal path rewrites.
    # Verify again before writing a PASS result.
    verify_packet(packet)
    summary = {
        'result': 'PASS',
        'scope': 'Independent exact algebra and inert rule-template validation only',
        'frozen_manifest_sha256': MANIFEST_SHA256,
        'pinned_packet_files_verified': len(PINNED),
        'frozen_checker_hashes': {name: PINNED[name] for name, _ in CHECKERS},
        'in_memory_rewrites_only': [{'old': old, 'new': new} for old, new in REBASE],
        'rebased_checker_sha256': rewritten_hashes,
        'replay_comparisons': comparisons,
        'author_or_physical_program_execution': False,
        'packet_files_modified': False,
    }
    (output / 'PORTABLE_REPLAY_RESULT.json').write_text(
        json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('Portable audit replay failed: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
