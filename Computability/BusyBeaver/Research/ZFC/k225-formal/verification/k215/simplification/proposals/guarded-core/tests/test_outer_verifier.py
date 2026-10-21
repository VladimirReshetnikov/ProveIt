#!/usr/bin/env python3
"""Owned rejection tests; only disposable copies are modified or executed."""
import os
import sys
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION')
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CHECKERS = [
    'check_source_pins.py', 'affine/review_owned.py', 'checked/audit_received.py',
    'checked/check_decoder_prefixes.py', 'refinements/audit_refinements.py',
    'refinements/verify_positive_trie.py', 'guarded_review/independent_verify.py',
]

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def inventory(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file()}

def run(root, script='verify_release.py', flags=(), environment=None):
    env = dict(os.environ)
    for key in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONOPTIMIZE', 'PYTHONSTARTUP'):
        env.pop(key, None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env.update(environment or {})
    args = ['--hash-only'] if script == 'verify_release.py' else []
    return subprocess.run([sys.executable, *flags, '-B', str(root / script), *args],
                          cwd=root.parent, env=env, capture_output=True, text=True, timeout=120)

def main():
    original = inventory(ROOT)
    results = {}
    with tempfile.TemporaryDirectory(prefix='k215-guarded-controls-') as td:
        root = Path(td) / 'packet'
        shutil.copytree(ROOT, root)
        require(run(root).returncode == 0, 'CLEAN_COPY_FAILED')
        results['clean_relocated_copy'] = 'passed'
        modes = [
            ('-O', ('-O',), {}), ('-OO', ('-OO',), {}),
            ('PYTHONOPTIMIZE=1', (), {'PYTHONOPTIMIZE': '1'}),
            ('PYTHONOPTIMIZE=2', (), {'PYTHONOPTIMIZE': '2'}),
            ('PYTHONOPTIMIZE=0', (), {'PYTHONOPTIMIZE': '0'}),
            ('-E plus PYTHONOPTIMIZE=1', ('-E',), {'PYTHONOPTIMIZE': '1'}),
            ('-I plus PYTHONOPTIMIZE=1', ('-I',), {'PYTHONOPTIMIZE': '1'}),
        ]
        guarded = {}
        for script in ['verify_release.py', *CHECKERS]:
            before = inventory(root)
            guarded[script] = []
            for label, flags, env in modes:
                result = run(root, script, flags, env)
                diagnostic = (result.stdout + result.stderr).lower()
                require(result.returncode != 0 and ('optimiz' in diagnostic or 'assertion' in diagnostic),
                        'OPTIMIZATION_NOT_EXPLICITLY_REJECTED: ' + script + ': ' + label)
                require(inventory(root) == before, 'REJECTED_MODE_CHANGED_FILES: ' + script)
                guarded[script].append(label)
        results['explicit_optimization_rejections'] = guarded
        cases = [
            ('changed_owned_checker', 'affine/review_owned.py', 'PAYLOAD_SHA256_MISMATCH'),
            ('changed_received_data', 'affine/GUARDED_CORE.json', 'PAYLOAD_SHA256_MISMATCH'),
            ('changed_manifest', 'MANIFEST.json', 'MANIFEST_SHA256_MISMATCH'),
        ]
        for label, name, reason in cases:
            p = root / name
            old = p.read_bytes()
            try:
                p.write_bytes(old + b'\n')
                result = run(root)
                require(result.returncode != 0 and reason in result.stderr + result.stdout, 'TAMPERING_ACCEPTED: ' + label)
            finally:
                p.write_bytes(old)
            results[label] = 'rejected'
        p = root / 'unexpected.txt'
        p.write_text('not manifested')
        result = run(root)
        p.unlink()
        require(result.returncode != 0 and 'UNMANIFESTED_OR_MISSING_FILE' in result.stderr, 'EXTRA_FILE_ACCEPTED')
        results['unlisted_file'] = 'rejected'
        p = root / 'affine/GUARDED_CORE_COMPACT.json'
        old = p.read_bytes()
        p.unlink()
        result = run(root)
        p.write_bytes(old)
        require(result.returncode != 0 and 'MISSING_OR_SYMLINK_FILE' in result.stderr, 'MISSING_FILE_ACCEPTED')
        results['missing_file'] = 'rejected'
        p.unlink()
        p.symlink_to(ROOT / 'affine/GUARDED_CORE_COMPACT.json')
        result = run(root)
        p.unlink()
        p.write_bytes(old)
        require(result.returncode != 0 and 'MISSING_OR_SYMLINK_FILE' in result.stderr, 'FILE_SYMLINK_ACCEPTED')
        results['payload_symlink'] = 'rejected'
        p = root / 'unexpected_directory'
        p.symlink_to(ROOT / 'affine', target_is_directory=True)
        result = run(root)
        p.unlink()
        require(result.returncode != 0 and 'SYMLINK_IN_RELEASE' in result.stderr, 'DIRECTORY_SYMLINK_ACCEPTED')
        results['directory_symlink'] = 'rejected'
        # Direct checker rejection must happen before any result is rewritten.
        direct_cases = [
            ('affine/review_owned.py', 'affine/extracted/Affine_Proof_Cores_and_Transport_2026-10-21/structural/input_graph.json', None),
            ('checked/audit_received.py', 'checked/extracted/K215_Checked_Simplifications_2026-10-21/SHA256SUMS', None),
            ('checked/check_decoder_prefixes.py', 'checked/extracted/K215_Checked_Simplifications_2026-10-21/decoder_lean/inputs/decoder_context_certificate.json', None),
            ('refinements/audit_refinements.py', 'refinements/incoming/K215_Certificate_Refinements_2026-10-21/balanced_lookup/Cert215Compact.v', None),
            ('refinements/verify_positive_trie.py', 'refinements/positive_trie_certificate.json', 'initial'),
            ('guarded_review/independent_verify.py', 'affine/extracted/Affine_Proof_Cores_and_Transport_2026-10-21/structural/input_graph.json', None),
        ]
        direct = {}
        for script, name, mutation in direct_cases:
            p = root / name
            old = p.read_bytes()
            if mutation:
                obj = json.loads(old)
                obj['initial'] = 2
                p.write_text(json.dumps(obj))
            else:
                p.write_bytes(old + b'\n')
            before = inventory(root)
            try:
                result = run(root, script, ('-I',))
                require(result.returncode != 0, 'DIRECT_BAD_INPUT_ACCEPTED: ' + script)
                require(inventory(root) == before, 'DIRECT_REJECTION_CHANGED_OUTPUT: ' + script)
            finally:
                p.write_bytes(old)
            direct[script] = 'rejected_without_output_write'
        results['direct_checker_changed_input_rejections'] = direct
        require(run(root).returncode == 0, 'RESTORED_COPY_FAILED')
        results['restored_copy'] = 'passed'
    require(inventory(ROOT) == original, 'ORIGINAL_CHANGED_BY_CONTROLS')
    print(json.dumps({'status': 'PASS_OUTER_AND_OWNED_CHECKER_NEGATIVE_CONTROLS',
                      'checks': results, 'original_packet_unchanged': True,
                      'received_code_executed': False}, indent=2))

if __name__ == '__main__':
    main()
