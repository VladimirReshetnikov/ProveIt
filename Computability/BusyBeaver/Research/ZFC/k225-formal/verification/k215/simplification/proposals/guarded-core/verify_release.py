#!/usr/bin/env python3
"""Verify sealed bytes, then replay only the explicit owned-checker allowlist.

All execution happens in a disposable package copy. Received archives, received
programs, proof assistants, report builds, and network commands are never run.
"""
import os
import sys
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION: remove -O/-OO and unset PYTHONOPTIMIZE.')
import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent
MANIFEST_SHA256 = 'e7f7ea985be72175e27847e8f57163c0e97a99abc4d16965f9bed0c75b2f6b74'
REPLAYS = [
    ('source_and_receipt_pins', 'check_source_pins.py', ['SOURCE_PIN_CHECKS.json']),
    ('guarded_core_construction', 'affine/review_owned.py', ['affine/GUARDED_CORE.json', 'affine/GUARDED_CORE_COMPACT.json', 'affine/CLEAR_ZERO_COUNTEREXAMPLES.json', 'affine/OWN_AUDIT.json']),
    ('received_checked_evidence', 'checked/audit_received.py', ['checked/INDEPENDENT_AUDIT.json']),
    ('literal_decoder_prefixes', 'checked/check_decoder_prefixes.py', ['checked/DECODER_PREFIX_RESULT.json']),
    ('certificate_refinements', 'refinements/audit_refinements.py', ['refinements/radix_certificate.json', 'refinements/positive_trie_certificate.json', 'refinements/AUDIT_RESULT.json']),
    ('independent_positive_trie', 'refinements/verify_positive_trie.py', ['refinements/POSITIVE_TRIE_INDEPENDENT.json']),
    ('independent_guarded_core', 'guarded_review/independent_verify.py', ['guarded_review/ENTRY_SUFFIX_CERTIFICATES.json', 'guarded_review/LOOP_BINDINGS.json', 'guarded_review/INDEPENDENT_AUDIT.json']),
]
NEGATIVE = ('outer_and_optimization_controls', 'tests/test_outer_verifier.py', [])

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inventory(root):
    result = {}
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'SYMLINK_IN_RELEASE: ' + str(p))
        if p.is_file():
            result[p.relative_to(root).as_posix()] = sha(p.read_bytes())
    return result

def validate_manifest():
    path = ROOT / 'MANIFEST.json'
    require(path.is_file() and not path.is_symlink(), 'MISSING_OR_SYMLINK_MANIFEST')
    raw = path.read_bytes()
    require(sha(raw) == MANIFEST_SHA256, 'MANIFEST_SHA256_MISMATCH')
    manifest = json.loads(raw)
    require(manifest['schema'] == 'k215-guarded-proof-core-release-sha256-v1', 'MANIFEST_SCHEMA')
    require(isinstance(manifest['files'], dict), 'MANIFEST_FILES')
    for name, pin in manifest['files'].items():
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == name, 'UNSAFE_MANIFEST_PATH')
        p = ROOT.joinpath(*rel.parts)
        require(p.is_file() and not p.is_symlink(), 'MISSING_OR_SYMLINK_FILE: ' + name)
        require(ROOT in p.resolve().parents, 'PATH_OUTSIDE_RELEASE: ' + name)
        raw = p.read_bytes()
        require(len(raw) == pin['bytes'] and sha(raw) == pin['sha256'], 'PAYLOAD_SHA256_MISMATCH: ' + name)
    require(set(inventory(ROOT)) == set(manifest['files']) | {'MANIFEST.json', 'verify_release.py'}, 'UNMANIFESTED_OR_MISSING_FILE')
    return manifest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hash-only', action='store_true')
    parser.add_argument('--negative-controls', action='store_true')
    args = parser.parse_args()
    manifest = validate_manifest()
    before = inventory(ROOT)
    result = {
        'status': 'PASS_PACKAGE_INTEGRITY_ONLY' if args.hash_only else 'PASS_FINITE_REPLAY_NOT_KERNEL_PROOF',
        'manifest_sha256': MANIFEST_SHA256,
        'manifest_files': len(manifest['files']),
        'verifier_sha256': before['verify_release.py'],
        'received_code_executed': False,
        'lean_or_rocq_compiled': False,
        'network_access_requested': False,
        'original_packet_unchanged': False,
        'checks': [],
    }
    if not args.hash_only:
        with tempfile.TemporaryDirectory(prefix='k215-guarded-replay-') as td:
            work = Path(td) / 'packet'
            shutil.copytree(ROOT, work)
            unrelated = Path(td) / 'unrelated-cwd'
            unrelated.mkdir()
            env = dict(os.environ)
            for key in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONOPTIMIZE', 'PYTHONSTARTUP'):
                env.pop(key, None)
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            for name, script, outputs in REPLAYS + ([NEGATIVE] if args.negative_controls else []):
                require(script in manifest['files'], 'UNPINNED_CHECKER: ' + script)
                prior = inventory(work)
                run = subprocess.run([sys.executable, '-I', '-B', str(work / script)], cwd=unrelated,
                                     env=env, capture_output=True, text=True, timeout=900)
                require(run.returncode == 0, 'REPLAY_FAILED: ' + name + '\n' + run.stdout + '\n' + run.stderr)
                after = inventory(work)
                require(set(prior) == set(after), 'REPLAY_ADDED_OR_REMOVED_FILE: ' + name)
                changed = {p for p in prior if prior[p] != after[p]}
                require(changed <= set(outputs), 'REPLAY_CHANGED_UNDECLARED_INPUT: ' + name + ': ' + repr(sorted(changed)))
                for output in outputs:
                    require((ROOT / output).read_bytes() == (work / output).read_bytes(), 'REPLAY_OUTPUT_CHANGED: ' + output)
                if script == NEGATIVE[1]:
                    require(json.loads(run.stdout) == json.loads((ROOT / 'OUTER_NEGATIVE_CONTROLS.json').read_text()), 'NEGATIVE_CONTROL_RESULT_CHANGED')
                result['checks'].append({'name': name, 'script': script, 'exit_code': 0,
                                         'archived_outputs_byte_equal': outputs,
                                         'stdout_sha256': sha(run.stdout.encode()),
                                         'stderr_sha256': sha(run.stderr.encode()),
                                         'undeclared_writes': False})
                print('PASS ' + name, file=sys.stderr, flush=True)
    validate_manifest()
    require(before == inventory(ROOT), 'ORIGINAL_RELEASE_CHANGED')
    result['original_packet_unchanged'] = True
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
