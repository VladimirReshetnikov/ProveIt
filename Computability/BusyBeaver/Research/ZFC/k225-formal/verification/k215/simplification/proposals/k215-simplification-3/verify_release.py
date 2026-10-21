#!/usr/bin/env python3
"""Validate the release bytes, then replay owned finite checkers in a temporary copy.
No Lean/Rocq compilation, upstream generator, or received ZIP code is executed.
"""
import os
import sys
if not __debug__ or sys.flags.optimize != 0 or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION: run without -O/-OO and unset PYTHONOPTIMIZE.')
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
MANIFEST_SHA256 = 'ae96f39ed69e66692d6b83d0e805464c9754a65b3721253a8232113efe38d068'
# This allowlist contains only independently written research checkers. In
# particular, no snapshot generator or received.zip member may enter it.
REPLAYS = [
 ('lean_snapshot', 'lean/verify_snapshot.py', [], []),
 ('lean_forward', 'lean/profiling/profile_forward_checks.py', [], ['lean/profiling/forward_profile.json']),
 ('lean_cfg', 'lean/profiling/verify_lean_canonical_cfg.py', [], ['lean/profiling/canonical_cfg_result.json']),
 ('lean_walker', 'lean/profiling/profile_walker_sharing.py', [], ['lean/profiling/walker_sharing_result.json']),
 ('lean_canonical_rows', 'lean/profiling/build_canonical_rows.py', [], ['lean/profiling/canonical_rows.json','lean/profiling/canonical_rows_result.json']),
 ('lean_minimization', 'lean/profiling/minimization/minimize_canonical_cfg.py', [], ['lean/profiling/minimization/minimization_result.json','lean/profiling/minimization/quotient_certificate.json']),
 ('rocq_certificate', 'rocq/prototype.py', [], ['rocq/prototype_result.json','rocq/PackedCert215.v','rocq/PackedCertAudit.v','rocq/Source215Plain.v']),
 ('rocq_cfg', 'rocq/compare_flat_cfg.py', [], ['rocq/flat_cfg_result.json','rocq/p215_flat_cfg.json','rocq/dagPerm_flat_cfg.json']),
 ('rocq_rewrites', 'rocq/analyze_cfg_rewrites.py', [], ['rocq/cfg_rewrite_result.json','rocq/common_block_cfg.json','rocq/cfg_swap_locations.json','rocq/two_node_swap_result.json','rocq/checkpoint_aliases.json']),
 ('candidate_interfaces', 'candidates/audit_candidate_interfaces.py', ['--expected','candidates/finite_interface_audit.json'], []),
 ('cm_transport', 'transport/check_transport.py', ['--certificate','transport/evidence/certificate.json','--out','transport/evidence'], ['transport/evidence/certificate.json','transport/evidence/result.json']),
 ('runtime', 'runtime/profile_runtime.py', [], ['runtime/profile_result.json']),
 ('window_reduction', 'window_reduction/verify.py', [], ['window_reduction/verification.json']),
 ('enumeration', 'enumeration/check_length_padding.py', [], []),
 ('gc_zc_intake_data', 'new_intake/gc_zc215/audit_received_data.py', [], ['new_intake/gc_zc215/independent_intake_audit.json']),
]
NEGATIVE_REPLAYS = [
 ('rocq_hardening', 'rocq/test_hardening.py', [], []),
 ('window_negative_controls', 'window_reduction/test_rejection.py', [], []),
]

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def validate_manifest():
    raw = (ROOT/'MANIFEST.json').read_bytes()
    require(sha(raw) == MANIFEST_SHA256, 'MANIFEST_SHA256_MISMATCH')
    m = json.loads(raw)
    require(m['schema'] == 'proof-simplification-release-sha256-v1', 'MANIFEST_SCHEMA')
    files = m['files']
    require(isinstance(files, dict), 'MANIFEST_FILES')
    for name, pin in files.items():
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == name, 'UNSAFE_MANIFEST_PATH')
        path = ROOT.joinpath(*rel.parts)
        require(path.is_file() and not path.is_symlink(), 'MISSING_OR_SYMLINK_FILE: '+name)
        require(ROOT in path.resolve().parents, 'PATH_OUTSIDE_RELEASE: '+name)
        raw = path.read_bytes()
        require(len(raw) == pin['bytes'] and sha(raw) == pin['sha256'], 'PAYLOAD_SHA256_MISMATCH: '+name)
    actual = set()
    for p in ROOT.rglob('*'):
        require(not p.is_symlink(), 'SYMLINK_IN_RELEASE: '+str(p))
        if p.is_file():
            actual.add(p.relative_to(ROOT).as_posix())
    require(actual == set(files) | {'MANIFEST.json','verify_release.py'}, 'UNMANIFESTED_OR_MISSING_FILE')
    return m

def compare_output(root, relative):
    before = (ROOT/relative).read_bytes()
    after = (root/relative).read_bytes()
    if relative.endswith('.json'):
        require(json.loads(before) == json.loads(after), 'REPLAY_OUTPUT_CHANGED: '+relative)
    else:
        require(before == after, 'REPLAY_OUTPUT_CHANGED: '+relative)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hash-only', action='store_true', help='Validate every packaged byte but do not replay checkers.')
    parser.add_argument('--negative-controls', action='store_true', help='Also replay the packaged mutation/optimization rejection suites.')
    args = parser.parse_args()
    manifest = validate_manifest()
    result = {'status':'PASS_PACKAGE_INTEGRITY_ONLY' if args.hash_only else 'PASS_FINITE_REPLAY_NOT_KERNEL_PROOF',
              'manifest_sha256':MANIFEST_SHA256, 'manifest_files':len(manifest['files']),
              'python':sys.version.split()[0], 'received_code_executed':False,
              'lean_or_rocq_compiled':False, 'original_packet_unchanged':False, 'checks':[]}
    if not args.hash_only:
        with tempfile.TemporaryDirectory(prefix='proof-simplification-replay-') as td:
            work = Path(td)/'packet'
            shutil.copytree(ROOT, work)
            env = dict(os.environ)
            for k in ('PYTHONPATH','PYTHONHOME','PYTHONOPTIMIZE','PYTHONSTARTUP'):
                env.pop(k,None)
            env['PYTHONDONTWRITEBYTECODE']='1'
            cases = REPLAYS + (NEGATIVE_REPLAYS if args.negative_controls else [])
            for name, script, extra, outputs in cases:
                require(script in manifest['files'], 'UNPINNED_CHECKER: '+script)
                started = time.monotonic()
                run = subprocess.run([sys.executable,'-B',str(work/script),*extra], cwd=work,
                                     env=env, capture_output=True, text=True, timeout=600)
                require(run.returncode == 0, 'REPLAY_FAILED: '+name+'\n'+run.stdout+'\n'+run.stderr)
                for output in outputs:
                    compare_output(work, output)
                if name == 'enumeration':
                    require(json.loads(run.stdout) == json.loads((ROOT/'enumeration/check_result.json').read_text()), 'ENUMERATION_OUTPUT_CHANGED')
                result['checks'].append({'name':name,'script':script,'exit_code':run.returncode,
                    'archived_outputs_equal':outputs,'stdout_sha256':sha(run.stdout.encode()),
                    'stderr_sha256':sha(run.stderr.encode()),
                    'python_replay_seconds_not_proof_assistant_benchmark':round(time.monotonic()-started,3)})
                print('PASS '+name, file=sys.stderr, flush=True)
    validate_manifest()
    result['original_packet_unchanged']=True
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
