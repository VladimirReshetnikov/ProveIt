#!/usr/bin/env python3
"""Point-in-time independent audit of a finished guarded Foundation provider."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
INPUT = PROJECT / 'reviews/foundation-provider-recovery/input-manifest.json'
DRIVER = PROJECT / 'reviews/foundation-provider-recovery/build_all.py'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
INPUT_SHA = '491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d'
PROJECT_MANIFEST_SHA = '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--observation', type=Path, required=True)
    parser.add_argument('--project-manifest', type=Path, required=True)
    args = parser.parse_args()
    assert sha(INPUT) == INPUT_SHA and sha(args.project_manifest) == PROJECT_MANIFEST_SHA
    m = json.loads(INPUT.read_text()); project = json.loads(args.project_manifest.read_text())
    receipt_path = args.receipt.resolve(strict=True); observation_path = args.observation.resolve(strict=True)
    receipt_hash = sha(receipt_path); observation_hash = sha(observation_path)
    r = json.loads(receipt_path.read_text()); obs = json.loads(observation_path.read_text())
    assert r['status'] == 'BUILT' and r['exit_code'] == 0 and not r['space_stop']
    assert obs['observed_exit_code'] is None and obs['receipt_sha256'] == receipt_hash
    assert Path(obs['receipt_path']).resolve(strict=True) == receipt_path
    assert obs['tool_session'] and 'BUILT 140 Foundation targets;' in obs['observed_stdout']
    assert r['manifest_sha256'] == INPUT_SHA and r['driver_sha256'] == sha(DRIVER)
    assert sha(LEAN) == m['lean_sha256']
    root = Path(r['root']).resolve(strict=True); source = root / 'lib/FormalizedFormalLogic-Foundation'
    assert receipt_path == root / 'build-all-receipt.json'
    actual_source = {}
    for p in source.rglob('*'):
        assert not p.is_symlink(), ('source symlink', str(p))
        if p.is_file(): actual_source[str(p.relative_to(source))] = sha(p)
    assert actual_source == m['foundation_archive_files_sha256']
    for name, expected in m['configs_sha256'].items(): assert sha(root / name) == expected
    rev = subprocess.check_output(['git', '-C', '/home/codex/src/Proofs/.lake/packages/mathlib',
                                   'rev-parse', 'HEAD'], text=True).strip()
    assert rev == m['mathlib_checkout_commit']
    assert sha(root / 'build-all.log') == r['log_sha256']
    for name, record in r['declared_external_guard'].items():
        path = Path(name)
        if record is None:
            assert not os.path.lexists(path), ('unexpected guard path', name)
        else:
            assert path.is_file() and str(path.resolve()) == record['realpath'] and sha(path) == record['sha256'], ('guard mismatch', name)
    foundation = root / '.lake/build/lib/lean/Foundation'
    actual = {}
    for path in foundation.rglob('*'):
        assert not path.is_symlink(), ('Foundation symlink', str(path))
        if path.is_file(): actual[str(path.relative_to(foundation))] = sha(path)
    assert actual == r['foundation_artifacts']
    assert set(r['objects']) == set(m['historical_module_names'])
    for name, expected in r['objects'].items():
        obj = root / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')
        assert sha(obj) == expected
    needed = {n for n in project['external_modules'] if n.startswith('Foundation.')}
    assert needed <= set(r['objects'])
    for name in needed:
        assert (root / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')).is_file()
    overlay = Path(r['overlay']); assert (overlay / 'Foundation').resolve(strict=True) == foundation
    assert all(x.exists() for x in overlay.iterdir())
    roots = [Path(p) for p in r['lake_lean_path'].split(':')]
    assert roots and all(p.is_absolute() for p in roots)
    namespaces = {}
    for name in r['declared_external_modules']:
        top = name.split('.')[0]
        candidates = [p for p in roots if (p / top).is_dir() or (p / (top + '.olean')).is_file()]
        assert candidates, ('namespace missing', top)
        selected = candidates[0]
        selected_obj = selected / Path(*name.split('.')).with_suffix('.olean')
        assert selected_obj.is_file() and r['declared_external_guard'].get(str(selected_obj)) is not None, ('selected object mismatch', name, str(selected_obj))
        namespaces[top] = [str(p) for p in candidates]
    assert sha(receipt_path) == receipt_hash and sha(observation_path) == observation_hash
    assert sha(INPUT) == INPUT_SHA and sha(args.project_manifest) == PROJECT_MANIFEST_SHA
    result = {'status': 'PASS_PROVIDER_POINT_IN_TIME_AUDIT_OUTER_EXIT_UNOBSERVED', 'provider_receipt_sha256': receipt_hash,
              'terminal_observation_sha256': observation_hash, 'build_log_sha256': r['log_sha256'],
              'input_manifest_sha256': INPUT_SHA, 'project_manifest_sha256': PROJECT_MANIFEST_SHA,
              'foundation_source_files': len(actual_source), 'foundation_artifacts': len(actual),
              'target_objects': len(r['objects']), 'guard_paths': len(r['declared_external_guard']),
              'aq29_direct_foundation_imports': len(needed), 'external_namespace_candidates': namespaces,
              'outer_process_exit_observed': False,
              'scope': 'Point-in-time independent rehash and direct-target coverage only; '
                       'the inner Lake exit is recorded as zero and terminal BUILT stdout was observed, '
                       'but the outer process exit code was not captured. This is '
                       'not an independent Foundation rebuild, source-to-object provenance '
                       'for inherited package objects, dynamic-load audit or project replay.'}
    out = HERE / 'receipt.json'
    with out.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True); stream.write('\n')
    print(result['status'], sha(out), flush=True)

if __name__ == '__main__':
    main()
