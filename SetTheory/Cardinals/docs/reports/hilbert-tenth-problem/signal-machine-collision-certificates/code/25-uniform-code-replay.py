#!/usr/bin/env python3
"""Offline isolated replay of inspected arithmetic checkers, not a CA compiler.
Verifies frozen pins before and after, never executes inherited source, and writes
only to a new/empty scratch directory outside the release. Assertions are enabled.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PINS = {
    'science': '0fb634cca9f665b44c3601509a6cef49391599064a9715164227fc475260be4c',
    'audit': '7719ee3d73a9811975218309d61db5ec6e622977f3cc6197c76771f7c7edb085',
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_file(base, rel):
    q = PurePosixPath(rel)
    require(not q.is_absolute() and '..' not in q.parts and str(q) == rel,
            'Unsafe member path: ' + rel)
    path = base / rel
    require(all(not p.is_symlink() for p in (path, *path.parents)),
            'Symlink rejected: ' + str(path))
    require(path.is_file() and path.resolve().is_relative_to(base.resolve()),
            'Missing or escaping file: ' + rel)
    return path


def verify_frozen():
    result = {}
    for name, pin in PINS.items():
        base = ROOT / 'frozen' / name
        manifest = safe_file(base, 'MANIFEST.json')
        require(digest(manifest) == pin, 'Frozen manifest changed: ' + name)
        records = json.loads(manifest.read_text())['files']
        for row in records:
            path = safe_file(base, row['path'])
            require(path.stat().st_size == row['bytes'], 'Byte length mismatch: ' + row['path'])
            require(digest(path) == row['sha256'], 'Hash mismatch: ' + row['path'])
        result[name] = {'manifest_sha256': pin, 'verified_entries': len(records)}
    sums = safe_file(ROOT / 'frozen' / 'science', 'SHA256SUMS')
    for line in sums.read_text().splitlines():
        sha, rel = line.split('  ', 1)
        require(digest(safe_file(sums.parent, rel)) == sha, 'Science SHA256SUMS mismatch: ' + rel)
    extra = ROOT / 'frozen' / 'manuscript-audit'
    sums = safe_file(extra, 'SHA256SUMS')
    require(digest(sums) == 'e29f6d321d0befe23b8bdfa77509552c499e883e504a94c98b5e000b5a581edd',
            'Manuscript audit manifest changed')
    lines = sums.read_text().splitlines()
    for line in lines:
        sha, rel = line.split('  ', 1)
        require(digest(safe_file(extra, rel)) == sha, 'Manuscript audit hash mismatch: ' + rel)
    result['manuscript-audit'] = {'manifest_sha256': digest(sums), 'verified_entries': len(lines)}
    prior = safe_file(ROOT / 'frozen' / 'report49', 'report49.tex')
    require(digest(prior) == 'c78133175cca8be54cbf230af1423b77b0ee3bcf6d71bd816f6478800ccf9056',
            'Report49 inert manuscript changed')
    result['report49'] = {'tex_sha256': digest(prior)}
    frame = ROOT / 'frozen' / 'frame-obstruction'
    sums = safe_file(frame, 'MANIFEST.sha256')
    require(digest(sums) == '5c06a46369d76f41c7bc4fb4c775bead1b907bab4c016ca89f3fffe701f98389',
            'Frame-obstruction manifest changed')
    lines = sums.read_text().splitlines()
    for line in lines:
        sha, rel = line.split('  ', 1)
        require(digest(safe_file(frame, rel)) == sha, 'Frame-obstruction hash mismatch: ' + rel)
    result['frame-obstruction'] = {'manifest_sha256': digest(sums), 'verified_entries': len(lines)}
    addendum = ROOT / 'frozen' / 'manuscript-audit-corollary'
    sums = safe_file(addendum, 'SHA256SUMS')
    require(digest(sums) == '6b141fa0522f0fbcad8ad39e397eada4d962e113958552016fa722c1fb18acb9',
            'Final manuscript audit manifest changed')
    lines = sums.read_text().splitlines()
    for line in lines:
        sha, rel = line.split('  ', 1)
        require(digest(safe_file(addendum, rel)) == sha, 'Final manuscript audit hash mismatch: ' + rel)
    result['manuscript-audit-corollary'] = {'manifest_sha256': digest(sums), 'verified_entries': len(lines)}
    return result


def prepare_output(raw):
    absolute = Path(os.path.abspath(raw))
    require(all(not p.is_symlink() for p in (absolute, *absolute.parents)), 'Output symlink rejected')
    target = absolute.resolve()
    require(target != ROOT and ROOT not in target.parents and target not in ROOT.parents,
            'Output must be external and must not contain the release')
    require(not target.exists() or (target.is_dir() and not any(target.iterdir())),
            'Output must be new or empty')
    target.mkdir(parents=True, exist_ok=True)
    return target


def run(output):
    before = verify_frozen()
    target = prepare_output(output)
    receipts = {}
    env = dict(os.environ)
    env.pop('PYTHONOPTIMIZE', None)
    env.update(PYTHONDONTWRITEBYTECODE='1', TZ='UTC')
    for name, script, receipt in (
        ('science', 'check_arithmetic.py', 'arithmetic-check-results.json'),
        ('audit', 'check_adversarial.py', 'CHECK-RESULTS.json'),
        ('manuscript-audit', 'check_manuscript_algebra.py', 'CHECK-RESULTS.json'),
        ('frame-obstruction', 'independent_check.py', 'check_result.json'),
        ('manuscript-audit-corollary', 'check_frame_obstruction.py', 'CHECK-RESULTS.json'),
    ):
        destination = target / name
        destination.mkdir()
        original = safe_file(ROOT / 'frozen' / name, script)
        shutil.copyfile(original, destination / script)
        with (destination / 'run.log').open('wb') as log:
            proc = subprocess.run([sys.executable, '-I', script], cwd=destination,
                                  env=env, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        require(proc.returncode == 0, 'Checker failed: ' + str(destination / 'run.log'))
        generated = destination / receipt
        expected = safe_file(ROOT / 'frozen' / name, receipt)
        require(generated.read_bytes() == expected.read_bytes(), 'Receipt differs: ' + name)
        receipts[name] = {'status': 'PASS', 'checker_sha256': digest(original),
                          'receipt_sha256': digest(generated),
                          'counts': json.loads(generated.read_text()).get('counts', {k: v for k, v in json.loads(generated.read_text()).items() if isinstance(v, int) and not isinstance(v, bool)})}
    after = verify_frozen()
    require(before == after, 'Frozen evidence changed during replay')
    result = {'status': 'PASS', 'scope': 'Exact deterministic replay of finite arithmetic fixtures',
              'frozen_manifests': after, 'checks': receipts,
              'assertions_enabled_in_children': True, 'executed_upstream_programs': False,
              'executed_saved_schedules': False, 'network_used': False,
              'frozen_inputs_unchanged': True}
    (target / 'replay-receipt.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    if args.verify_only:
        require(args.output is None, 'Do not combine --verify-only and --output')
        result = {'status': 'PASS', 'frozen_manifests': verify_frozen()}
    else:
        require(args.output is not None, '--output is required')
        result = run(args.output)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
