#!/usr/bin/env python3
"""Run ordinary/optimized deterministic builds and deliberate failure regression."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from common import ROOT, canonical_json, require, sha256, VerificationError
import independent_series


def run_process(args, expected=0, cwd=None):
    result = subprocess.run(args, cwd=cwd or ROOT, capture_output=True, text=True)
    require((result.returncode == 0) == (expected == 0), 'Unexpected process status: '+repr(args)+'\n'+result.stdout+result.stderr)
    return result


def tree(path):
    return {str(p.relative_to(path)): sha256(p) for p in sorted(path.rglob('*')) if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--terms', type=int, default=200)
    args = parser.parse_args()
    require(8 <= args.terms <= 240, 'Test terms must be 8..240')
    checks = []
    with tempfile.TemporaryDirectory(prefix='report170-test-') as raw:
        tmp = Path(raw)
        normal, optimized = tmp/'normal', tmp/'optimized'
        for flag, destination in [([], normal), (['-O'], optimized)]:
            command = [sys.executable]+flag+[str(ROOT/'build.py'), '--terms', str(args.terms), '--output', str(destination)]
            run_process(command, cwd=tmp)
        require(tree(normal) == tree(optimized), 'Normal and python -O results are not byte-identical')
        checks.append('Normal and optimized builds are byte-identical, including manifests')
        before = tree(normal)
        run_process([sys.executable, str(ROOT/'build.py'), '--output', str(normal)], expected=1)
        require(before == tree(normal), 'No-clobber test changed existing output')
        checks.append('Existing output rejected without modifying a byte')
        safe = tmp/'safe-parent'
        safe.mkdir()
        sentinel = safe/'sentinel'
        sentinel.write_bytes(b'preserve this exact content\n')
        sentinel_hash = sha256(sentinel)
        linked_parent = tmp/'linked-parent'
        linked_parent.symlink_to(safe, target_is_directory=True)
        linked_leaf = tmp/'linked-leaf'
        linked_leaf.symlink_to(sentinel)
        linked_directory = tmp/'linked-directory'
        linked_directory.symlink_to(safe, target_is_directory=True)
        dangling = tmp/'dangling-leaf'
        dangling.symlink_to(tmp/'absent-target')
        bad_parent = tmp/'dangling-parent'
        bad_parent.symlink_to(tmp/'absent-parent', target_is_directory=True)
        unsafe = [linked_parent/'new-results', linked_leaf, linked_directory, dangling,
                  bad_parent/'new-results', safe/'..'/'traversed-results', sentinel]
        for flag in ([], ['-O']):
            for target in unsafe:
                run_process([sys.executable]+flag+[str(ROOT/'build.py'), '--terms', '8', '--output', str(target)], expected=1)
        require(sha256(sentinel) == sentinel_hash, 'Unsafe-path tests altered a preexisting file')
        require(not (safe/'new-results').exists() and not (tmp/'traversed-results').exists(), 'Unsafe output path was created')
        require(not (tmp/'absent-target').exists() and not (tmp/'absent-parent').exists(), 'Dangling symlink target was created')
        checks.append('Seven unsafe/existing destination cases rejected in both modes, preserving sentinel bytes')

        for bad in ('7', '241'):
            target = tmp/('bad-'+bad)
            run_process([sys.executable, str(ROOT/'build.py'), '--terms', bad, '--output', str(target)], expected=1)
            require(not target.exists(), 'Invalid term bound created output')
        checks.append('Lower and upper CLI bounds are enforced before work')
        for flag in ([], ['-O']):
            run_process([sys.executable]+flag+['-c', 'from common import require; require(False, "intentional failure")'], expected=1)
            run_process([sys.executable]+flag+['-c', 'import exact_counts; exact_counts.run(7)'], expected=1)
        checks.append('Deliberately failed predicates raise under ordinary and optimized Python')
        algebra = json.loads((normal/'exact_algebra.json').read_text())
        altered = copy.deepcopy(algebra)
        altered['exact_d_polynomials_ascending_v'][1][0][0] = '0'
        try:
            independent_series.run(altered)
        except VerificationError:
            checks.append('Corrupt algebraic certificate rejected by independent series comparison')
        else:
            raise VerificationError('Corrupt algebraic certificate was accepted')
        # Separate fixture-integrity failure, without changing the release fixture.
        run_process([sys.executable, '-O', '-c', 'from pathlib import Path; import common; common.sha256=lambda p: "0"*64; common.validate_fixtures()'], expected=1)
        checks.append('Fixture hash corruption rejected under optimized Python')
        # Hash verification also succeeds independently of the invoking directory.
        manifest = json.loads((normal/'manifest.json').read_text())
        for name, digest in manifest['artifact_sha256'].items():
            require(sha256(normal/name) == digest, 'Result artifact hash mismatch')
        checks.append('Portable invocation and all artifact hashes verified')
    print(canonical_json({'status': 'PASS', 'terms': args.terms, 'checks': checks}).decode('utf-8'), end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
