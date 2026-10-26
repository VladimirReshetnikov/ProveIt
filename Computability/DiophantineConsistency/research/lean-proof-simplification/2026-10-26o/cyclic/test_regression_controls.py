#!/usr/bin/env python3
"""Verify read-only behavior and explicit regression failures, including under -O."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def snapshot(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file()}


def run(root, optimized):
    command = [sys.executable]
    if optimized:
        command.append('-O')
    command.append(str(root / 'regression.py'))
    return subprocess.run(command, capture_output=True, text=True, check=False)


def fixture(root):
    shutil.copy(ROOT / 'regression.py', root / 'regression.py')
    shutil.copytree(ROOT / 'source', root / 'source')
    shutil.copytree(ROOT / 'candidates', root / 'candidates')


def main():
    cases = []
    for optimized in (False, True):
        mode = 'python -O' if optimized else 'python'
        with TemporaryDirectory(prefix='cyclic-regression-check-') as tmp:
            root = Path(tmp)
            fixture(root)
            before = snapshot(root)
            result = run(root, optimized)
            require(result.returncode == 0, f'{mode}: ordinary fixture failed: {result.stderr}')
            require(before == snapshot(root), f'{mode}: default invocation modified fixture files')
            require(result.stdout == (ROOT / 'regression-results.json').read_text(),
                    f'{mode}: output differs from recorded results')
            cases.append({'mode': mode, 'case': 'ordinary_read_only', 'passed': True})
        mutations = (
            ('changed_statement', 'candidates/CurrentCellCycle2011.lean',
             lambda s: s.replace('∃ j < N', '∃ j ≤ N', 1), 'Declaration signature changed'),
            ('unproved_candidate', 'candidates/CurrentCellCycle2011.lean',
             lambda s: s + '\naxiom injected_control : False\n', 'Unproved or axiomatic candidate'),
            ('arithmetic_control', 'regression.py',
             lambda s: s.replace('expected = word(prefix + south[:9-k])',
                                 'expected = word(prefix + south[:9-k]) + 1', 1),
             'Prefix identity failed'),
            ('wrong_source_snapshot', 'source/CurrentCellCycle2011.lean',
             lambda s: s + '\n', 'Source snapshot does not match pinned baseline'),
        )
        for name, path, mutate, expected_diagnostic in mutations:
            with TemporaryDirectory(prefix='cyclic-regression-control-') as tmp:
                root = Path(tmp)
                fixture(root)
                target = root / path
                old = target.read_text()
                changed = mutate(old)
                require(changed != old, f'{name}: control mutation did not change its target')
                target.write_text(changed)
                before = snapshot(root)
                result = run(root, optimized)
                require(result.returncode != 0, f'{mode}: malformed control {name} unexpectedly passed')
                require(expected_diagnostic in result.stderr,
                        f'{mode}: {name} failed for an unexpected reason: {result.stderr}')
                require(before == snapshot(root), f'{mode}: failed control {name} modified fixture files')
                cases.append({'mode': mode, 'case': name, 'rejected_as_expected': True})
    print(json.dumps({'not_a_lean_proof': True, 'checks': cases}, indent=2))


if __name__ == '__main__':
    main()
