#!/usr/bin/env python3
"""Standard-library regression tests, independent of every search program."""
import copy
import itertools
import json
import subprocess
import sys
import tempfile
from pathlib import Path
import verify_selective as checker

ROOT = Path(__file__).resolve().parent
REQUIRED = [
    'verify_selective.py', 'code_v1.json', 'SOURCE_PINS.json',
    'upstream_parent_quartic31.json', 'upstream_QUADRATIC_TARGETS.json',
    'source_support.json',
]


def main():
    canonical = checker.audit()
    failures = {}
    original = json.loads((ROOT / 'code_v1.json').read_text())
    mutations = {
        'repeated_weight': lambda c: c['weights'].__setitem__(1, c['weights'][2]),
        'zero_nonpadding_weight': lambda c: c['weights'].__setitem__(1, 0),
        'negative_target': lambda c: c['targets'].__setitem__(0, -1),
        'repeated_target': lambda c: c['targets'].__setitem__(0, c['targets'][1]),
        'missing_row': lambda c: c['order'].pop(),
        'negative_reversed_exponent': lambda c: c['targets'].__setitem__(0, 0),
        'target_interference': lambda c: c['targets'].__setitem__(1, c['targets'][1] + 1),
        'stale_summary': lambda c: c.__setitem__('maximum_target', 5191),
    }
    with tempfile.TemporaryDirectory(prefix='selective-replay-') as td:
        folder = Path(td)
        for name, mutate in mutations.items():
            c = copy.deepcopy(original)
            mutate(c)
            path = folder / (name + '.json')
            path.write_text(json.dumps(c))
            try:
                checker.audit(path)
            except ValueError as e:
                failures[name] = str(e)
            else:
                raise ValueError('Mutation not rejected: ' + name)
        replay = folder / 'standalone'
        replay.mkdir()
        for name in REQUIRED:
            (replay / name).write_bytes((ROOT / name).read_bytes())
        command = [sys.executable, str(replay / 'verify_selective.py')]
        plain = subprocess.run(command, cwd=folder, check=True, capture_output=True).stdout
        optimized = subprocess.run(command[:1] + ['-O'] + command[1:], cwd=folder, check=True, capture_output=True).stdout
        checker.require(plain == optimized, 'Python -O changed result')
        checker.require(json.loads(plain) == canonical, 'standalone replay changed result')
        checker.require(plain == (ROOT / 'verification_v1.json').read_bytes(), 'committed verification receipt is stale')
        # Provenance checks deliberately reject one-byte source corruption.
        for name in ['upstream_parent_quartic31.json', 'upstream_QUADRATIC_TARGETS.json', 'code_v1.json']:
            path = replay / name
            original_bytes = path.read_bytes()
            path.write_bytes(original_bytes + b'\n')
            bad = subprocess.run(command, cwd=folder, capture_output=True)
            checker.require(bad.returncode != 0, 'one-byte mutation escaped hash pin: ' + name)
            failures['byte_pin_' + name] = 'rejected'
            path.write_bytes(original_bytes)

    # Exhaustive tiny-instance check of the carry lemma is a regression test;
    # the mathematical argument in section.tex proves its unbounded version.
    cases = 0
    for base in [4, 8, 16, 32]:
        coefficients = range(1 - base // 4, base // 4)
        for a in itertools.product(coefficients, repeat=3):
            value = sum(c * base ** i for i, c in enumerate(a))
            if value <= 0:
                continue
            for selector in range(8):
                target = [i for i in range(3) if selector >> i & 1]
                pad = sum(base ** i for i in target)
                J = 2 * value + pad
                carry_free = (J & ((base - 2) * pad)) == 0
                checker.require(carry_free == all(a[i] == 0 for i in target), 'sparse carry lemma failed')
                cases += 1
    return {
        'status': 'PASS',
        'standalone_without_search_or_sibling_tree': True,
        'byte_identical_standard_and_optimized_replay': True,
        'mutation_rejections': failures,
        'sparse_padding_regression_cases': cases,
        'source_extraction_checks': canonical['finite_interactions_checked'],
        'formal_target_identities': canonical['formal_target_polynomial_identities'],
        'scope': 'Finite regression and certificate checks; unbounded carry and extraction proofs are in section.tex.',
    }


if __name__ == '__main__':
    print(json.dumps(main(), indent=2) + '\n', end='')
