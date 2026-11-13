"""Independent finite checks of the H3 de Bruijn operations.

These checks exercise naturality identities used in the written proof.
They are not a formal verification of the checker or the iPRA bridge.
Run with the proposed checker directory, optionally followed by its filename.
"""
import importlib.util
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys


def main():
    directory = Path(sys.argv[1]).resolve()
    filename = sys.argv[2] if len(sys.argv) > 2 else 'h3_checker.py'
    checker = directory / filename
    spec = importlib.util.spec_from_file_location('h3_audited', checker)
    h3 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(h3)
    rng = random.Random(20261113)

    def term(n, fuel):
        tag = rng.randrange(3) if fuel else 0
        if tag == 0:
            return rng.randrange(n + 1)
        if tag == 1:
            return [term(n, fuel - 1)]
        return [term(n, fuel - 1), term(n, fuel - 1), term(n + 1, fuel - 1)]

    def formula(n, fuel):
        if fuel and rng.randrange(3) == 0:
            return [formula(n + 2, fuel - 1)]
        return [term(n, fuel), term(n, fuel)]

    counts = {'export_after_lift': 0, 'gate_naturality': 0,
              'clause_specialization_naturality': 0, 'gate_zero_reflexive': 0,
              'gate_one_computation': 0, 'diagonal_renaming': 0}
    for _ in range(1200):
        n = rng.randrange(6)
        a = formula(n, rng.randrange(5))
        assert h3.formula(a, n)
        assert h3.export(h3.lift(a, f=True)) == a
        counts['export_after_lift'] += 1
        assert h3.gate(h3.lift(a, f=True)) == h3.lift(h3.gate(a), f=True, cutoff=1)
        counts['gate_naturality'] += 1
        gate_zero = h3.instance(h3.gate(a), [0], True)
        while len(gate_zero) == 1:
            gate_zero = gate_zero[0]
        assert gate_zero[0] == gate_zero[1]
        counts['gate_zero_reflexive'] += 1
        gate_one = h3.instance(h3.gate(a), [[0]], True)
        source = a
        while len(source) == 1:
            source, gate_one = source[0], gate_one[0]
        left, right = gate_one
        assert left[0] == 0 and right[0] == [0]
        assert left[1] == right[1] == source[0]
        assert h3.instance(right[2], [[0, right[1], right[2]]]) == source[1]
        counts['gate_one_computation'] += 1
        b = formula(n + 1, rng.randrange(4))
        t = term(n, rng.randrange(4))
        assert h3.lift(h3.instance(b, [t], True), f=True) == h3.instance(
            h3.lift(b, f=True, cutoff=1), [h3.lift(t)], True)
        counts['clause_specialization_naturality'] += 1
        matrix = formula(n + 2, rng.randrange(4))
        assert h3.diagonal(matrix) == h3.diagonal(h3.lift(matrix, f=True, cutoff=2))
        counts['diagonal_renaming'] += 1

    # False in the standard natural-number reading: D_xy(y=0).
    false_goal = [[1, 0]]
    invalid = [false_goal, ['intro', false_goal, 0, None]]
    ordinary = subprocess.run([sys.executable, '-I', '-S', '-B', str(checker)],
                              input=json.dumps(invalid), text=True, capture_output=True)
    optimized = subprocess.run([sys.executable, '-I', '-S', '-B', '-O', str(checker)],
                               input=json.dumps(invalid), text=True, capture_output=True)
    assert ordinary.returncode == 0 and ordinary.stdout == 'False\n'
    assert optimized.returncode != 0
    print(json.dumps({'checker': filename, 'sha256': hashlib.sha256(checker.read_bytes()).hexdigest(),
                      'seed': 20261113, 'syntax_checks': counts,
                      'false_intro_rejected': True,
                      'optimized_execution_refused': True,
                      'formal_verification': False}, indent=2))


if __name__ == '__main__':
    main()
