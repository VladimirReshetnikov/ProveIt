import json
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).parent


def zero(a, h=0):
    return [1, [], a, h]


def refl(a):
    p = zero(a)
    return [3, 0, p, p]


def sym(p, lhs):
    return [3, 0, refl(lhs), p]


z = -1
base = zero([])
successor = [2, z, [], 0]
lhs = [[z], [], 0]
step = [3, 0, [0, 0], sym(successor, lhs)]
induction = [7, [[], [0, [], 0], []], step]
use_induction = [4, induction, base, [[]]]
case = [6, [], [[], 1, 1], [0, 0]]
use_case = [4, [0, 0], refl(-1), []]
elimination = [5, case, [3, [], use_case, refl([])]]
compound_case = [6, [], [[1], 1, 1], [7, [[], [-1], [-1]], refl([-1])]]
tests = [
    ('zero', base, [[], [[], [], 0], []]),
    ('successor', [2, [], [], 0], [[], [[[]], [], 0], [[], [], 0]]),
    ('reflexivity', refl([]), [[], [], []]),
    ('induction_using_hypothesis', induction, [[1], [0, [], 0], []]),
    ('closure_use', use_induction, [[], [[[]], [], 0], []]),
    ('case_introduction', case, [[2], 1, 1]),
    ('case_elimination_using_major', elimination, [[], [], []]),
    ('compound_case', compound_case, [[2, 1], 1, 1]),
    ('escaping_eigenparameter', [5, case, use_case], None),
    ('wrong_induction_step', [7, [[], 0, []], [0, 0]], None),
    ('future_witness', [6, -1, [[], 1, 1], [0, 0]], None),
    ('free_public_variable', zero(-1), None),
    ('malformed_boolean', [1, False, [], 0], None),
    ('malformed_constructor', [8], None),
]
rows = []
for optimized in (False, True):
    for name, proof, expected in tests:
        command = [sys.executable] + (['-O'] if optimized else []) + [str(BASE / 'synth.py')]
        p = subprocess.run(command, input=json.dumps(proof), capture_output=True, text=True)
        accepted = p.returncode == 0
        output = json.loads(p.stdout) if accepted else None
        ok = output == expected and accepted == (expected is not None)
        rows.append(dict(name=name, optimized=optimized, expected=expected, output=output, ok=ok))
        if not ok:
            print(name, optimized, output, expected, p.stderr)
            raise SystemExit(1)
(BASE / 'synthesis_tests.json').write_text(json.dumps(rows, indent=2) + '\n')
print(f'{len(rows)} synthesis executions, zero failures')
