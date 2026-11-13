"""Reproduce syntax checks and the controls delimiting the semantic theorem.

The semantic theorem is the written proof in second_dummy_proof.md.
No finite test is used to assert that every certificate for a goal fails.
"""
import ast
import json
import subprocess
import sys
from pathlib import Path

from canonical_goal import formula

ROOT = Path(__file__).resolve().parents[1]
CONTROL = ROOT / 'controls/checker_strict_tokens317.py'
module = ast.parse(CONTROL.read_text())
check = next(n for n in module.body if isinstance(n, ast.FunctionDef) and n.name == 'c')
opening = ast.Expression(check.body[0].value)
namespace = {'k': 0, 'g': [], 'c': object()}
namespace['i'] = eval(compile(ast.fix_missing_locations(opening), '<validator>', 'eval'), namespace)

checks = []
for label, goal, expected_sorted, expected_exact in [
    ('ordinary reflexivity', [1, 1], True, True),
    ('first padding slot', [[3], [1]], True, False),
    ('second padding slot obstruction', [[5], [1]], True, False),
    ('out-of-range slot', [[7], [1]], False, False),
    ('actual D variable', [[3, 3]], True, True),
    ('actual D variable below successor', [[[7], [7]]], True, True),
    ('guarded D equation', [[[5, 1, 7], [5, 1, 7]]], True, True),
    ('Boolean masquerading as zero', [True, 1], True, False),
]:
    # The extracted parity scan assumes alphabet validation; it accepts True.
    # The complete strict checker rejects True by its whole-input alphabet test.
    try:
        namespace['i'](goal)
        sorted_valid = True
    except Exception:
        sorted_valid = False
    exact_valid = formula(goal)
    assert sorted_valid == expected_sorted, (label, sorted_valid)
    assert exact_valid == expected_exact, (label, exact_valid)
    checks.append(dict(label=label, goal=goal, sorted_scan=sorted_valid,
                       exact_encoder_image=exact_valid))

runs = []
for label, stack, expected in [
    ('nonzero iterator dummy reading refuted',
     [[0, 0, 3, 1], [[1, 3, 1], 1]], True),
    ('nonzero first successor dummy reading refuted',
     [[0, 3, 1, [7]], [[[3], 1, [7]], [[3, 1, [7]]]]], True),
    ('second successor dummy blocked in recursive image',
     [[0, 5, 1, [7]], [[[5], 1, [7]], [[5, 1, [7]]]]], False),
]:
    result = subprocess.run([sys.executable, str(CONTROL)], input=json.dumps(stack),
                            text=True, capture_output=True, timeout=5)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    assert accepted == expected, (label, result.returncode, result.stdout)
    runs.append(dict(label=label, accepted=accepted, stack=stack))

print(json.dumps(dict(syntax_checks=checks, computation_boundaries=runs,
                     claim='The universal nonacceptance theorem is mathematical, not established by these finite checks.'), indent=2))
