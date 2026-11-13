#!/usr/bin/env python3
"""Exercise the actual runner's axiom-report parser without invoking Lean."""
import ast
import re
from pathlib import Path

path = Path(__file__).with_name('run.py')
tree = ast.parse(path.read_text())
func = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'check_report')
scope = {'re': re}
exec(compile(ast.Module(body=[func], type_ignores=[]), str(path), 'exec'), scope)
check = scope['check_report']
name = "'Trace74NaturalBlock.natural_block' "
cases = [
    (name+'does not depend on any axioms\n', True),
    (name+'depends on axioms: [propext, Classical.choice, Quot.sound]\n', True),
    (name+'depends on axioms: [propext,\n Classical.choice, Quot.sound]\n', True),
    (name+'depends on axioms: [propext, sorryAx]\n', False),
    (name+'depends on axioms: [propext, propext]\n', False),
    (name+'depends on axioms: [propext,,Quot.sound]\n', False),
    (name+'depends on axioms: []\n', False),
    (name+'depends on axioms: [propext]\nextra\n', False),
    ('garbage\n'+name+'depends on axioms: [propext]\n', False),
    (name+'depends on axioms: [propext]\n'+name+'depends on axioms: [propext]\n', False),
    ("'Other.theorem' depends on axioms: [propext]\n", False),
]
for i, (text, want) in enumerate(cases):
    if check(text) != want:
        raise SystemExit('report control failed: '+str(i))
print('PASS:', len(cases), 'report controls')
