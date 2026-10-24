#!/usr/bin/env python3
"""Offline rebuild and exact audit. Python standard library only."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
steps = [
    'audit/check_normalization.py',
    'build_direct.py',
    'reduce_affine.py',
    'audit/check_interfaces.py',
    'audit/check_composition.py',
    'audit/check_horn.py',
    'audit/check_source_binding.py',
    'audit/check_structure.py',
    'audit/check_affine.py',
]
for step in steps:
    print('CHECK ' + step, flush=True)
    subprocess.run([sys.executable, str(ROOT / step)], cwd=ROOT, check=True)

natural = json.loads((ROOT / 'summary_affine.json').read_text())
integer = json.loads((ROOT / 'summary_integer.json').read_text())
expected = [14956, 670455, 3744, 11212, 11502, 26188, 724768]
observed = [natural['ordinary_polynomial_variables'],
            natural['ordinary_polynomial_monomials'],
            natural['input_existentials'], natural['nonlinear_wires'],
            natural['SOS_residuals'], integer['ordinary_polynomial_variables'],
            integer['ordinary_polynomial_monomials']]
if observed != expected:
    raise ValueError('sealed metrics changed: ' + repr(observed))
receipt = {'status':'PASS', 'steps':steps, 'natural':natural, 'integer':integer,
           'scope':'Complete exact finite artifact replay; ordinary unbounded proof in normalization.tex and UPSTREAM_MATHEMATICAL_AUDIT.md. No Lean build is claimed.'}
(ROOT / 'REPLAY.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({'status':'PASS','natural_variables':14956,'integer_variables':26188,'degree':4}))
