#!/usr/bin/env python3
"""Mechanically name the exact 45 quoted prefixes; no Lean invocation."""
import hashlib
import json
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parent.parent
source = D / 'research/nine-seed38-jones-compact-lean-draft/Norm38MacroRecipe.lean'
if hashlib.sha256(source.read_bytes()).hexdigest() != '3756c5e056e9bfedd28aa1fca5d5aa01c6bbde8163332c70abced196cf6d3979':
    raise RuntimeError('source hash')
text = source.read_text()
rows = re.findall(r'^  let d(\d+) : Dag (\d+) := (.*)$', text, re.M)
if len(rows) != 46 or any(int(a) != i or int(b) != i for i, (a, b, _) in enumerate(rows)):
    raise RuntimeError('unexpected telescope')
if rows[0][2] != '.nil' or any(not expr.startswith(f'.snoc d{i-1} ') for i, (_, _, expr) in enumerate(rows) if i):
    raise RuntimeError('unexpected prefix relation')
lines = ['import DiophantineConsistency.Norm38MacroRecipe', '',
         '/-! Source-only split. The recipe identity has not yet been checked. -/',
         'set_option autoImplicit false', 'noncomputable section',
         'namespace DiophantineConsistency.Norm38MacroPrefixes',
         'open Norm38MacroLanguage', '']
for i, (_, _, expr) in enumerate(rows):
    lines.append(f'def d{i} : Dag {i} := {expr}')
lines += ['', '/-- Proposed identity of the original telescope and named final prefix. -/',
          'theorem recipe_eq_named : Norm38MacroRecipe.recipe = d45 := by',
          '  rfl', '', '#print axioms recipe_eq_named',
          'end DiophantineConsistency.Norm38MacroPrefixes']
encoded = ('\n'.join(lines) + '\n').encode()
out = P / 'Norm38MacroPrefixes.lean'
if sys.argv[1:] == ['--write']:
    with out.open('xb') as f: f.write(encoded)
elif sys.argv[1:] == ['--check']:
    if out.read_bytes() != encoded: raise RuntimeError('split differs')
    print(json.dumps({'status': 'PASS_MECHANICAL_PREFIX_SPLIT_ONLY',
                      'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                      'split_sha256': hashlib.sha256(encoded).hexdigest(), 'prefixes': 46,
                      'scope': 'Exact textual node bodies, not Lean compilation or evaluator equality.'}, sort_keys=True))
else:
    raise SystemExit('expected --write or --check')
