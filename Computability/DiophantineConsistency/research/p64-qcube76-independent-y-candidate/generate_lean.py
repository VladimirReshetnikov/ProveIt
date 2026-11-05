#!/usr/bin/env python3
"""Generate an unchecked Lean graph transcription for the P64 q-cube candidate."""
import hashlib
import json
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here = Path(__file__).resolve().parent
source = here/'graph.json'
raw = source.read_bytes()
expected = '196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c'
if hashlib.sha256(raw).hexdigest() != expected:
    raise RuntimeError('candidate graph hash drift')
graph = json.loads(raw)
lines = [
  'import DiophantineConsistency.Compact44.P64Graph',
  '',
  '/-! Generated q-cube independent-y candidate.  No zero-equivalence is asserted here. -/',
  'set_option autoImplicit false',
  'set_option Elab.async false',
  'noncomputable section',
  'namespace P64QCube76Y',
  'open LO LO.FirstOrder LO.FirstOrder.Arithmetic',
  'open scoped LO.FirstOrder.Arithmetic',
  'open DiophantineConsistency AdaptiveEquationSyntax2011',
  '',
  'def graph (p : Fin 4 → ℤ) : P64Graph.Graph :=',
]
for idx, name in enumerate(graph['witnesses']):
    lines.append(f'  let {name} : Expr (Fin 14) := .var {idx}')
for idx, name in enumerate(graph['fixed_numerals']):
    lines.append(f'  let {name} : Expr (Fin 14) := .constant (p {idx})')
lines.append('  -- BEGIN GENERATED GRAPH')
for name, op, x, y in graph['source']:
    lines.append(f'  let {name} := {x} {op} {y}')
lines.extend(['  -- END GENERATED GRAPH', '  ⟨A0, M, W, Na, Lt, polynomial⟩', '', 'end P64QCube76Y', ''])
text='\n'.join(lines)
path=here/'P64QCube76Y.lean'
if sys.argv[1:] == ['--write']:
    with path.open('x') as out: out.write(text)
elif sys.argv[1:]:
    raise SystemExit('usage: python3 -I -S -B generate_lean.py [--write]')
elif path.read_text()!=text:
    raise SystemExit('generated Lean graph differs')
print('PASS: 76 generated gate rows; source transcription only, no Lean check')
