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
expected = 'd70bbed8b36895ffcf144f51bf78287e03fb2942d62c016ac9c845e691820b9b'
if hashlib.sha256(raw).hexdigest() != expected:
    raise RuntimeError('candidate graph hash drift')
graph = json.loads(raw)
lines = [
  'import DiophantineConsistency.Compact44.P64Graph',
  '',
  '/-! Generated q-cube first-root candidate.  No zero-equivalence is asserted here. -/',
  'set_option autoImplicit false',
  'set_option Elab.async false',
  'noncomputable section',
  'namespace P64QCube79',
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
lines.extend(['  -- END GENERATED GRAPH', '  ⟨A0, M, W, Na, Lt, polynomial⟩', '', 'end P64QCube79', ''])
text='\n'.join(lines)
path=here/'P64QCube79.lean'
if sys.argv[1:] == ['--write']:
    with path.open('x') as out: out.write(text)
elif sys.argv[1:]:
    raise SystemExit('usage: python3 -I -S -B generate_lean.py [--write]')
elif path.read_text()!=text:
    raise SystemExit('generated Lean graph differs')
print('PASS: 79 generated gate rows; source transcription only, no Lean check')
