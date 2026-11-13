#!/usr/bin/env python3
"""Reproduce a Lean expression source from the pinned retained graph."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent
root=here.parents[2]
graph=root/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
expected='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
raw=graph.read_bytes()
if hashlib.sha256(raw).hexdigest()!=expected:raise RuntimeError('graph hash mismatch')
data=json.loads(raw)
variables=['J','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
ports=['beta','K0','MC','MF']
if data['witnesses']!=variables or data['fixed_numerals']!=ports or len(data['source'])!=95 or data['output']!='P12':raise RuntimeError('graph metadata mismatch')
header='''import DiophantineConsistency.Ordinary12FreeJ

/-! A direct expression generated from a pinned 95-row graph. Correspondence
between this Lean source and an external file remains an explicit boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace FreeJRetainedDirectExpression
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ

def retainedExpression (p : Fin 4 → ℤ) : Expr (Fin 12) :=
'''
lines=[]
for i,v in enumerate(variables):lines.append(f'  let {v} : Expr (Fin 12) := .var {i}')
for i,v in enumerate(ports):lines.append(f'  let {v} : Expr (Fin 12) := .constant (p {i})')
seen=set(variables+ports)
for name,op,a,b in data['source']:
 if name in seen or op not in ('+','-','*'):raise ValueError('bad gate')
 for item in (a,b):
  if not isinstance(item,int) and item not in seen:raise ValueError('missing or forward operand')
 lines.append(f'  let {name} := {a} {op} {b}');seen.add(name)
footer='''
  P12

/-- Equality of the generated direct Lean expression and the formal graph,
for arbitrary integer ports. No equality with a filesystem file is asserted. -/
theorem retained_eq_literal (p : Fin 4 → ℤ) : retainedExpression p = literal p := by
  rfl

#print axioms FreeJRetainedDirectExpression.retained_eq_literal
end FreeJRetainedDirectExpression
'''
(here/'FreeJRetainedDirectExpression.lean').write_text(header+'\n'.join(lines)+footer)
print('PASS generated exact 95-gate direct source from pinned JSON')
