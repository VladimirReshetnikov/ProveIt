#!/usr/bin/env python3
"""Emit inert source from pinned graph to stdout; never launches Lean."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
p=ROOT/'research/adaptive87-four-square-current88-30/graph.json'; raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='293dac5175d4924812177a1e73a316bf5cc16bf1b5cef636388d9e110eebb7ed': raise RuntimeError('graph pin changed')
g=json.loads(raw)
print('''import DiophantineConsistency.AdaptiveFirstRootFactor87Literal
/-! Generated source only; no Lean elaboration or JSON theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.AdaptiveFourSquare88GraphDraft
open AdaptiveEquationSyntax2011
structure Graph where
  first : Expr (Fin 13)
  main : Expr (Fin 13)
  aux : Expr (Fin 13)
  strong : Expr (Fin 13)
  q : Expr (Fin 13)
  root : Expr (Fin 13)
  radicand : Expr (Fin 13)
  scale : Expr (Fin 13)
  a : Expr (Fin 13)
  c : Expr (Fin 13)
  mainRoot : Expr (Fin 13)
  f : Expr (Fin 13)
  I : Expr (Fin 13)
  V : Expr (Fin 13)
  y : Expr (Fin 13)
  output : Expr (Fin 13)
  parent : Expr (Fin 13)
def graph (p : Fin 4 → ℤ) : Graph :=''')
for j,name in enumerate(g['witnesses']):print(f'  let {name} : Expr (Fin 13) := .var {j}')
for j,name in enumerate(g['fixed_numerals']):print(f'  let {name} : Expr (Fin 13) := .constant (p {j})')
for out,op,left,right in g['source']: print(f'  let {out} := {left} {op} {right}')
print('''  let parent := (1+g72)*(Fa*((1+A0)*(1+A1)))-1
  ⟨A0,A1,Fa,g72,q,Z,g41,U,a,c,Dstar,f,I,V,g78,output,parent⟩
def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 13) := (graph p).output
theorem parent_eq (p : Fin 4 → ℤ) :
    (graph p).parent = AdaptiveFirstRootFactor87Literal.expressionAt87 p := by
  rfl
end DiophantineConsistency.AdaptiveFourSquare88GraphDraft''')
