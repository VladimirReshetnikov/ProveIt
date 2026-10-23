#!/usr/bin/env python3
"""Emit a closed Lean constructor proposal from the authored literal local data.

Output has no sorry/axiom placeholders, but has NOT been kernel compiled here.
Its input and target APIs are pinned in SOURCE_PINS.json.
"""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
d=json.loads((ROOT/'stack_step_quartic.json').read_text())
def var(x):
    if x in ['S','Sp']:return f'(.var (.inl {0 if x=="S" else 1}))'
    j=['a','b','c','u','v'].index(x) if not x.startswith('q') else 5+int(x[1:])
    return f'(.var (.inr {j}))'
def term(t):
    m=t['monomial']; c=t['coefficient']
    factors=[var(x) for x in m]
    if c!=1 or not factors:factors.insert(0,f'(.constant ({c} : ℤ))')
    return '('+' * '.join(factors)+')'
def expr(row):return '('+' + '.join(term(t) for t in row)+')'
s='''import DiophantineConsistency.RemainderRepresentation
import DiophantineConsistency.BoundedForallRepresentation
import DiophantineConsistency.QuarticCompiler
import Mathlib.Data.Fin.VecNotation

/-!
Closed constructor PROPOSAL for the one-stack proof equation.
Pin: beb0192cb8dc36f78c369c080f2adfbc1887a486.
No K215 transition table or Jones finalizer is used.
This file has NOT been elaborated or kernel compiled in this packet.
The full final polynomial has NOT been expanded or counted.
-/
namespace DiophantineConsistency.OneStackProposal

-- Exposed coordinates: old stack and new stack. Hidden: a,b,c,u,v,q0,...,q83.
def stepPolynomial : Expr (Fin 2 ⊕ Fin 89) :=
'''
for i,row in enumerate(d['quadratic_residuals']):s+=f'  let r{i} : Expr (Fin 2 ⊕ Fin 89) := {expr(row)}\n'
s+='  '+ ' + '.join(f'r{i} * r{i}' for i in range(len(d['quadratic_residuals'])))+'\n\n'
s+='''def stepRep := (Rep.equality stepPolynomial 0).existsBlock

-- Outside coordinates: path length t, beta numerator x, beta step y.
def betaValue (x y i : ℕ) : ℕ := x % ((i + 1) * y + 1)

def betaGraph {σ : Type} {x y i : (σ → ℕ) → ℕ}
    (rx : GraphRep x) (ry : GraphRep y) (ri : GraphRep i) :
    GraphRep (fun v => betaValue (x v) (y v) (i v)) :=
  rx.mod (((ri.add (GraphRep.constant 1)).mul ry).add (GraphRep.constant 1))

def currentStackGraph : GraphRep (fun v : Option (Fin 3) → ℕ =>
    betaValue (v (some 1)) (v (some 2)) (v none)) :=
  betaGraph (GraphRep.coordinate (some 1)) (GraphRep.coordinate (some 2))
    (GraphRep.coordinate none)

def nextStackGraph : GraphRep (fun v : Option (Fin 3) → ℕ =>
    betaValue (v (some 1)) (v (some 2)) (v none + 1)) :=
  betaGraph (GraphRep.coordinate (some 1)) (GraphRep.coordinate (some 2))
    ((GraphRep.coordinate none).add (GraphRep.constant 1))

def stepInputs : Fin 2 → (Option (Fin 3) → ℕ) → ℕ :=
  ![fun v => betaValue (v (some 1)) (v (some 2)) (v none),
    fun v => betaValue (v (some 1)) (v (some 2)) (v none + 1)]

def stepGraphs : ∀ j : Fin 2, GraphRep (stepInputs j) :=
  Fin.cases currentStackGraph (Fin.cases nextStackGraph (fun j => Fin.elim0 j))

def everyStep := (Rep.compose stepRep stepGraphs).boundedForall (0 : Fin 3)

def initial : GraphRep (fun v : Fin 3 → ℕ => betaValue (v 1) (v 2) 0) :=
  betaGraph (GraphRep.coordinate 1) (GraphRep.coordinate 2) (GraphRep.constant 0)

def finalStack : GraphRep (fun v : Fin 3 → ℕ => betaValue (v 1) (v 2) (v 0)) :=
  betaGraph (GraphRep.coordinate 1) (GraphRep.coordinate 2) (GraphRep.coordinate 0)

def endpointInputs : Fin 2 → (Fin 3 → ℕ) → ℕ :=
  ![fun v => betaValue (v 1) (v 2) 0,
    fun v => betaValue (v 1) (v 2) (v 0)]

def endpointGraphs : ∀ j : Fin 2, GraphRep (endpointInputs j) :=
  Fin.cases initial (Fin.cases finalStack (fun j => Fin.elim0 j))

def endpointPolynomial : Expr (Fin 2) :=
  .var 0 * .var 0 + (.var 1 - 2) * (.var 1 - 2)

def endpointRep := Rep.compose (Rep.equality endpointPolynomial 0) endpointGraphs
def pathRep := endpointRep.conjunction everyStep

def closedRep :=
  (pathRep.reindex (fun j : Fin 3 => (Sum.inr j : Empty ⊕ Fin 3))).existsBlock

-- This is the direct quartic compiler, deliberately stopping BEFORE Jones.
noncomputable def result := QuarticCompiler.compile closedRep
noncomputable def equation := result.polynomial

end DiophantineConsistency.OneStackProposal
'''
(ROOT/'OneStackEquation.lean').write_text(s)
print('Wrote closed constructor proposal:',len(s),'bytes')
