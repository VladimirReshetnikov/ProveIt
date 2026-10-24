#!/usr/bin/env python3
"""Emit a closed, explicitly UNCOMPILED one-block constructor proposal."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
obj=json.loads((R/'height_shared_step.json').read_text());w=obj['witnesses'];ex=obj['exposed_coordinates']
def atom(s):
 return f'(.var (.inl {ex.index(s)}))' if s in ex else f'(.var (.inr {w.index(s)}))'
def expr(rows):
 return ' + '.join('('+' * '.join([f'(.constant ({r["coefficient"]} : ℤ))']+[atom(s) for s in r['monomial']])+')' for r in rows) or '0'
s='''import DiophantineConsistency.RemainderRepresentation
import DiophantineConsistency.BoundedForallRepresentation
import DiophantineConsistency.QuarticCompiler
import Mathlib.Data.Fin.VecNotation

/-!
Closed one-bounded-block PROPOSAL; UNCOMPILED and UNMATERIALIZED.
Current API pin2605669a532342f153b13eb6b4a0af4b54f5fa37.
Its source equivalence is proved in HEIGHT_CERTIFICATE.md, not in this file.
No K215 simulation, Jones finalizer, primality, or common-multiple block.
-/
namespace DiophantineConsistency.HeightCommutativeProposal

def stepPolynomial : Expr (Fin 5 ⊕ Fin 20) :=
'''
for i,b in enumerate(obj['horn_source']['branches']): s+=f'  let h{i} : Expr (Fin 5 ⊕ Fin 20) := {expr(b["sum_of_squares"])}\n'
for i,r in enumerate(obj['extra_residuals']): s+=f'  let e{i} : Expr (Fin 5 ⊕ Fin 20) := {expr(r)}\n'
s+='  '+' * '.join(f'h{i}' for i in range(len(obj['horn_source']['branches'])))+' + e0 * e0 + e1 * e1\n\n'
s+='''def stepRep := (Rep.equality stepPolynomial 0).existsBlock

-- Outer natural coordinates N,x,z,y,M0; M=M0+1.
def betaValue (x y i : ℕ) : ℕ := x % ((i + 1) * y + 1)
def betaGraph {σ : Type} {x y i : (σ → ℕ) → ℕ}
    (rx : GraphRep x) (ry : GraphRep y) (ri : GraphRep i) :
    GraphRep (fun v => betaValue (x v) (y v) (i v)) :=
  rx.mod (((ri.add (GraphRep.constant 1)).mul ry).add (GraphRep.constant 1))

def currentS : GraphRep (fun v : Option (Fin 5) → ℕ =>
    betaValue (v (some 1)) (v (some 3)) (v none)) :=
  betaGraph (GraphRep.coordinate (some 1)) (GraphRep.coordinate (some 3))
    (GraphRep.coordinate none)
def nextS : GraphRep (fun v : Option (Fin 5) → ℕ =>
    betaValue (v (some 1)) (v (some 3)) (v none + 1)) :=
  betaGraph (GraphRep.coordinate (some 1)) (GraphRep.coordinate (some 3))
    ((GraphRep.coordinate none).add (GraphRep.constant 1))
def currentR : GraphRep (fun v : Option (Fin 5) → ℕ =>
    betaValue (v (some 2)) (v (some 3)) (v none)) :=
  betaGraph (GraphRep.coordinate (some 2)) (GraphRep.coordinate (some 3))
    (GraphRep.coordinate none)
def nextR : GraphRep (fun v : Option (Fin 5) → ℕ =>
    betaValue (v (some 2)) (v (some 3)) (v none + 1)) :=
  betaGraph (GraphRep.coordinate (some 2)) (GraphRep.coordinate (some 3))
    ((GraphRep.coordinate none).add (GraphRep.constant 1))
def stepInputs : Fin 5 → (Option (Fin 5) → ℕ) → ℕ :=
  ![fun v => betaValue (v (some 1)) (v (some 3)) (v none),
    fun v => betaValue (v (some 1)) (v (some 3)) (v none + 1),
    fun v => betaValue (v (some 2)) (v (some 3)) (v none),
    fun v => betaValue (v (some 2)) (v (some 3)) (v none + 1),
    fun v => v (some 4)]
def stepGraphs : ∀ j : Fin 5, GraphRep (stepInputs j) :=
  Fin.cases currentS (Fin.cases nextS (Fin.cases currentR
    (Fin.cases nextR (Fin.cases (GraphRep.coordinate (some 4))
      (fun j => Fin.elim0 j)))))
def everyStep := (Rep.compose stepRep stepGraphs).boundedForall (0 : Fin 5)

def initialS : GraphRep (fun v : Fin 5 → ℕ => betaValue (v 1) (v 3) 0) :=
  betaGraph (GraphRep.coordinate 1) (GraphRep.coordinate 3) (GraphRep.constant 0)
def finalS : GraphRep (fun v : Fin 5 → ℕ => betaValue (v 1) (v 3) (v 0)) :=
  betaGraph (GraphRep.coordinate 1) (GraphRep.coordinate 3) (GraphRep.coordinate 0)
def initialR : GraphRep (fun v : Fin 5 → ℕ => betaValue (v 2) (v 3) 0) :=
  betaGraph (GraphRep.coordinate 2) (GraphRep.coordinate 3) (GraphRep.constant 0)
def finalR : GraphRep (fun v : Fin 5 → ℕ => betaValue (v 2) (v 3) (v 0)) :=
  betaGraph (GraphRep.coordinate 2) (GraphRep.coordinate 3) (GraphRep.coordinate 0)
def endpointInputs : Fin 5 → (Fin 5 → ℕ) → ℕ :=
  ![fun v => betaValue (v 1) (v 3) 0,
    fun v => betaValue (v 1) (v 3) (v 0),
    fun v => betaValue (v 2) (v 3) 0,
    fun v => betaValue (v 2) (v 3) (v 0), fun v => v 4]
def endpointGraphs : ∀ j : Fin 5, GraphRep (endpointInputs j) :=
  Fin.cases initialS (Fin.cases finalS (Fin.cases initialR
    (Fin.cases finalR (Fin.cases (GraphRep.coordinate 4) (fun j => Fin.elim0 j)))))
def endpointPolynomial : Expr (Fin 5) :=
  (.var 0 - .var 4 - 2) * (.var 0 - .var 4 - 2) +
  (.var 1 - 1) * (.var 1 - 1) +
  (.var 2 - 2) * (.var 2 - 2) +
  (.var 3 - .var 4) * (.var 3 - .var 4)
def endpoints := Rep.compose (Rep.equality endpointPolynomial 0) endpointGraphs
def pathRep := endpoints.conjunction everyStep

def closedRep :=
  (pathRep.reindex (fun j : Fin 5 => (Sum.inr j : Empty ⊕ Fin 5))).existsBlock
noncomputable def result := QuarticCompiler.compile closedRep
noncomputable def equation := result.polynomial
end DiophantineConsistency.HeightCommutativeProposal
'''
(R/'HeightCommutativeEquation.lean').write_text(s)
print('Emitted uncompiled20-local-witness, one-bounded-block constructor')
