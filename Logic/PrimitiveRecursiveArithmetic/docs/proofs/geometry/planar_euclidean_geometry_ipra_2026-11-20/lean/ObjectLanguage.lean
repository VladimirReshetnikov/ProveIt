import Translation
import ConciseIPRA.PR
import Mathlib.Data.Fin.VecNotation

/-! Compile scalar formulas into ProveIt's actual iPRA syntax.
The argument ScalarSymbols is data (PR syntax), not a field axiom.
Instantiating it with the scalar kernel and proving the operations' laws are
the remaining tasks described in the report. Boolean truth is the numeral 1. -/

namespace PlanarIPRA.ObjectLanguage

open PlaneTranslation LeanProofs.ConciseIPRA

structure ScalarSymbols where
  valid : PR 1
  zero : PR 0
  add : PR 2
  sub : PR 2
  mul : PR 2
  eqTest : PR 2
  leTest : PR 2

def scalarTerm {n : Nat} (S : ScalarSymbols) (ρ : Slot → PTm n) : Term → PTm n
  | .var i => ρ i
  | .zero => .app S.zero Fin.elim0
  | .add a b => .app S.add ![scalarTerm S ρ a, scalarTerm S ρ b]
  | .sub a b => .app S.sub ![scalarTerm S ρ a, scalarTerm S ρ b]
  | .mul a b => .app S.mul ![scalarTerm S ρ a, scalarTerm S ρ b]

def isTrue {n : Nat} (t : PTm n) : Fm PTm n :=
  .eq t (PTm.succ PTm.zero)

def newSlot {n : Nat} (ρ : Slot → PTm n) (i j : Slot) : PTm (n+1) :=
  if i = j then .var 0 else Syn.shift (ρ j)

def guard (S : ScalarSymbols) (n : Nat) : Fm PTm (n+1) :=
  isTrue (.app S.valid ![PTm.var 0])

def objectFormula (S : ScalarSymbols) : (φ : Scalar) → {n : Nat} →
    (Slot → PTm n) → Fm PTm n
  | .atom (.eq a b), _, ρ =>
    isTrue (.app S.eqTest ![scalarTerm S ρ a, scalarTerm S ρ b])
  | .atom (.le a b), _, ρ =>
    isTrue (.app S.leTest ![scalarTerm S ρ a, scalarTerm S ρ b])
  | .bot, _, _ => .bot
  | .conj p q, _, ρ => .and (objectFormula S p ρ) (objectFormula S q ρ)
  | .disj p q, _, ρ => .or (objectFormula S p ρ) (objectFormula S q ρ)
  | .impl p q, _, ρ => .imp (objectFormula S p ρ) (objectFormula S q ρ)
  | .ex i p, n, ρ => .ex (.and (guard S n) (objectFormula S p (newSlot ρ i)))
  | .all i p, n, ρ => .all (.imp (guard S n) (objectFormula S p (newSlot ρ i)))

/-- For a closed input no free slot is used. A numerically fixed environment
also permits testing open examples under a specified default valuation. -/
def closeTranslation (S : ScalarSymbols) (φ : Geom) : Fm PTm 0 :=
  objectFormula S (translate φ) (fun _ => PTm.zero)

end PlanarIPRA.ObjectLanguage
