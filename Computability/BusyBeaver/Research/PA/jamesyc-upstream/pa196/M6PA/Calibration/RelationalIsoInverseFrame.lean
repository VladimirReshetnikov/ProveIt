module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseCoverageExtension
@[expose] public section

/-! Actual finite premises for one inverse-prefix successor witness. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inversePrefixShift {Γ : List Form} (g n h : Nat)
    (hc : ND.Proof Γ (inversePrefix (.fvar g) (.fvar n) (.fvar h))) :
    ND.Proof (shifted Γ) (inversePrefix (.fvar (g+1)) (.fvar (n+1)) (.fvar (h+1))) := by
  convert shiftProof hc using 1 <;> inverseSyntax

structure InverseFrame (Γ : List Form) (g n s h v : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  graph : ND.Proof Γ (inversePrefix (.fvar g) (.fvar n) (.fvar h))
  successor : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s))
  forward : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v))

def InverseFrame.weaken {Γ Δ : List Form} {g n s h v : Nat} (I : InverseFrame Γ g n s h v)
    (inc : ∀ p, p ∈ Γ → p ∈ Δ) : InverseFrame Δ g n s h v where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  graph := ND.weaken I.graph inc
  successor := ND.weaken I.successor inc
  forward := ND.weaken I.forward inc

def InverseFrame.shift {Γ : List Form} {g n s h v : Nat} (I : InverseFrame Γ g n s h v) :
    InverseFrame (shifted Γ) (g+1) (n+1) (s+1) (h+1) (v+1) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  graph := inversePrefixShift g n h I.graph
  successor := Ordinal.successorShift n s I.successor
  forward := by convert shiftProof I.forward using 1 <;> inverseSyntax

#print axioms inversePrefixShift
#print axioms InverseFrame.weaken
#print axioms InverseFrame.shift
end M6.PA.RelationalSource.PairGraph
