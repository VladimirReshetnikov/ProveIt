module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionInduction
public import M6PA.Calibration.RelationalAdditionZeroSupplier
@[expose] public section

/-! Finite actual-basis addition-prefix totality for an arbitrary free base
parameter. The exact negated-prefix Separation instance is discharged. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def prefixTotalStatement (base : Nat) : Form :=
  Ordinal.domain (.fvar base) 🡒 Ordinal.inductionConclusion (prefixProperty base)

def prefixTotalAxioms (base : Nat) : List Form :=
  separationFormula (∼prefixProperty base) :: Ordinal.intersectionFormula :: exactContext

def prefixTotalDerivation (base : Nat) : ND.Proof (prefixTotalAxioms base) (prefixTotalStatement base) := by
  apply impIntro
  let q : Form := Ordinal.domain (.fvar base)
  have hq : ND.Proof (q :: prefixTotalAxioms base) q := assumption (by simp)
  let S : SetProofs (q :: prefixTotalAxioms base) := {
    equality := ⟨⟨assumption (by simp [prefixTotalAxioms,exactContext]),
      assumption (by simp [prefixTotalAxioms,exactContext]),
      assumption (by simp [prefixTotalAxioms,exactContext])⟩,
      assumption (by simp [prefixTotalAxioms,exactContext])⟩
    empty := assumption (by simp [prefixTotalAxioms,exactContext])
    adjunction := assumption (by simp [prefixTotalAxioms,exactContext])
    intersection := assumption (by simp [prefixTotalAxioms]) }
  exact prefixTotal S base hq (assumption (by simp [prefixTotalAxioms]))

def prefixTotalSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (prefixTotalDerivation base) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (prefixTotalStatement base) f lo z) := by
  apply compileContext (prefixTotalAxioms base) _ (prefixTotalDerivation base) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases hs : p = separationFormula (∼prefixProperty base)
  · subst p; exact separationSupplier _ f lo z hlo hf hsep
  by_cases hi : p = Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have hm : p ∈ exactContext := by simpa [prefixTotalAxioms,hs,hi] using hp
  exact graphContextSupplier f lo z hlo hz hadj p hm

#print axioms prefixTotalDerivation
#print axioms prefixTotalSupplier
end M6.PA.RelationalSource.PairGraph

