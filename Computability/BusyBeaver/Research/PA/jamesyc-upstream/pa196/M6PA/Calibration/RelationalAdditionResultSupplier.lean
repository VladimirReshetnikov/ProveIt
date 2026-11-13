module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionOutputTotal
@[expose] public section

/-! A finite actual-calculus proof of ordinal-valued addition totality.
All eight source premises, including the exact Separation instance, are paid. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def addTotalStatement (base : Nat) : Form :=
  Ordinal.domain (.fvar base) 🡒 addOutputConclusion base

def addTotalDerivation (base : Nat) : ND.Proof (prefixTotalAxioms base) (addTotalStatement base) := by
  apply impIntro
  let d : Form := Ordinal.domain (.fvar base)
  have hd : ND.Proof (d :: prefixTotalAxioms base) d := assumption (by simp)
  let E : FormulaEquality (d :: prefixTotalAxioms base) :=
    ⟨⟨assumption (by simp [prefixTotalAxioms,exactContext]),
      assumption (by simp [prefixTotalAxioms,exactContext]),
      assumption (by simp [prefixTotalAxioms,exactContext])⟩,
      assumption (by simp [prefixTotalAxioms,exactContext])⟩
  exact outputConclusionFromPrefix E base (mp hd (up (prefixTotalDerivation base) d))

def addTotalSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (addTotalDerivation base) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (addTotalStatement base) f lo z) := by
  apply compileContext (prefixTotalAxioms base) _ (addTotalDerivation base) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases hs : p = separationFormula (∼prefixProperty base)
  · subst p; exact separationSupplier _ f lo z hlo hf hsep
  by_cases hi : p = Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have hm : p ∈ exactContext := by simpa [prefixTotalAxioms,hs,hi] using hp
  exact graphContextSupplier f lo z hlo hz hadj p hm

#print axioms addTotalDerivation
#print axioms addTotalSupplier
end M6.PA.RelationalSource.PairGraph

