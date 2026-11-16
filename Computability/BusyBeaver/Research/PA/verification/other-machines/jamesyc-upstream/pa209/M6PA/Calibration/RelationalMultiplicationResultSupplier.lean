module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationOutputTotal
@[expose] public section

/-! Ordinal-valued multiplication result existence for a fixed free base, with
all finite source premises paid. Neither uniqueness nor PA laws follow here. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def mulTotalStatement (base : Nat) : Form :=
  Ordinal.domain (.fvar base) 🡒 mulOutputConclusion base

def mulTotalDerivation (base : Nat) :
    ND.Proof (mulPrefixTotalAxioms base) (mulTotalStatement base) := by
  apply impIntro
  let d : Form := Ordinal.domain (.fvar base)
  have hd : ND.Proof (d :: mulPrefixTotalAxioms base) d := assumption (by simp)
  let E : FormulaEquality (d :: mulPrefixTotalAxioms base) :=
    ⟨⟨assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext]),
      assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext]),
      assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext])⟩,
      assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext])⟩
  exact mulOutputConclusionFromPrefix E base (mp hd (up (mulPrefixTotalDerivation base) d))

def mulTotalSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hmulSep : lo+3+depth (∼mulPrefixProperty base) ≤ z)
    (haddSep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (mulTotalDerivation base) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (mulTotalStatement base) f lo z) := by
  apply compileContext (mulPrefixTotalAxioms base) _ (mulTotalDerivation base) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases hm : p = separationFormula (∼mulPrefixProperty base)
  · subst p; exact separationSupplier _ f lo z hlo hf hmulSep
  by_cases ha : p = separationFormula (∼prefixProperty base)
  · subst p; exact separationSupplier _ f lo z hlo hf haddSep
  by_cases hi : p = Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have hh : p ∈ exactContext := by simpa [mulPrefixTotalAxioms,prefixTotalAxioms,hm,ha,hi] using hp
  exact graphContextSupplier f lo z hlo hz hadj p hh

#print axioms mulTotalDerivation
#print axioms mulTotalSupplier
end M6.PA.RelationalSource.PairGraph

