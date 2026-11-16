module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationInduction
public import M6PA.Calibration.RelationalAdditionResultSupplier
@[expose] public section

/-! Fixed-base finite multiplication-prefix totality. The additive and
multiplicative Separation formulas are different, explicit, and individually
paid by the actual-basis supplier. This is not universal parameter closure. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def mulPrefixTotalStatement (base : Nat) : Form :=
  Ordinal.domain (.fvar base) 🡒 Ordinal.inductionConclusion (mulPrefixProperty base)

def mulPrefixTotalAxioms (base : Nat) : List Form :=
  separationFormula (∼mulPrefixProperty base) :: prefixTotalAxioms base

def mulPrefixTotalDerivation (base : Nat) :
    ND.Proof (mulPrefixTotalAxioms base) (mulPrefixTotalStatement base) := by
  apply impIntro
  let q : Form := Ordinal.domain (.fvar base)
  have hq : ND.Proof (q :: mulPrefixTotalAxioms base) q := assumption (by simp)
  let S : SetProofs (q :: mulPrefixTotalAxioms base) := {
    equality := ⟨⟨assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext]),
      assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext]),
      assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext])⟩,
      assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext])⟩
    empty := assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext])
    adjunction := assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms,exactContext])
    intersection := assumption (by simp [mulPrefixTotalAxioms,prefixTotalAxioms]) }
  have ha : ND.Proof (q :: mulPrefixTotalAxioms base) (addTotalStatement base) := ND.weaken (addTotalDerivation base)
    (fun p hp => List.mem_cons_of_mem q (List.mem_cons_of_mem (separationFormula (∼mulPrefixProperty base)) hp))
  exact mulPrefixTotal S base (mp hq ha) (assumption (by simp [mulPrefixTotalAxioms]))

def mulPrefixTotalSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hmulSep : lo+3+depth (∼mulPrefixProperty base) ≤ z)
    (haddSep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (mulPrefixTotalDerivation base) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (mulPrefixTotalStatement base) f lo z) := by
  apply compileContext (mulPrefixTotalAxioms base) _ (mulPrefixTotalDerivation base) f lo z hlo hf hbudget
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

#print axioms mulPrefixTotalDerivation
#print axioms mulPrefixTotalSupplier
end M6.PA.RelationalSource.PairGraph

