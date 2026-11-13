module
public import M6PA.Theory
public import M6PA.Calibration.RelationalKuratowskiExistence
@[expose] public section

/-! Finite actual-basis Kuratowski existence; its only nonlogical inputs are the
already constructed empty and adjunction proofs, at the same allocator. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def kuratowskiDerivation (a b : Nat) :
    ND.Proof [emptyFormula, adjunctionFormula]
      (kuratowskiExists (.fvar a) (.fvar b)) :=
  kuratowskiWitness a b (assumption (by simp)) (assumption (by simp))

def kuratowskiSupplier (a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (kuratowskiDerivation a b) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (kuratowskiExists (.fvar a) (.fvar b)) f lo z) := by
  apply compileContext [emptyFormula, adjunctionFormula]
    (kuratowskiExists (.fvar a) (.fvar b)) (kuratowskiDerivation a b)
    f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h : p = emptyFormula
  · subst p
    exact emptySupplier f lo z (by omega)
  · have he : p = adjunctionFormula := by simpa [h] using hp
    subst p
    exact adjunctionSupplier f lo z hlo hz hadj

#print axioms kuratowskiDerivation
#print axioms kuratowskiSupplier
end M6.PA.RelationalSource.PairGraph
