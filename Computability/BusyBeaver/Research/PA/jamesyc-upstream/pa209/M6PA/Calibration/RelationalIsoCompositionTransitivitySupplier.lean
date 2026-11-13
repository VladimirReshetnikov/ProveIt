module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionTransitivity
@[expose] public section

/-! Actual-basis existential transitivity. Both graph-parameter closures of
Separation are supplied by reusable generalization, with exact finite budgets. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionClosedSeparationSupplier (a : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hsep : lo+5+depth (∼compositionProperty 1 0 (a+1+1)) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (compositionClosedSeparation a) f lo z) := by
  apply closeParameterSupplier
  apply closedSeparationSupplier _ (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega

def compositionTransitivityStatement (a b c : Nat) : Form :=
  (Ordinal.domain (.fvar a) ⋏ (orderIso (.fvar a) (.fvar b) ⋏ orderIso (.fvar b) (.fvar c))) 🡒
    orderIso (.fvar a) (.fvar c)

def compositionTransitivityAxioms (a : Nat) : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,Ordinal.intersectionFormula,compositionClosedSeparation a]

def compositionTransitivityDerivation (a b c : Nat) :
    ND.Proof (compositionTransitivityAxioms a) (compositionTransitivityStatement a b c) := by
  apply impIntro
  let d : Form := Ordinal.domain (.fvar a) ⋏ (orderIso (.fvar a) (.fvar b) ⋏ orderIso (.fvar b) (.fvar c))
  let C := d :: compositionTransitivityAxioms a
  have hd : ND.Proof C d := assumption (by simp [C])
  have E : FormulaEquality C :=
    ⟨⟨assumption (by simp [C,compositionTransitivityAxioms]),assumption (by simp [C,compositionTransitivityAxioms]),
      assumption (by simp [C,compositionTransitivityAxioms])⟩,assumption (by simp [C,compositionTransitivityAxioms])⟩
  exact compositionIsoTransitivity E a b c (assumption (by simp [C,compositionTransitivityAxioms]))
    (assumption (by simp [C,compositionTransitivityAxioms])) (assumption (by simp [C,compositionTransitivityAxioms]))
    (assumption (by simp [C,compositionTransitivityAxioms])) (andLeft (andRight hd)) (andRight (andRight hd)) (andLeft hd)

def compositionTransitivityAxiomSupplier (a : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+5+depth (∼compositionProperty 1 0 (a+1+1)) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ compositionTransitivityAxioms a) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z hlo hz hadj
  by_cases h6 : p = Ordinal.intersectionFormula
  · subst p; exact Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have h7 : p = compositionClosedSeparation a := by
    simpa [compositionTransitivityAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p; exact compositionClosedSeparationSupplier a f lo z hlo hf hsep

def compositionTransitivitySupplier (a b c : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+5+depth (∼compositionProperty 1 0 (a+1+1)) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (compositionTransitivityDerivation a b c) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (compositionTransitivityStatement a b c) f lo z) :=
  compileContext (compositionTransitivityAxioms a) _ (compositionTransitivityDerivation a b c) f lo z hlo hf hbudget
    (compositionTransitivityAxiomSupplier a f lo z hlo hf hz hsep hadj)

#print axioms compositionClosedSeparationSupplier
#print axioms compositionTransitivityDerivation
#print axioms compositionTransitivityAxiomSupplier
#print axioms compositionTransitivitySupplier
end M6.PA.RelationalSource.PairGraph
