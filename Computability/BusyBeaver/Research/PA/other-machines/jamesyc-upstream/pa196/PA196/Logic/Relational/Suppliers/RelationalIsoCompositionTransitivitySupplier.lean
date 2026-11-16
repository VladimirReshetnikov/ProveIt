module
public import M6PA.Calibration.RelationalIsoCompositionTransitivitySupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalParameterClosure
public import PA196.Logic.Relational.Suppliers.RelationalSourceEmpty
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def compositionClosedSeparationSupplier (a : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hsep : lo+5+depth (∼compositionProperty 1 0 (a+1+1)) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (compositionClosedSeparation a) f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.closedSeparationSupplier _ (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
#print axioms compositionClosedSeparationSupplier
end PA196.Logic.Relational.Source.PairGraph

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def compositionTransitivityAxiomSupplier (a : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+5+depth (∼compositionProperty 1 0 (a+1+1)) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ compositionTransitivityAxioms a) : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p f lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier f lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact PA196.Logic.Relational.Source.symmetrySupplier f lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact PA196.Logic.Relational.Source.transitivitySupplier f lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact PA196.Logic.Relational.Source.congruenceSupplier f lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact PA196.Logic.Relational.Source.emptySupplier f lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact PA196.Logic.Relational.Source.adjunctionSupplier f lo z hlo hz hadj
  by_cases h6 : p = Ordinal.intersectionFormula
  · subst p; exact PA196.Logic.Relational.Source.Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have h7 : p = compositionClosedSeparation a := by
    simpa [compositionTransitivityAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p; exact PA196.Logic.Relational.Source.PairGraph.compositionClosedSeparationSupplier a f lo z hlo hf hsep
#print axioms compositionTransitivityAxiomSupplier
end PA196.Logic.Relational.Source.PairGraph

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def compositionTransitivitySupplier (a b c : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+5+depth (∼compositionProperty 1 0 (a+1+1)) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (compositionTransitivityDerivation a b c) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (compositionTransitivityStatement a b c) f lo z) :=
  PA196.Logic.Relational.Source.compileContext (compositionTransitivityAxioms a) _ (compositionTransitivityDerivation a b c) f lo z hlo hf hbudget
    (PA196.Logic.Relational.Source.PairGraph.compositionTransitivityAxiomSupplier a f lo z hlo hf hz hsep hadj)
#print axioms compositionTransitivitySupplier
end PA196.Logic.Relational.Source.PairGraph
end
