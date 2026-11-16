module
public import M6PA.Calibration.RelationalMultiplicationResultSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.SourceSeparation
public import PA196.Logic.Relational.Suppliers.RelationalAdditionZeroSupplier
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

def mulTotalSupplier (base : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hmulSep : lo+3+depth (∼mulPrefixProperty base) ≤ z)
    (haddSep : lo+3+depth (∼prefixProperty base) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (mulTotalDerivation base) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (mulTotalStatement base) f lo z) := by
  apply PA196.Logic.Relational.Source.compileContext (mulPrefixTotalAxioms base) _ (mulTotalDerivation base) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases hm : p = separationFormula (∼mulPrefixProperty base)
  · subst p; exact PA196.Logic.Relational.Source.separationSupplier _ f lo z hlo hf hmulSep
  by_cases ha : p = separationFormula (∼prefixProperty base)
  · subst p; exact PA196.Logic.Relational.Source.separationSupplier _ f lo z hlo hf haddSep
  by_cases hi : p = Ordinal.intersectionFormula
  · subst p; exact PA196.Logic.Relational.Source.Ordinal.intersectionAxiomSupplier f lo z hlo (by omega)
  have hh : p ∈ exactContext := by simpa [mulPrefixTotalAxioms,prefixTotalAxioms,hm,ha,hi] using hp
  exact PA196.Logic.Relational.Source.PairGraph.graphContextSupplier f lo z hlo hz hadj p hh
#print axioms mulTotalSupplier
end PA196.Logic.Relational.Source.PairGraph
end
