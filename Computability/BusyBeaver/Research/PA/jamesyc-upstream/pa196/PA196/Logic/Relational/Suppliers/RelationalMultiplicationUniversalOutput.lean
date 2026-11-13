module
public import M6PA.Calibration.RelationalMultiplicationUniversalOutput
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalMultiplicationClosedResult
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
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulUniversalOutputSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hmulSep : lo+4+depth (∼mulPrefixProperty 0) ≤ z)
    (haddSep : lo+4+depth (∼prefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hresultBudget : lo+1+lkBudget (mulTotalDerivation 0) ≤ z)
    (hbudget : lo+lkBudget mulUniversalOutputDerivation ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code mulUniversalOutput f lo z) := by
  apply PA196.Logic.Relational.Source.compileContext [mulClosedResult] _ mulUniversalOutputDerivation f lo z hlo hf hbudget
  intro p hp
  have he : p = mulClosedResult := by simpa using hp
  subst p
  exact PA196.Logic.Relational.Source.PairGraph.mulClosedResultSupplier f lo z hlo hf hz hmulSep haddSep hadj hresultBudget
#print axioms mulUniversalOutputSupplier
end PA196.Logic.Relational.Source.PairGraph
end
