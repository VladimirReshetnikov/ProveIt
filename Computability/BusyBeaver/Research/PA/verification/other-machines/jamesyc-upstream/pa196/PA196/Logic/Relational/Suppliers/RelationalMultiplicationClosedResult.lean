module
public import M6PA.Calibration.RelationalMultiplicationClosedResult
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalMultiplicationResultSupplier
public import PA196.Logic.Relational.Suppliers.RelationalParameterClosure
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

def mulClosedResultSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hmulSep : lo+4+depth (∼mulPrefixProperty 0) ≤ z)
    (haddSep : lo+4+depth (∼prefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+1+lkBudget (mulTotalDerivation 0) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code mulClosedResult f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.PairGraph.mulTotalSupplier 0 (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
  · omega
  · omega
  · omega
  · omega
#print axioms mulClosedResultSupplier
end PA196.Logic.Relational.Source.PairGraph
end
