module
public import M6PA.Calibration.RelationalOrderIsoClosedTransitivity
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalIsoCompositionTransitivitySupplier
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
attribute [local irreducible] orderIso Ordinal.domain
set_option maxHeartbeats 600000

def isoTransitivityClosedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0<lo) (hf : ∀i,f i<lo) (hz : lo+9<z)
    (hsep : lo+8+depth (∼compositionProperty 1 0 (2+1+1))≤z)
    (hadj : lo+5+lkBudget adjunctionDerivation≤z)
    (hbudget : lo+3+lkBudget (compositionTransitivityDerivation 2 1 0)≤z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code isoTransitivityClosed f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.PairGraph.compositionTransitivitySupplier 2 1 0 _ (lo+1+1+1) z (by omega)
    (shiftedLabelsBound _ _ (shiftedLabelsBound _ _ (shiftedLabelsBound f lo hf)))
    (by omega) (by omega) (by omega) (by omega)
#print axioms isoTransitivityClosedSupplier
end PA196.Logic.Relational.Source.PairGraph
end
