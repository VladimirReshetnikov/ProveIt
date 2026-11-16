module
public import M6PA.Calibration.RelationalOrderIsoClosedSymmetry
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalIsoInverseSymmetrySupplier
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

def isoSymmetryClosedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0<lo) (hf : ∀i,f i<lo) (hz : lo+8<z)
    (hsep : lo+6+depth (∼inverseProperty 0 (1+1))≤z)
    (hadj : lo+4+lkBudget adjunctionDerivation≤z)
    (hbudget : lo+2+lkBudget (inverseSymmetryDerivation 1 0)≤z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code isoSymmetryClosed f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.PairGraph.inverseSymmetrySupplier 1 0 _ (lo+1+1) z (by omega)
    (shiftedLabelsBound _ _ (shiftedLabelsBound f lo hf))
    (by omega) (by omega) (by omega) (by omega)
#print axioms isoSymmetryClosedSupplier
end PA196.Logic.Relational.Source.PairGraph
end
