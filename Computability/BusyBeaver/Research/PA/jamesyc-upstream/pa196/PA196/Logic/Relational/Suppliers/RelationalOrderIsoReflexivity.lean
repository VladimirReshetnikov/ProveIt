module
public import M6PA.Calibration.RelationalOrderIsoReflexivity
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalIdentitySupplier
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
open M6.PA.RelationalSource.Ordinal (Term Formula)

def orderIsoReflexivitySupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hsep : lo+3+depth (∼identityProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget orderIsoReflexivityDerivation ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code orderIsoReflexivityStatement f lo z) :=
  PA196.Logic.Relational.Source.compileContext identityAxioms _ orderIsoReflexivityDerivation f lo z hlo hf hbudget
    (PA196.Logic.Relational.Source.PairGraph.identityAxiomSupplier f lo z hlo hf hz hsep hadj)
#print axioms orderIsoReflexivitySupplier
end PA196.Logic.Relational.Source.PairGraph
end
