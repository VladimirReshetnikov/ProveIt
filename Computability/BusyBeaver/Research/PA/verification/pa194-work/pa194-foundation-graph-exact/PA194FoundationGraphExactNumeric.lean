import PA194FoundationGraphExactExistence
import PA194FoundationGraphContext
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def exactFoundationDerivation (g a b : Nat) : LO.FirstOrder.Derivation
    (exactContext.map Semiformula.neg ++ [exactExtensionExists (.fvar g) (.fvar a) (.fvar b)]) :=
  (exactDerivation g a b).contra (by simp [ND.Proof])

noncomputable def exactExtensionSupplier (g a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (exactFoundationDerivation g a b) ≤ z) :
    Proof (code (exactExtensionExists (.fvar g) (.fvar a) (.fvar b)) f lo z) :=
  compileGraphContext _ (exactFoundationDerivation g a b) f lo z hlo hf hz hadj hbudget
#print axioms exactFoundationDerivation
#print axioms exactExtensionSupplier
end PA194Logic.Relational.Source.PairGraph
