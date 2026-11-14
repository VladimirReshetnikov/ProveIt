import PA194FoundationPairSupplier
import PA194FoundationGraphContext
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def kuratowskiFoundationDerivation (a b : Nat) : LO.FirstOrder.Derivation
    (exactContext.map Semiformula.neg ++ [kuratowskiExists (.fvar a) (.fvar b)]) :=
  (kuratowskiDerivation a b).contra (by simp [ND.Proof, exactContext])

noncomputable def kuratowskiSupplier (a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (kuratowskiFoundationDerivation a b) ≤ z) :
    Proof (code (kuratowskiExists (.fvar a) (.fvar b)) f lo z) :=
  compileGraphContext _ (kuratowskiFoundationDerivation a b) f lo z hlo hf hz hadj hbudget
#print axioms kuratowskiFoundationDerivation
#print axioms kuratowskiSupplier
end PA194Logic.Relational.Source.PairGraph
