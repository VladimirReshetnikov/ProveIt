import PA194FoundationAdditionZeroSupplier
import PA194FoundationGraphContext
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def zeroPrefixFoundationDerivation (a b : Nat) : LO.FirstOrder.Derivation
    (exactContext.map Semiformula.neg ++ [zeroPrefixStatement (.fvar a) (.fvar b)]) :=
  (zeroPrefixDerivation a b).contra (by simp [ND.Proof])

noncomputable def zeroPrefixSupplier (a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (zeroPrefixFoundationDerivation a b) ≤ z) :
    Proof (code (zeroPrefixStatement (.fvar a) (.fvar b)) f lo z) :=
  compileGraphContext _ (zeroPrefixFoundationDerivation a b) f lo z hlo hf hz hadj hbudget
#print axioms zeroPrefixFoundationDerivation
#print axioms zeroPrefixSupplier
end PA194Logic.Relational.Source.PairGraph
