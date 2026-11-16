import PA194FoundationGraphExtension
import PA194FoundationGraphContext
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def extensionFoundationDerivation (g a b : Nat) : LO.FirstOrder.Derivation
    (exactContext.map Semiformula.neg ++ [extensionExists (.fvar g) (.fvar a) (.fvar b)]) :=
  (extensionDerivation g a b).contra (by simp [ND.Proof, exactContext])

noncomputable def extensionSupplier (g a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (extensionFoundationDerivation g a b) ≤ z) :
    Proof (code (extensionExists (.fvar g) (.fvar a) (.fvar b)) f lo z) :=
  compileGraphContext _ (extensionFoundationDerivation g a b) f lo z hlo hf hz hadj hbudget
#print axioms extensionFoundationDerivation
#print axioms extensionSupplier
end PA194Logic.Relational.Source.PairGraph
