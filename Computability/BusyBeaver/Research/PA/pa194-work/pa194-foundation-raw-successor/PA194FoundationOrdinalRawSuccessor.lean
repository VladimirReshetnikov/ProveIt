import PA194FoundationOrdinalSuccessorBase
namespace PA194Logic.Relational.Source.Ordinal
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND
open PA194Logic PA194Logic.Relational

def rawSuccessorFoundationDerivation (a : Term 0) : LO.FirstOrder.Derivation
    ([adjunctionFormula].map Semiformula.neg ++ [successorExists a]) :=
  (rawSuccessorDerivation a).contra (by simp [ND.Proof])

noncomputable def rawSuccessorSupplier (a : Term 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget (rawSuccessorFoundationDerivation a) ≤ z) :
    Proof (code (successorExists a) f lo z) := by
  apply compileFoundationContext [adjunctionFormula] (successorExists a)
    (rawSuccessorFoundationDerivation a) f lo z hlo hf hbudget
  intro p hp
  have he : p = adjunctionFormula := by simpa using hp
  subst p
  exact foundationAdjunctionSupplier f lo z hlo hz hadj
#print axioms rawSuccessorFoundationDerivation
#print axioms rawSuccessorSupplier
end PA194Logic.Relational.Source.Ordinal
