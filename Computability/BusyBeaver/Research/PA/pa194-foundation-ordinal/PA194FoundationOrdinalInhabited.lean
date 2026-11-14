import PA194FoundationOrdinalEmpty
namespace PA194Logic.Relational.Source.Ordinal
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND
open PA194Logic PA194Logic.Relational

def emptyFoundationDerivation : LO.FirstOrder.Derivation
    ([emptyFormula].map Semiformula.neg ++ [inhabited]) :=
  emptyInhabitedDerivation.contra (by simp [ND.Proof])

noncomputable def inhabitedSupplier (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hf : ∀ i, f i < lo) (hz : lo+1 < z)
    (hbudget : lo + foundationBudget emptyFoundationDerivation ≤ z) :
    Proof (code inhabited f lo z) := by
  apply compileFoundationContext [emptyFormula] inhabited emptyFoundationDerivation f lo z hlo hf hbudget
  intro p hp
  have he : p = emptyFormula := by simpa using hp
  subst p
  exact emptySupplier f lo z hz
#print axioms emptyFoundationDerivation
#print axioms inhabitedSupplier
end PA194Logic.Relational.Source.Ordinal
