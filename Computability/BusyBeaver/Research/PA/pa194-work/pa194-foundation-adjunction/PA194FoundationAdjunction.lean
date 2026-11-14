import PA194FoundationAdjunctionAxioms
import PA194FoundationAdjunctionConditional
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder M6.PA.RelationalSource
open PA194Logic PA194Logic.Relational

def foundationAdjunctionDerivation : LO.FirstOrder.Derivation
    ((ND.adjunctionAxioms (.fvar 0) (.fvar 1)).map Semiformula.neg ++
      [ND.adjunctionExists (.fvar 0) (.fvar 1)]) := by
  apply LO.FirstOrder.Derivation.contraction (ND.exactAdjunctionFromAxioms (.fvar 0) (.fvar 1))
  intro p hp
  simp only [ND.Proof, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hp ⊢
  tauto

noncomputable def foundationAdjunctionSupplier (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hz : lo+6 < z) (hbudget : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z) :
    Proof (code adjunctionFormula f lo z) :=
  foundationAdjunctionSupplierConditional f lo z hlo hz foundationAdjunctionDerivation hbudget

#print axioms foundationAdjunctionDerivation
#print axioms foundationAdjunctionSupplier
end PA194Logic.Relational.Source
