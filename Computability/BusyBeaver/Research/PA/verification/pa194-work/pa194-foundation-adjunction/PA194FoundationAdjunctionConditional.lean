import PA194FoundationLK
import PA194SourceAdjunctionConditional
namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open PA194Logic PA194Logic.Relational

noncomputable def foundationAdjunctionSupplierConditional (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hz : lo+6 < z)
    (d : LO.FirstOrder.Derivation
      ((ND.adjunctionAxioms (.fvar 0) (.fvar 1)).map Semiformula.neg ++
        [ND.adjunctionExists (.fvar 0) (.fvar 1)]))
    (hbudget : lo+2+foundationBudget d ≤ z) : Proof (code adjunctionFormula f lo z) := by
  let p := compileFoundationContext (ND.adjunctionAxioms (.fvar 0) (.fvar 1))
    (ND.adjunctionExists (.fvar 0) (.fvar 1)) d (adjunctionEnvironment lo) (lo+2) z
    (by omega) (by intro i; simp [adjunctionEnvironment]; split <;> (try split) <;> omega)
    hbudget (adjunctionPremises lo z hlo hz)
  exact .all lo (.all (lo+1) p)
#print axioms foundationAdjunctionSupplierConditional
end PA194Logic.Relational.Source
