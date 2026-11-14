import PA194FoundationAdjunction
import PA194SourceEmpty
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
def exactContext : List Form :=
  [emptyFormula,adjunctionFormula,reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula]
end M6.PA.RelationalSource.PairGraph
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

noncomputable def graphContextSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hz : lo+6 < z) (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ exactContext) : Proof (code p f lo z) := by
  classical
  by_cases h0 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h1 : p = adjunctionFormula
  · subst p; exact foundationAdjunctionSupplier f lo z hlo hz hadj
  by_cases h2 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h3 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h4 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  have h5 : p = congruenceFormula := by simpa [exactContext,h0,h1,h2,h3,h4] using hp
  subst p; exact congruenceSupplier f lo z (by omega)

noncomputable def compileGraphContext (q : Form)
    (d : LO.FirstOrder.Derivation (exactContext.map Semiformula.neg ++ [q]))
    (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hz : lo+6 < z) (hadj : lo+2+foundationBudget foundationAdjunctionDerivation ≤ z)
    (hbudget : lo+foundationBudget d ≤ z) : Proof (code q f lo z) :=
  compileFoundationContext exactContext q d f lo z hlo hf hbudget (graphContextSupplier f lo z hlo hz hadj)
#print axioms graphContextSupplier
#print axioms compileGraphContext
end PA194Logic.Relational.Source.PairGraph
