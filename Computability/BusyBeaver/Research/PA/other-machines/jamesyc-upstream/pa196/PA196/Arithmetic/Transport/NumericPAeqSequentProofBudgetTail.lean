module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentProofBudget
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormula
open M6.PA.NumericPAeqFormula.Sequent

namespace PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem SourceProofBudget.tail_child {d child f : V} (h : SourceProofBudget d f)
    (hc : child<d) : SourceProofBudget child (sndIdx f) := by
  rcases nil_or_adjoin f with rfl | ⟨x,f,rfl⟩
  · have hh : child<0 := lt_of_lt_of_le hc (by simpa using h.2)
    exact False.elim (by simpa using hh)
  · have hf : IsSemitermVec language (len f) 0 f := (by simpa using h.1 : IsSemiterm language 0 x ∧ IsSemitermVec language (len f) 0 f).2
    refine ⟨by simpa using hf,?_⟩
    have hn : child+1≤len f+1 := le_trans (succ_le_iff_lt.mpr hc) (by simpa using h.2)
    simpa using (add_le_add_iff_right 1).mp hn

#print axioms SourceProofBudget.tail_child
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent

