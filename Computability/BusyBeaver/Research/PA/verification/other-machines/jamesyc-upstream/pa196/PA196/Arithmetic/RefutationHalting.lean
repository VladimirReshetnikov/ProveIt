module
public import PA196.Arithmetic.RefutationMachine
public import PA196.Arithmetic.NoRefutation
@[expose] public section

namespace PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

attribute [local irreducible] Machine.Exact.PA.HaltingFormula.traceSentence

/-- This is a syntactic PA proof of a precise implication, established using
all-model correctness; it is not a standard-model-only simulation claim. -/
theorem pa_proves_nonhalting_no_refutation :
    M6.PA.theory ⊢ nonhaltingSentence 🡒 noRefutationSentence := by
  apply Arithmetic.complete.{0} M6.PA.theory _
  intro V _ _
  simp only [models_iff,LogicalConnective.HomClass.map_imply]
  intro hn
  apply (noRefutation_correct (V:=V)).mpr
  intro code hc
  have hn' : ¬ (V ⊧/![] haltingSentence) := by
    simpa [nonhaltingSentence,Machine.Exact.PA.HaltingFormula.nonhaltingSentence,
      haltingSentence,models_iff,Semiformula.Realize,Semiformula.Evalb] using hn
  exact hn' (refutation_implies_literal code hc)

#print axioms pa_proves_nonhalting_no_refutation
end PA196.Arithmetic
