module
public import PA196.Arithmetic.RefutationHalting
public import PA196.Arithmetic.Transport.InternalConsistency
@[expose] public section

namespace PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- PA itself proves that literal PA196 nonhalting implies its standard
syntactic consistency sentence. -/
theorem pa_proves_nonhalting_consistency :
    M6.PA.theory ⊢ nonhaltingSentence 🡒 M6.PA.consistencySentence :=
  C_trans pa_proves_nonhalting_no_refutation pa_proves_no_refutation_consistency

/-- Gödel's second incompleteness theorem discharges the remaining direction.
The consistency instance comes from the standard natural-number PA model. -/
theorem nonhalting_unprovable : M6.PA.theory ⊬ nonhaltingSentence :=
  M6.PA.unprovable_of_internal_consistency_implication _ inferInstance
    pa_proves_nonhalting_consistency

theorem two_sided_independence :
    (M6.PA.theory ⊬ nonhaltingSentence) ∧ (M6.PA.theory ⊬ haltingSentence) :=
  ⟨nonhalting_unprovable,halting_unprovable⟩

#print axioms pa_proves_nonhalting_consistency
#print axioms nonhalting_unprovable
#print axioms two_sided_independence
end PA196.Arithmetic
