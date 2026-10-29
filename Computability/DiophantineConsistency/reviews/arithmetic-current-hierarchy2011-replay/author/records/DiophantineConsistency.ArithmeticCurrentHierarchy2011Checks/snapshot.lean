import DiophantineConsistency.ArithmeticCurrentHierarchy2011

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCurrentHierarchy2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticCurrentHierarchy2011

example : Hierarchy 𝚷 1 FoundationHACurrentNoZero2011.classicalSentence :=
  current_pi_one

example : Hierarchy 𝚷 1 FoundationZFCConsistencyNat.sourceSentence :=
  consistency_pi_one

example : Hierarchy 𝚷 2
    (FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence) := current_iff_consistency_pi_two

example : endpoint.val =
    (FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence) := endpoint_val

#print axioms current_pi_one
#print axioms consistency_pi_one
#print axioms current_iff_consistency_pi_two
#print axioms endpoint_val

end DiophantineConsistency.ArithmeticCurrentHierarchy2011Checks
