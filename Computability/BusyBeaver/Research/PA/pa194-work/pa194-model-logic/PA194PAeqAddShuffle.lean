import PA194PAeqAddLawsAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddLawsAt
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped
variable {Γ : List Fm}
noncomputable def shuffle (a b c d : Tm) (ha : ∀ p ∈ AddAssoc.axioms, p ∈ Γ)
    (hc : ∀ p ∈ AddComm.axioms, p ∈ Γ)
    (hadd : addCongruence ∈ Γ) (hrefl : reflexivity ∈ Γ)
    (hsym : symmetry ∈ Γ) (htrans : transitivity ∈ Γ) :
    ND.Proof Γ (eq (add (add a b) (add c d)) (add (add a c) (add b d))) := by
  have h1 := symmAt _ _ hsym (assocAt (add a b) c d ha)
  have h2 := addCongrAt (add (add a b) c) (add (add a c) b) d d hadd
    (swapMiddle a b c ha hc hadd hrefl hsym htrans) (reflAt d hrefl)
  have h3 := assocAt (add a c) b d ha
  exact transAt _ _ _ htrans h1 (transAt _ _ _ htrans h2 h3)
#print axioms shuffle
end PA194PAeq.AddLawsAt
