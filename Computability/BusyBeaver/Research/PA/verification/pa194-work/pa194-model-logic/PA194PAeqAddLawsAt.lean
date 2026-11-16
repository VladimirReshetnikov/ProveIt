import PA194PAeqAddAssocProof
import PA194PAeqAddCommProof
import PA194PAeqLessCongrTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddLawsAt
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped
variable {Γ : List Fm}
noncomputable def assocAt (x y z : Tm) (hΓ : ∀ p ∈ AddAssoc.axioms, p ∈ Γ) :
    ND.Proof Γ (eq (add (add x y) z) (add x (add y z))) := by
  have h : ND.Proof Γ (.all AddAssoc.prop) := ND.weaken AddAssoc.proof hΓ
  have h1 := ND.allElim _ x h
  have h2 := ND.allElim _ y h1
  have h3 := ND.allElim _ z h2
  simpa [AddAssoc.prop,eq,add,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice] using h3
noncomputable def commAt (x y : Tm) (hΓ : ∀ p ∈ AddComm.axioms, p ∈ Γ) :
    ND.Proof Γ (eq (add x y) (add y x)) := by
  have h : ND.Proof Γ (.all AddComm.prop) := ND.weaken AddComm.proof hΓ
  have h1 := ND.allElim _ x h
  have h2 := ND.allElim _ y h1
  simpa [AddComm.prop,eq,add,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using h2
noncomputable def swapMiddle (a c t : Tm) (ha : ∀ p ∈ AddAssoc.axioms, p ∈ Γ)
    (hc : ∀ p ∈ AddComm.axioms, p ∈ Γ)
    (hadd : addCongruence ∈ Γ) (hrefl : reflexivity ∈ Γ)
    (hsym : symmetry ∈ Γ) (htrans : transitivity ∈ Γ) :
    ND.Proof Γ (eq (add (add a c) t) (add (add a t) c)) := by
  have h1 := assocAt a c t ha
  have h2 := addCongrAt a a (add c t) (add t c) hadd (reflAt a hrefl) (commAt c t hc)
  have h3 := symmAt _ _ hsym (assocAt a t c ha)
  exact transAt _ _ _ htrans h1 (transAt _ _ _ htrans h2 h3)
#print axioms swapMiddle
#print axioms assocAt
#print axioms commAt
end PA194PAeq.AddLawsAt
