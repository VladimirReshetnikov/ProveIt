import PA194PAeqLessCongrTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.LeTransport
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped
variable {Γ : List Fm}

def le (a b : Tm) : Fm := eq a b ⋎ less a b
noncomputable def transport (a s t : Tm) (d : ND.Proof Γ (le a s)) (e : ND.Proof Γ (eq s t))
    (hadd : addCongruence ∈ Γ) (hsym : symmetry ∈ Γ) (htrans : transitivity ∈ Γ) (hrefl : reflexivity ∈ Γ) :
    ND.Proof Γ (le a t) := by
  apply ND.orElim d
  · let Δ := eq a s :: Γ
    have ha : ND.Proof Δ (eq a s) := ND.assumption (by simp [Δ])
    have he : ND.Proof Δ (eq s t) := ND.weaken e (by intro p hp; simp [Δ,hp])
    exact ND.orLeft (transAt _ _ _ (by simp [Δ,htrans]) ha he)
  · let Δ := less a s :: Γ
    have ha : ND.Proof Δ (less a s) := ND.assumption (by simp [Δ])
    have he : ND.Proof Δ (eq s t) := ND.weaken e (by intro p hp; simp [Δ,hp])
    have hr : ND.Proof Δ (eq a a) := reflAt a (by simp [Δ,hrefl])
    exact ND.orRight (lessCongrAt a s a t hr he ha (by simp [Δ,hadd]) (by simp [Δ,hsym])
      (by simp [Δ,htrans]) (by simp [Δ,hrefl]))
#print axioms transport
end PA194PAeq.LeTransport
