import PA194PAeqTriSucc
import PA194PAeqLeTransport
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.TriTransport
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped PA194PAeq.TriSucc
variable {Γ : List Fm}
noncomputable def transport (a s t : Tm) (d : ND.Proof Γ (tri a s)) (e : ND.Proof Γ (eq s t))
    (hadd : addCongruence ∈ Γ) (hsym : symmetry ∈ Γ) (htrans : transitivity ∈ Γ) (hrefl : reflexivity ∈ Γ) :
    ND.Proof Γ (tri a t) := by
  apply ND.orElim d
  · let Δ := less a s :: Γ
    have ha : ND.Proof Δ (less a s) := ND.assumption (by simp [Δ])
    have he : ND.Proof Δ (eq s t) := ND.weaken e (by intro p hp; simp [Δ,hp])
    have hr : ND.Proof Δ (eq a a) := reflAt a (by simp [Δ,hrefl])
    exact ND.orLeft (lessCongrAt a s a t hr he ha (by simp [Δ,hadd]) (by simp [Δ,hsym]) (by simp [Δ,htrans]) (by simp [Δ,hrefl]))
  · let Δ := (eq a s ⋎ less s a) :: Γ
    have hh : ND.Proof Δ (eq a s ⋎ less s a) := ND.assumption (by simp [Δ])
    apply ND.orElim hh
    · let Ψ := eq a s :: Δ
      have ha : ND.Proof Ψ (eq a s) := ND.assumption (by simp [Ψ])
      have he : ND.Proof Ψ (eq s t) := ND.weaken e (by intro p hp; simp [Ψ,Δ,hp])
      exact ND.orRight (ND.orLeft (transAt _ _ _ (by simp [Ψ,Δ,htrans]) ha he))
    · let Ψ := less s a :: Δ
      have ha : ND.Proof Ψ (less s a) := ND.assumption (by simp [Ψ])
      have he : ND.Proof Ψ (eq s t) := ND.weaken e (by intro p hp; simp [Ψ,Δ,hp])
      have hr : ND.Proof Ψ (eq a a) := reflAt a (by simp [Ψ,Δ,hrefl])
      exact ND.orRight (ND.orRight (lessCongrAt s a t a he hr ha (by simp [Ψ,Δ,hadd]) (by simp [Ψ,Δ,hsym]) (by simp [Ψ,Δ,htrans]) (by simp [Ψ,Δ,hrefl])))
#print axioms transport
end PA194PAeq.TriTransport
