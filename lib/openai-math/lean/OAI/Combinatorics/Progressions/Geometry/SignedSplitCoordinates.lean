import OAI.Combinatorics.Progressions.Linear.SplitSurjectionBasis

namespace OAI

section

namespace Erdos3

open Module

variable {R E F I J : Type*} [Ring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] [Fintype I] [Fintype J]

noncomputable def signedSplitCoordinates (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F) :
    E ≃ₗ[R] (J → R) × (I → R) :=
  (splitSurjectionEquiv q s hs).symm.trans
    ((bK.equivFun.prodCongr bI.equivFun).trans
      ((LinearEquiv.prodComm R (I → R) (J → R)).trans
        ((LinearEquiv.neg R : (J → R) ≃ₗ[R] (J → R)).prodCongr
          (LinearEquiv.refl R (I → R)))))

theorem signedSplitCoordinates_fst (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F) (x : E) :
    (signedSplitCoordinates q s hs bK bI x).1 = -(bI.equivFun (q x)) := rfl

theorem signedSplitCoordinates_symm_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F)
    (z : J → R) (w : I → R) :
    (signedSplitCoordinates q s hs bK bI).symm (z, w) =
      (bK.equivFun.symm w).val - s (bI.equivFun.symm z) := by
  change (bK.equivFun.symm w).val + s (bI.equivFun.symm (-z)) = _
  rw [map_neg, map_neg, sub_eq_add_neg]

theorem signedSplitCoordinates_reconstruction (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (bK : Basis I R (LinearMap.ker q)) (bI : Basis J R F) (x : E) :
    x + s (bI.equivFun.symm (signedSplitCoordinates q s hs bK bI x).1) =
      (bK.equivFun.symm (signedSplitCoordinates q s hs bK bI x).2).val := by
  have h := signedSplitCoordinates_symm_apply q s hs bK bI
    (signedSplitCoordinates q s hs bK bI x).1 (signedSplitCoordinates q s hs bK bI x).2
  change (signedSplitCoordinates q s hs bK bI).symm
    (signedSplitCoordinates q s hs bK bI x) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact eq_sub_iff_add_eq.mp h

end Erdos3

end

end OAI
