import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

noncomputable def operatorPrecompose (J : E →L[ℝ] X) :
    (X →L[ℝ] Y) →L[ℝ] (E →L[ℝ] Y) :=
  (ContinuousLinearMap.compL ℝ E X Y).flip J

theorem operatorPrecompose_apply (J : E →L[ℝ] X) (A : X →L[ℝ] Y) :
    operatorPrecompose J A = A.comp J := rfl

theorem operatorPrecompose_norm_le (J : E →L[ℝ] X) :
    ‖operatorPrecompose (Y := Y) J‖ ≤ ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg J)
  intro A
  exact (A.opNorm_comp_le J).trans_eq (mul_comm _ _)

theorem affineSlice_fderiv (F : X → Y) (c : X) (J : E →L[ℝ] X) (x : E)
    (hF : DifferentiableAt ℝ F (c + J x)) :
    fderiv ℝ (fun y => F (c + J y)) x = (fderiv ℝ F (c + J x)).comp J := by
  exact (hF.hasFDerivAt.comp x (J.hasFDerivAt.const_add c)).fderiv

theorem affineSlice_fderiv_norm_le (F : X → Y) (c : X) (J : E →L[ℝ] X) (x : E)
    (hF : DifferentiableAt ℝ F (c + J x)) (hJ : ‖J‖ ≤ 1) {H : ℝ}
    (hH : ‖fderiv ℝ F (c + J x)‖ ≤ H) :
    ‖fderiv ℝ (fun y => F (c + J y)) x‖ ≤ H := by
  rw [affineSlice_fderiv F c J x hF]
  calc
    _ ≤ ‖fderiv ℝ F (c + J x)‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ H * 1 := mul_le_mul hH hJ (norm_nonneg J) ((norm_nonneg _).trans hH)
    _ = H := mul_one H

theorem affineSlice_second_fderiv_norm_le (F : X → Y) (hF : ContDiff ℝ 2 F)
    (c : X) (J : E →L[ℝ] X) (x : E) (hJ : ‖J‖ ≤ 1) {H : ℝ}
    (hH : ‖fderiv ℝ (fderiv ℝ F) (c + J x)‖ ≤ H) :
    ‖fderiv ℝ (fderiv ℝ (fun y => F (c + J y))) x‖ ≤ H := by
  let L : (X →L[ℝ] Y) →L[ℝ] (E →L[ℝ] Y) := operatorPrecompose J
  let g : E → (X →L[ℝ] Y) := fun y => fderiv ℝ F (c + J y)
  have hD : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hg := ((hD.differentiable one_ne_zero (c + J x)).hasFDerivAt.comp x
    (J.hasFDerivAt.const_add c))
  have hg' : HasFDerivAt g ((fderiv ℝ (fderiv ℝ F) (c + J x)).comp J) x := hg
  have he : fderiv ℝ (fun y => F (c + J y)) = L ∘ g := by
    funext y
    exact affineSlice_fderiv F c J y (hF.differentiable (by norm_num) _)
  rw [he, fderiv_comp x L.differentiableAt hg'.differentiableAt, L.fderiv, hg'.fderiv]
  have hL : ‖L‖ ≤ 1 := (operatorPrecompose_norm_le J).trans hJ
  have hinner : ‖(fderiv ℝ (fderiv ℝ F) (c + J x)).comp J‖ ≤ H := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ F) (c + J x)‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ H * 1 := mul_le_mul hH hJ (norm_nonneg J)
        ((norm_nonneg (fderiv ℝ (fderiv ℝ F) (c + J x))).trans hH)
      _ = H := mul_one H
  calc
    _ ≤ ‖L‖ * ‖(fderiv ℝ (fderiv ℝ F) (c + J x)).comp J‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * H := mul_le_mul hL hinner
      (norm_nonneg ((fderiv ℝ (fderiv ℝ F) (c + J x)).comp J)) zero_le_one
    _ = H := one_mul H

end Erdos3

end

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem second_fderiv_sub (F G : X → Y) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (x : X) :
    fderiv ℝ (fderiv ℝ (fun y => F y - G y)) x =
      fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ G) x := by
  have he : fderiv ℝ (fun y => F y - G y) = fun y => fderiv ℝ F y - fderiv ℝ G y := by
    funext y
    exact fderiv_sub (hF.differentiable (by norm_num) y) (hG.differentiable (by norm_num) y)
  rw [he]
  exact fderiv_sub ((hF.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x)
    ((hG.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x)

theorem affineSlice_first_difference_bound (F G : X → Y)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (b : X)
    (J : E →L[ℝ] X) (hJ : ‖J‖ ≤ 1) (x : E) {ε : ℝ}
    (herr : ‖fderiv ℝ F (b + J x) - fderiv ℝ G (b + J x)‖ ≤ ε) :
    ‖fderiv ℝ (fun y => F (b + J y)) x - fderiv ℝ (fun y => G (b + J y)) x‖ ≤ ε := by
  rw [affineSlice_fderiv F b J x (hF.differentiable (by norm_num) _),
    affineSlice_fderiv G b J x (hG.differentiable (by norm_num) _), ← ContinuousLinearMap.sub_comp]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hJ)).trans herr

theorem affineSlice_second_difference_bound (F G : X → Y)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (b : X)
    (J : E →L[ℝ] X) (hJ : ‖J‖ ≤ 1) (x : E) {ε : ℝ}
    (herr : ‖fderiv ℝ (fderiv ℝ F) (b + J x) - fderiv ℝ (fderiv ℝ G) (b + J x)‖ ≤ ε) :
    ‖fderiv ℝ (fderiv ℝ (fun y => F (b + J y))) x -
      fderiv ℝ (fderiv ℝ (fun y => G (b + J y))) x‖ ≤ ε := by
  have hs : ‖fderiv ℝ (fderiv ℝ (fun y => F y - G y)) (b + J x)‖ ≤ ε := by
    rw [second_fderiv_sub F G hF hG]
    exact herr
  have ht := affineSlice_second_fderiv_norm_le (fun y => F y - G y) (hF.sub hG) b J x hJ hs
  have hFs : ContDiff ℝ 2 (fun y => F (b + J y)) := hF.comp (contDiff_const.add J.contDiff)
  have hGs : ContDiff ℝ 2 (fun y => G (b + J y)) := hG.comp (contDiff_const.add J.contDiff)
  rw [second_fderiv_sub (fun y => F (b + J y)) (fun y => G (b + J y)) hFs hGs] at ht
  exact ht

theorem affineSlice_c2_difference_bound (F G : X → Y)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (b : X)
    (J : E →L[ℝ] X) (hJ : ‖J‖ ≤ 1) (x : E) {ε : ℝ}
    (herr : ‖F (b + J x) - G (b + J x)‖ ≤ ε ∧
      ‖fderiv ℝ F (b + J x) - fderiv ℝ G (b + J x)‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ F) (b + J x) - fderiv ℝ (fderiv ℝ G) (b + J x)‖ ≤ ε) :
    ‖F (b + J x) - G (b + J x)‖ ≤ ε ∧
      ‖fderiv ℝ (fun y => F (b + J y)) x - fderiv ℝ (fun y => G (b + J y)) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => F (b + J y))) x -
        fderiv ℝ (fderiv ℝ (fun y => G (b + J y))) x‖ ≤ ε :=
  ⟨herr.1, affineSlice_first_difference_bound F G hF hG b J hJ x herr.2.1,
    affineSlice_second_difference_bound F G hF hG b J hJ x herr.2.2⟩

end Erdos3

end

end OAI
