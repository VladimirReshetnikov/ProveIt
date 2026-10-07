/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.NativeProductCoefficient

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realification_range {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (f : V →ₗ[ℚ] W) :
    (LinearMap.range f).baseChange ℝ = LinearMap.range (f.baseChange ℝ) := by
  rw [← Submodule.map_top, realification_map, Submodule.baseChange_top, Submodule.map_top]

theorem real_lieTreeEval_hom {I L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] (φ : L →ₗ⁅ℚ⁆ M)
    (v : I → ℝ ⊗[ℚ] L) (a : FreeMagma I) :
    lieTreeEval (fun i => realificationLieHom φ (v i)) a =
      realificationLieHom φ (lieTreeEval v a) := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => simp only [lieTreeEval, ha, hb, LieHom.map_lie]

namespace DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

include hφ

theorem real_layerProjection_mem (d : ℕ) (k : Fin 4) (x : ℝ ⊗[ℚ] M)
    (hx : x ∈ (A d).baseChange ℝ) :
    realificationLieHom ((liePiEval k).comp φ) x ∈ (F.layer d 1).baseChange ℝ :=
  baseChange_mem_of_mapsTo (A d) (F.layer d 1) ((liePiEval k).comp φ).toLinearMap
    (fun x hx => hφ d x hx k) hx

noncomputable def realLayerProjection (d : ℕ) (k : Fin 4) :
    (A d).baseChange ℝ →ₗ[ℝ] (F.layer d 1).baseChange ℝ :=
  (((realificationLieHom ((liePiEval k).comp φ)).toLinearMap).comp
    ((A d).baseChange ℝ).subtype).codRestrict ((F.layer d 1).baseChange ℝ)
    (fun x => F.real_layerProjection_mem A φ hφ d k x.val x.property)

theorem real_layerHorizontalMap_component (d : ℕ) (k : Fin 4) (x : ℝ ⊗[ℚ] A d) :
    (LinearMap.proj k).baseChange ℝ ((F.layerHorizontalMap A φ hφ d).baseChange ℝ x) =
      F.realHorizontalMap d
        (F.realLayerProjection A φ hφ d k (realificationSubmoduleEquiv (A d) x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    let y : F.layer d 1 := ⟨φ x.val k, hφ d x.val x.property k⟩
    have heq : F.realLayerProjection A φ hφ d k
        (realificationSubmoduleEquiv (A d) (a ⊗ₜ[ℚ] x)) =
        realificationSubmoduleEquiv (F.layer d 1) (a ⊗ₜ[ℚ] y) := by
      apply Subtype.ext
      rfl
    rw [heq, F.realHorizontalMap_baseChange]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem real_layerHorizontalImage_frequency
    (η : L →ₗ[ℚ] ℚ) (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ u : I → ℝ ⊗[ℚ] M, (∀ i, u i ∈ (A (d i)).baseChange ℝ) →
      realifyFunctional η (realificationLieHom ((liePiEval 0).comp φ) (lieTreeEval u a)) +
      realifyFunctional η (realificationLieHom ((liePiEval 1).comp φ) (lieTreeEval u a)) -
      realifyFunctional η (realificationLieHom ((liePiEval 2).comp φ) (lieTreeEval u a)) -
      realifyFunctional η (realificationLieHom ((liePiEval 3).comp φ) (lieTreeEval u a)) = 0)
    (v : ∀ i, ℝ ⊗[ℚ] (Fin 4 → F.HigherHorizontal (d i)))
    (hv : ∀ i, v i ∈ (F.layerHorizontalImage A φ hφ (d i)).baseChange ℝ) :
    realifyFunctional η (F.realHorizontalTreeValue d a (fun i => (LinearMap.proj (0 : Fin 4)).baseChange ℝ (v i))) +
    realifyFunctional η (F.realHorizontalTreeValue d a (fun i => (LinearMap.proj (1 : Fin 4)).baseChange ℝ (v i))) -
    realifyFunctional η (F.realHorizontalTreeValue d a (fun i => (LinearMap.proj (2 : Fin 4)).baseChange ℝ (v i))) -
    realifyFunctional η (F.realHorizontalTreeValue d a (fun i => (LinearMap.proj (3 : Fin 4)).baseChange ℝ (v i))) = 0 := by
  classical
  have hlift (i : I) : ∃ w : ℝ ⊗[ℚ] A (d i),
      (F.layerHorizontalMap A φ hφ (d i)).baseChange ℝ w = v i := by
    have h := hv i
    rw [layerHorizontalImage, realification_range] at h
    exact h
  choose w hw using hlift
  let u (i : I) := realificationSubmoduleEquiv (A (d i)) (w i)
  have hmap (k : Fin 4) :
      (fun i => F.realHorizontalMap (d i) (F.realLayerProjection A φ hφ (d i) k (u i))) =
        (fun i => (LinearMap.proj k).baseChange ℝ (v i)) := by
    funext i
    exact (F.real_layerHorizontalMap_component A φ hφ (d i) k (w i)).symm.trans
      (congrArg ((LinearMap.proj k).baseChange ℝ) (hw i))
  have hvalue (k : Fin 4) :
      F.realHorizontalTreeValue d a (fun i => (LinearMap.proj k).baseChange ℝ (v i)) =
        realificationLieHom ((liePiEval k).comp φ) (lieTreeEval (fun i => (u i).val) a) := by
    rw [← hmap k, F.realHorizontalTreeValue_map d a hd hr]
    exact real_lieTreeEval_hom ((liePiEval k).comp φ) (fun i => (u i).val) a
  rw [hvalue 0, hvalue 1, hvalue 2, hvalue 3]
  exact hker (fun i => (u i).val) (fun i => (u i).property)

end DegreeRankLieFiltration
end Erdos3

end

end OAI
