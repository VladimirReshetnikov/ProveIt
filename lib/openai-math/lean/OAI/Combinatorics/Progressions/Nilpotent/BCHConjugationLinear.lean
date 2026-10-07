import Mathlib.Algebra.Group.End
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.IsometricSMul
import OAI.Combinatorics.Progressions.Estimates.RiemannianLipschitz
import OAI.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth

namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ}

attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_of_step_le (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hst : s ≤ t) (a b : L) : lieBCH t a b = lieBCH s a b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) s
  have hx (i : Fin 2) : scaledFreeGenerator s i ∈ F.layer 1 := scaledFreeGenerator_mem_layer s i
  have h : scaledFreeLieEval s (lieBCH t (x 0) (x 1)) =
      scaledFreeLieEval s (lieBCH s (x 0) (x 1)) := by
    simp only [map_lieBCH, x, scaledFreeLieEval_of]
    rw [(F.extend hst).lieBCH_eq (hx 0) (hx 1), F.lieBCH_eq (hx 0) (hx 1)]
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, x, FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem lieBCH_eq_of_nilpotent_steps (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) (a b : L) : lieBCH s a b = lieBCH t a b := by
  rcases le_total s t with hst | hts
  · exact (lieBCH_eq_of_step_le hs hst a b).symm
  · exact lieBCH_eq_of_step_le ht hts a b

theorem map_lieBCH_of_nilpotent_steps (φ : L →ₗ⁅ℚ⁆ M)
    (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ M M t = ⊥) (a b : L) :
    φ (lieBCH s a b) = lieBCH t (φ a) (φ b) := by
  rcases le_total s t with hst | hts
  · rw [← lieBCH_eq_of_step_le hs hst, map_lieBCH]
  · rw [map_lieBCH, lieBCH_eq_of_step_le ht hts]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L M N : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [LieRing N] [LieAlgebra ℚ N] {s t u : ℕ}
  {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
  {hN : LieModule.lowerCentralSeries ℚ N N u = ⊥}

noncomputable def mapOfSteps (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup L s hL →* NilpotentLieBCHGroup M t hM where
  toFun g := ⟨φ g.coord⟩
  map_one' := ext (map_zero φ)
  map_mul' g h := ext (map_lieBCH_of_nilpotent_steps φ hL hM g.coord h.coord)

@[simp] theorem mapOfSteps_coord (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) :
    (mapOfSteps (hM := hM) φ g).coord = φ g.coord := rfl

theorem mapOfSteps_injective (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Injective φ) :
    Function.Injective (mapOfSteps (hL := hL) (hM := hM) φ) := by
  intro g h heq
  exact ext (hφ (congrArg coord heq))

theorem mapOfSteps_surjective (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Surjective φ) :
    Function.Surjective (mapOfSteps (hL := hL) (hM := hM) φ) := by
  intro g
  obtain ⟨x, hx⟩ := hφ g.coord
  exact ⟨⟨x⟩, ext hx⟩

theorem mapOfSteps_comp (φ : L →ₗ⁅ℚ⁆ M) (ψ : M →ₗ⁅ℚ⁆ N) :
    (mapOfSteps (hL := hM) (hM := hN) ψ).comp (mapOfSteps (hL := hL) (hM := hM) φ) =
      mapOfSteps (hL := hL) (hM := hN) (ψ.comp φ) := by
  ext g
  rfl

noncomputable def changeStep (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) :
    NilpotentLieBCHGroup L s hs ≃* NilpotentLieBCHGroup L t ht where
  toFun g := ⟨g.coord⟩
  invFun g := ⟨g.coord⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := ext (lieBCH_eq_of_nilpotent_steps hs ht g.coord h.coord)

@[simp] theorem changeStep_coord (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) (g : NilpotentLieBCHGroup L s hs) :
    (changeStep hs ht g).coord = g.coord := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem bchSubgroupCoordinates_comap_of_steps [DecidableEq κ]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_bchSubgroup_comap_grid_of_steps [DecidableEq ι] [DecidableEq κ]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) ∧
      bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap_of_steps b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightTranslate (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) : ι → ℝ :=
  basisHomeomorph e ((basisHomeomorph e).symm x * g)

@[simp] theorem rightTranslate_coordinates (g h : NilpotentLieBCHGroup L s hnil) :
    rightTranslate e h (basisHomeomorph e g) = basisHomeomorph e (g * h) := by
  simp only [rightTranslate, Homeomorph.symm_apply_apply]

@[simp] theorem rightTranslate_one : rightTranslate (hnil := hnil) e 1 = id := by
  funext x
  simp only [rightTranslate, mul_one, Homeomorph.apply_symm_apply, id_eq]

theorem rightTranslate_comp (g h : NilpotentLieBCHGroup L s hnil) :
    rightTranslate e h ∘ rightTranslate e g = rightTranslate e (g * h) := by
  funext x
  simp only [Function.comp_apply, rightTranslate, Homeomorph.symm_apply_apply, mul_assoc]

variable [IsScalarTower ℚ ℝ L]

theorem contDiff_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (n : ℕ∞ω) :
    ContDiff ℝ n (rightTranslate e g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  exact ((contMDiff_basisHomeomorph e n).comp
    ((contMDiff_basisHomeomorph_symm e n).mul contMDiff_const)).contDiff

theorem rightTranslate_fderiv_leftInverse (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    (fderiv ℝ (rightTranslate e g⁻¹) (rightTranslate e g x)).comp
      (fderiv ℝ (rightTranslate e g) x) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have hg := (contDiff_rightTranslate e g 1).differentiable (by decide)
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  rw [← fderiv_comp x hi.differentiableAt hg.differentiableAt,
    rightTranslate_comp, mul_inv_cancel, rightTranslate_one, fderiv_id]

theorem rightTranslate_fderiv_injective (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    Function.Injective (fderiv ℝ (rightTranslate e g) x) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ (rightTranslate e g⁻¹) (rightTranslate e g x)) hvw
  simpa only [← ContinuousLinearMap.comp_apply, rightTranslate_fderiv_leftInverse,
    ContinuousLinearMap.id_apply] using h

noncomputable def rightVelocity (g : NilpotentLieBCHGroup L s hnil) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  fderiv ℝ (rightTranslate e g⁻¹) (basisHomeomorph e g)

theorem rightVelocity_injective (g : NilpotentLieBCHGroup L s hnil) :
    Function.Injective (rightVelocity e g) :=
  rightTranslate_fderiv_injective e g⁻¹ (basisHomeomorph e g)

omit [IsScalarTower ℚ ℝ L] in
@[simp] theorem rightVelocity_one :
    rightVelocity (hnil := hnil) e 1 = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  simp only [rightVelocity, inv_one, rightTranslate_one, fderiv_id]

theorem rightVelocity_mul (g h : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity e (g * h)).comp (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g)) =
      rightVelocity e g := by
  have hh := (contDiff_rightTranslate e h 1).differentiable (by decide)
  have hi := (contDiff_rightTranslate e (g * h)⁻¹ 1).differentiable (by decide)
  unfold rightVelocity
  rw [← rightTranslate_coordinates e g h, ← fderiv_comp _ hi.differentiableAt hh.differentiableAt,
    rightTranslate_comp]
  simp only [mul_inv_rev, mul_inv_cancel_left]

theorem contDiff_rightVelocity :
    ContDiff ℝ ∞ (fun x : ι → ℝ => rightVelocity (hnil := hnil) e ((basisHomeomorph e).symm x)) := by
  have h : ContDiff ℝ ∞ (fun p : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (lieBCH s (e.equivFun.symm p.2) (e.equivFun.symm (-p.1)))) :=
    ContDiff.comp
      (g := fun z : (ι → ℝ) × (ι → ℝ) =>
        e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2)))
      (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.2, -p.1))
      (contDiff_coordinateBCH (n := ∞) e s) (contDiff_snd.prodMk contDiff_fst.neg)
  have hd : ContDiff ℝ ∞ (fun x : ι → ℝ =>
      fderiv ℝ (fun y => e.equivFun (lieBCH s (e.equivFun.symm y) (e.equivFun.symm (-x)))) x) :=
    h.fderiv contDiff_id (by simp)
  convert hd using 1
  funext x
  unfold rightVelocity
  rw [Homeomorph.apply_symm_apply]
  apply congrArg (fun f : (ι → ℝ) → (ι → ℝ) => fderiv ℝ f x)
  funext y
  change e.equivFun (lieBCH s (e.equivFun.symm y) (-e.equivFun.symm x)) = _
  rw [map_neg]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def coordinateDotForm {ι : Type*} [Fintype ι] :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i)

@[simp] theorem coordinateDotForm_apply {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    coordinateDotForm v w = ∑ i, v i * w i := by
  simp [coordinateDotForm]

theorem contDiff_bilinearComp_self {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    (B : F →L[ℝ] F →L[ℝ] ℝ) (T : E → F →L[ℝ] F) (hT : ContDiff ℝ n T) :
    ContDiff ℝ n (fun x => B.bilinearComp (T x) (T x)) := by
  have hflip : ContDiff ℝ n (fun A : F →L[ℝ] F →L[ℝ] ℝ => A.flip) :=
    (show IsBoundedLinearMap ℝ (fun A : F →L[ℝ] F →L[ℝ] ℝ => A.flip) from
      { map_add := ContinuousLinearMap.flip_add
        map_smul := ContinuousLinearMap.flip_smul
        bound := ⟨1, zero_lt_one, fun A => by simp only [one_mul, ContinuousLinearMap.opNorm_flip, le_refl]⟩ }).contDiff
  exact hflip.comp ((hflip.comp (contDiff_const.clm_comp hT)).clm_comp hT)

end Erdos3

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightInnerForm (g : NilpotentLieBCHGroup L s hnil) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  coordinateDotForm.bilinearComp (rightVelocity e g) (rightVelocity e g)

theorem rightInnerForm_apply (g : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e g v w = ∑ i, rightVelocity e g v i * rightVelocity e g w i := by
  simp only [rightInnerForm, ContinuousLinearMap.bilinearComp_apply, coordinateDotForm_apply]

theorem rightInnerForm_symm (g : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e g v w = rightInnerForm e g w v := by
  simp only [rightInnerForm_apply, mul_comm]

@[simp] theorem rightInnerForm_one : rightInnerForm (hnil := hnil) e 1 = coordinateDotForm := by
  ext v w
  simp only [rightInnerForm, rightVelocity_one, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply]

variable [IsScalarTower ℚ ℝ L]

theorem rightInnerForm_pos (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) (hv : v ≠ 0) :
    0 < rightInnerForm e g v v := by
  have hne : rightVelocity e g v ≠ 0 := by
    intro h
    apply hv
    exact (rightVelocity_injective e g) (h.trans (map_zero _).symm)
  obtain ⟨i, hi⟩ : ∃ i, rightVelocity e g v i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  rw [rightInnerForm_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun j _ => mul_self_nonneg _)).mpr
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem rightInnerForm_right_invariant (g h : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e (g * h)
      (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) v)
      (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) w) = rightInnerForm e g v w := by
  have hv := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) (rightVelocity_mul e g h)
  have hw := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T w) (rightVelocity_mul e g h)
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  simp only [rightInnerForm_apply, hv, hw]

theorem contDiff_rightInnerForm :
    ContDiff ℝ ∞ (fun x : ι → ℝ => rightInnerForm (hnil := hnil) e ((basisHomeomorph e).symm x)) :=
  contDiff_bilinearComp_self (E := ι → ℝ) (F := ι → ℝ) (n := ∞) coordinateDotForm
    (fun x => rightVelocity (hnil := hnil) e ((basisHomeomorph e).symm x))
    (contDiff_rightVelocity (hnil := hnil) e)

theorem rightInnerForm_isVonNBounded (g : NilpotentLieBCHGroup L s hnil) :
    Bornology.IsVonNBounded ℝ {v : ι → ℝ | rightInnerForm e g v v < 1} := by
  let A := fderiv ℝ (rightTranslate e g)
    (rightTranslate e g⁻¹ (basisHomeomorph e g))
  have hleft : A.comp (rightVelocity e g) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    simpa only [inv_inv, A, rightVelocity] using
      rightTranslate_fderiv_leftInverse e g⁻¹ (basisHomeomorph e g)
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨‖A‖, ?_⟩
  intro v hv
  change rightInnerForm e g v v < 1 at hv
  have hTv : ‖rightVelocity e g v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    have hi : rightVelocity e g v i * rightVelocity e g v i ≤ rightInnerForm e g v v := by
      rw [rightInnerForm_apply]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith
  have heq : A (rightVelocity e g v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) hleft
  calc
    ‖v‖ = ‖A (rightVelocity e g v)‖ := congrArg norm heq.symm
    _ ≤ ‖A‖ * ‖rightVelocity e g v‖ := A.le_opNorm _
    _ ≤ ‖A‖ := mul_le_of_le_one_right (norm_nonneg _) hTv

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module MvPolynomial
open scoped NNReal Topology

theorem lieBCH_right_coordinates_sub_bound {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (x y z : L) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |e.repr x i| ≤ B) (hy : ∀ i, |e.repr y i| ≤ B)
    (hz : ∀ i, |e.repr z i| ≤ B) (hxy : ∀ i, |e.repr x i - e.repr y i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x z) k - e.repr (lieBCH s y z) k| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun i => e.repr (![x, z] i.1) i.2
  let w : Fin 2 × ι → ℝ := fun i => e.repr (![y, z] i.1) i.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (i : Fin 2 × ι) : |v i| ≤ B := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hx i
    · exact hz i
  have hw (i : Fin 2 × ι) : |w i| ≤ B := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hy i
    · exact hz i
  have hvw (i : Fin 2 × ι) : |v i - w i| ≤ δ := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hxy i
    · simpa [v, w] using hδ
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hevalv : aeval v P = e.repr (lieBCH s x z) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x z k
  have hevalw : aeval w P = e.repr (lieBCH s y z) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s y z k
  rw [hevalv, hevalw] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

namespace NilpotentLieBCHGroup

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lipschitzOn_rightTranslate_box (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    LipschitzOnWith ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
      (rightTranslate e g) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  change ∀ i, |v i| ≤ B at hv
  change ∀ i, |w i| ≤ B at hw
  apply (dist_pi_le_iff (mul_nonneg
    (bchBoxCoordinateBound_nonneg _ _ _ (by linarith : 0 ≤ B)) dist_nonneg)).mpr
  intro k
  rw [Real.dist_eq]
  change |e.equivFun (lieBCH s (e.equivFun.symm v) g.coord) k -
    e.equivFun (lieBCH s (e.equivFun.symm w) g.coord) k| ≤ _
  simp only [Basis.equivFun_apply]
  apply lieBCH_right_coordinates_sub_bound e c hstructure hc _ _ _ hB dist_nonneg
  · simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hv
  · simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hw
  · exact hg
  · intro i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Real.dist_eq] using
      dist_le_pi_dist v w i

theorem norm_fderiv_rightTranslate_zero_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    ‖fderiv ℝ (rightTranslate e g) 0‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B := by
  apply norm_fderiv_le_of_lipschitzOn ℝ ?_ (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ι → ℝ) (by linarith : 0 < B))
  intro v hv i
  have hi := norm_le_pi_norm v i
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (show |v i| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using hi).trans hv.le

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightRiemannianMetric :
    letI := basisChartedSpace (hnil := hnil) e
    RiemannianMetric (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  refine
    { inner := fun g => ?_
      symm := ?_
      pos := ?_
      continuousAt := ?_
      isVonNBounded := ?_ }
  · exact rightInnerForm e g
  · intro g v w
    exact rightInnerForm_symm e g v w
  · intro g v hv
    exact rightInnerForm_pos e g v hv
  · intro g
    exact ((rightInnerForm e g).continuous.clm_apply continuous_id).continuousAt
  · intro g
    exact rightInnerForm_isVonNBounded e g

omit [IsScalarTower ℚ ℝ L] in
theorem basisChart_mem_source (x y : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    y ∈ (chartAt (ι → ℝ) x).source := by
  let := basisChartedSpace (hnil := hnil) e
  change y ∈ ((basisHomeomorph e).isOpenEmbedding.toOpenPartialHomeomorph (basisHomeomorph e)).source
  simp

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangentCoordChange (x y z : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    tangentCoordChange 𝓘(ℝ, ι → ℝ) x y z = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  apply ContinuousLinearMap.ext
  intro v
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) x x z v = v
  apply tangentCoordChange_self
  rw [extChartAt_source]
  exact basisChart_mem_source e x z

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangent_trivialization (x y : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x ⟨y, v⟩).2 = v := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) y x y v = v
  rw [basis_tangentCoordChange]
  rfl

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangent_symmL (x y : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symmL ℝ y v = v := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  rw [TangentBundle.symmL_trivializationAt_eq_core (basisChart_mem_source e x y)]
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) x y y v = v
  rw [basis_tangentCoordChange]
  rfl

theorem contMDiff_rightInnerForm :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) ∞
      (rightInnerForm (hnil := hnil) e) := by
  let := basisChartedSpace (hnil := hnil) e
  have h := (contDiff_rightInnerForm (hnil := hnil) e).contMDiff.comp
    (contMDiff_basisHomeomorph (hnil := hnil) e ∞)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h

noncomputable def rightSmoothRiemannianMetric :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    ContMDiffRiemannianMetric 𝓘(ℝ, ι → ℝ) ∞ (ι → ℝ)
      (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  refine
    { __ := rightRiemannianMetric (hnil := hnil) e
      contMDiff := ?_ }
  intro x
  rw [contMDiffAt_section]
  convert (contMDiff_rightInnerForm (hnil := hnil) e).contMDiffAt (x := x) using 1; try rfl
  funext y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    rightRiemannianMetric, Trivialization.continuousLinearMapAt_apply]
  have hy : y ∈ (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).baseSet :=
    basisChart_mem_source e x y
  have hw : (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symm y w = w :=
    (Trivialization.symmL_apply (R := ℝ) _ hy w).symm.trans (basis_tangent_symmL e x y w)
  change rightInnerForm e y
    ((trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symmL ℝ y v)
    ((trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symm y w) = rightInnerForm e y v w
  exact congrArg₂ (fun a b : ι → ℝ => rightInnerForm e y a b)
    (basis_tangent_symmL e x y v) hw

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Set
open scoped ENNReal Topology

theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have ho : IsOpen (Metric.eball x ⊤)ᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (Metric.eball_mem_nhds z zero_lt_one)
    intro w hw hfin
    apply hz
    change edist z x < ⊤
    have hzw : edist z w < ⊤ := by
      have hw' : edist w z < 1 := hw
      rw [edist_comm]
      exact hw'.trans (by simp)
    exact (edist_triangle z w x).trans_lt (ENNReal.add_lt_top.mpr ⟨hzw, hfin⟩)
  have hall : Metric.eball x ⊤ = univ :=
    (show IsClopen (Metric.eball x ⊤) from ⟨isOpen_compl_iff.mp ho, Metric.isOpen_eball⟩).eq_univ
      ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hall]; trivial
  have hxy : edist y x < ⊤ := hy
  exact (by simpa only [edist_comm] using hxy.ne)

end Erdos3

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

@[instance_reducible]
noncomputable def rightRiemannianBundle :
    letI := basisChartedSpace (hnil := hnil) e
    RiemannianBundle (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  exact ⟨(rightSmoothRiemannianMetric (hnil := hnil) e).toRiemannianMetric⟩

theorem rightRiemannianBundle_continuous :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    letI := rightRiemannianBundle (hnil := hnil) e
    IsContinuousRiemannianBundle (ι → ℝ)
      (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e ∞
  let := rightRiemannianBundle (hnil := hnil) e
  exact ⟨(rightSmoothRiemannianMetric e).inner,
    (rightSmoothRiemannianMetric e).contMDiff.continuous, fun _ _ _ => rfl⟩

@[instance_reducible]
noncomputable def rightEMetricSpace : EMetricSpace (NilpotentLieBCHGroup L s hnil) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  letI := rightRiemannianBundle (hnil := hnil) e
  letI := rightRiemannianBundle_continuous (hnil := hnil) e
  letI : T3Space (NilpotentLieBCHGroup L s hnil) := (basisHomeomorph e).isEmbedding.t3Space
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ι → ℝ) (NilpotentLieBCHGroup L s hnil)

theorem rightEMetricSpace_topology :
    (rightEMetricSpace (hnil := hnil) e).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (NilpotentLieBCHGroup L s hnil)) := rfl

@[instance_reducible]
noncomputable def rightMetricSpace : MetricSpace (NilpotentLieBCHGroup L s hnil) := by
  letI := rightEMetricSpace (hnil := hnil) e
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

theorem rightMetricSpace_topology :
    (rightMetricSpace (hnil := hnil) e).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (NilpotentLieBCHGroup L s hnil)) := rfl

theorem rightMetricSpace_isRiemannian :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightMetricSpace (hnil := hnil) e
    IsRiemannianManifold 𝓘(ℝ, ι → ℝ) (NilpotentLieBCHGroup L s hnil) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e ∞
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  exact ⟨fun _ _ => rfl⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

theorem basis_extChartAt_apply (g x : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    extChartAt 𝓘(ℝ, ι → ℝ) g x = basisHomeomorph e x := rfl

theorem basis_extChartAt_symm_apply (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    (extChartAt 𝓘(ℝ, ι → ℝ) g).symm x = (basisHomeomorph e).symm x := by
  let := basisChartedSpace (hnil := hnil) e
  have hs : (basisHomeomorph e).symm x ∈ (extChartAt 𝓘(ℝ, ι → ℝ) g).source := by
    rw [extChartAt_source]
    exact basisChart_mem_source e g _
  have h := (extChartAt 𝓘(ℝ, ι → ℝ) g).left_inv hs
  rw [basis_extChartAt_apply, Homeomorph.apply_symm_apply] at h
  exact h

variable [IsScalarTower ℚ ℝ L]

theorem mfderiv_mul_right_coordinates (g h : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v =
      fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) v := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e 1
  have hm : MDifferentiableAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g :=
    contMDiff_mul_right.mdifferentiableAt one_ne_zero
  rw [hm.mfderiv_abuse]
  simp only [writtenInExtChartAt, Function.comp_def, basis_extChartAt_apply,
    basis_extChartAt_symm_apply, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

theorem enorm_mfderiv_mul_right (g h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v‖ₑ = ‖v‖ₑ := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  have hn : ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    congr 1
    change rightInnerForm e (g * h)
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v)
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v) = rightInnerForm e g v v
    have hv := mfderiv_mul_right_coordinates e g h v
    exact (congrArg₂ (fun a b : ι → ℝ => rightInnerForm e (g * h) a b) hv hv).trans
      (rightInnerForm_right_invariant e g h v v)
  exact enorm_eq_iff_norm_eq.mpr hn

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

theorem riemannianEDist_mul_right_le (x y h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    riemannianEDist 𝓘(ℝ, ι → ℝ) (x * h) (y * h) ≤ riemannianEDist 𝓘(ℝ, ι → ℝ) x y := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e 1
  exact riemannianEDist_le_of_mfderiv_norm_le contMDiff_mul_right
    (fun z v => (enorm_mfderiv_mul_right e z h v).le) x y

theorem riemannianEDist_mul_right (x y h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    riemannianEDist 𝓘(ℝ, ι → ℝ) (x * h) (y * h) = riemannianEDist 𝓘(ℝ, ι → ℝ) x y := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  apply le_antisymm (riemannianEDist_mul_right_le e x y h)
  simpa only [mul_inv_cancel_right] using riemannianEDist_mul_right_le e (x * h) (y * h) h⁻¹

theorem rightMetricSpace_isometry_mul_right (h : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    Isometry (fun x => x * h) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  intro x y
  exact riemannianEDist_mul_right e x y h

theorem rightMetricSpace_isIsometricSMul :
    letI := rightMetricSpace (hnil := hnil) e
    IsIsometricSMul (NilpotentLieBCHGroup L s hnil)ᵐᵒᵖ (NilpotentLieBCHGroup L s hnil) := by
  let := rightMetricSpace (hnil := hnil) e
  exact ⟨fun h => rightMetricSpace_isometry_mul_right e h.unop⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module

noncomputable def basisCoordinateMap {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ[ℝ] M) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  LinearMap.toContinuousLinearMap
    (f.equivFun.toLinearMap.comp (φ.comp e.equivFun.symm.toLinearMap))

@[simp] theorem basisCoordinateMap_apply {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ[ℝ] M) (x : ι → ℝ) :
    basisCoordinateMap e f φ x = f.equivFun (φ (e.equivFun.symm x)) := rfl

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]

def realLieHomToRat (φ : L →ₗ⁅ℝ⁆ M) : L →ₗ⁅ℚ⁆ M where
  toLinearMap := φ.toLinearMap.restrictScalars ℚ
  map_lie' {x y} := φ.map_lie x y

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def mapReal (φ : L →ₗ⁅ℝ⁆ M) :
    NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M t hM :=
  mapOfSteps (realLieHomToRat φ)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]

open scoped Manifold ContDiff

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem mapReal_basisHomeomorph (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph f (mapReal (hM := hM) φ g) =
      basisCoordinateMap e f φ.toLinearMap (basisHomeomorph e g) := by
  change f.equivFun (φ g.coord) = f.equivFun (φ (e.equivFun.symm (e.equivFun g.coord)))
  rw [LinearEquiv.symm_apply_apply]

theorem mapReal_basisHomeomorph_symm (x : ι → ℝ) :
    mapReal (hnil := hnil) (hM := hM) φ ((basisHomeomorph e).symm x) =
      (basisHomeomorph f).symm (basisCoordinateMap e f φ.toLinearMap x) := by
  apply (basisHomeomorph f).injective
  rw [mapReal_basisHomeomorph e f, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem contMDiff_mapReal (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) n (mapReal (hnil := hnil) (hM := hM) φ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph f).isOpenEmbedding
  have hc := (basisCoordinateMap e f φ.toLinearMap).contDiff.contMDiff.comp
    (contMDiff_basisHomeomorph (hnil := hnil) e n)
  convert hc using 1; try rfl
  funext g
  exact mapReal_basisHomeomorph e f φ g

theorem mfderiv_mapReal_coordinates (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hnil := hnil) (hM := hM) φ) g v =
      basisCoordinateMap e f φ.toLinearMap v := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  have hm := (contMDiff_mapReal (hnil := hnil) (hM := hM) e f φ 1).mdifferentiableAt
    (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) g (mapReal (hM := hM) φ) =
      basisCoordinateMap e f φ.toLinearMap := by
    funext x
    simp only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_apply,
      basis_extChartAt_symm_apply, mapReal_basisHomeomorph e f, Homeomorph.apply_symm_apply]
  rw [hm.mfderiv_abuse, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    ContinuousLinearMap.fderiv]
  rfl

theorem basisCoordinateMap_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    basisCoordinateMap e f φ.toLinearMap (rightTranslate e g x) =
      rightTranslate f (mapReal (hM := hM) φ g) (basisCoordinateMap e f φ.toLinearMap x) := by
  change basisCoordinateMap e f φ.toLinearMap
    (basisHomeomorph e ((basisHomeomorph e).symm x * g)) = _
  rw [← mapReal_basisHomeomorph e f φ, map_mul, mapReal_basisHomeomorph_symm e f φ]
  rfl

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)

noncomputable def homCoordinates (v : ι → ℝ) : κ → ℝ :=
  basisHomeomorph f (φ ((basisHomeomorph e).symm v))

theorem homCoordinates_apply (g : NilpotentLieBCHGroup L s hnil) :
    homCoordinates e f φ (basisHomeomorph e g) = basisHomeomorph f (φ g) := by
  simp only [homCoordinates, Homeomorph.symm_apply_apply]

theorem homCoordinates_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    homCoordinates e f φ (rightTranslate e g v) =
      rightTranslate f (φ g) (homCoordinates e f φ v) := by
  simp only [homCoordinates, rightTranslate, Homeomorph.symm_apply_apply, map_mul]

theorem homCoordinates_continuous (hφ : Continuous φ) : Continuous (homCoordinates e f φ) :=
  (basisHomeomorph f).continuous.comp (hφ.comp (basisHomeomorph e).symm.continuous)

@[simp] theorem homCoordinates_zero : homCoordinates e f φ 0 = 0 := by
  have he : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply ext
    exact map_zero e.equivFun.symm
  simp only [homCoordinates, he, map_one]
  exact map_zero f.equivFun

theorem basisHomeomorph_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    basisHomeomorph e (g ^ n) = n • basisHomeomorph e g := by
  change e.equivFun (g ^ n).coord = n • e.equivFun g.coord
  rw [coord_pow, map_nsmul]

theorem basisHomeomorph_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    basisHomeomorph e (g ^ n) = n • basisHomeomorph e g := by
  change e.equivFun (g ^ n).coord = n • e.equivFun g.coord
  rw [coord_zpow, map_zsmul]

theorem homCoordinates_nsmul (n : ℕ) (v : ι → ℝ) :
    homCoordinates e f φ (n • v) = n • homCoordinates e f φ v := by
  have he : (basisHomeomorph (hnil := hnil) e).symm (n • v) =
      ((basisHomeomorph e).symm v) ^ n := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_pow]
  simp only [homCoordinates, he, map_pow, basisHomeomorph_pow]

theorem homCoordinates_zsmul (n : ℤ) (v : ι → ℝ) :
    homCoordinates e f φ (n • v) = n • homCoordinates e f φ v := by
  have he : (basisHomeomorph (hnil := hnil) e).symm (n • v) =
      ((basisHomeomorph e).symm v) ^ n := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_zpow]
  simp only [homCoordinates, he, map_zpow, basisHomeomorph_zpow]

theorem homCoordinates_natCast_smul (n : ℕ) (v : ι → ℝ) :
    homCoordinates e f φ ((n : ℝ) • v) = (n : ℝ) • homCoordinates e f φ v := by
  simpa only [Nat.cast_smul_eq_nsmul] using homCoordinates_nsmul e f φ n v

theorem homCoordinates_intCast_smul (n : ℤ) (v : ι → ℝ) :
    homCoordinates e f φ ((n : ℝ) • v) = (n : ℝ) • homCoordinates e f φ v := by
  simpa only [Int.cast_smul_eq_zsmul] using homCoordinates_zsmul e f φ n v

theorem homCoordinates_ratCast_smul (q : ℚ) (v : ι → ℝ) :
    homCoordinates e f φ ((q : ℝ) • v) = (q : ℝ) • homCoordinates e f φ v := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  apply smul_right_injective (κ → ℝ) hd
  dsimp only
  rw [← homCoordinates_natCast_smul, smul_smul, hq, homCoordinates_intCast_smul,
    smul_smul, hq]

theorem homCoordinates_smul (hφ : Continuous φ) (t : ℝ) (v : ι → ℝ) :
    homCoordinates e f φ (t • v) = t • homCoordinates e f φ v := by
  have heq : (fun t : ℝ => homCoordinates e f φ (t • v)) =
      fun t : ℝ => t • homCoordinates e f φ v :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).equalizer
      ((homCoordinates_continuous e f φ hφ).comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
      (funext fun q => homCoordinates_ratCast_smul e f φ q v)
  exact congrFun heq t

theorem homCoordinates_eq_fderiv (hφ : Continuous φ)
    (hd : DifferentiableAt ℝ (homCoordinates e f φ) 0) (v : ι → ℝ) :
    homCoordinates e f φ v = fderiv ℝ (homCoordinates e f φ) 0 v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hD : HasFDerivAt (homCoordinates e f φ) (fderiv ℝ (homCoordinates e f φ) 0)
      ((0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have hcomp := hD.comp_hasDerivAt (0 : ℝ) hline
  have heq : homCoordinates e f φ ∘ (fun t : ℝ => t • v) =
      fun t : ℝ => t • homCoordinates e f φ v :=
    funext fun t => homCoordinates_smul e f φ hφ t v
  rw [heq] at hcomp
  have hlin : HasDerivAt (fun t : ℝ => t • homCoordinates e f φ v)
      (homCoordinates e f φ v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (homCoordinates e f φ v)
  exact hlin.unique hcomp

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

include e in
theorem continuous_conjugation : Continuous ((MulAut.conj a).toMonoidHom) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem contDiff_conjugationCoordinates (n : ℕ∞ω) :
    ContDiff ℝ n (homCoordinates e e (MulAut.conj a).toMonoidHom) := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  exact ((contMDiff_basisHomeomorph e n).comp
    ((contMDiff_const.mul (contMDiff_basisHomeomorph_symm e n)).mul contMDiff_const)).contDiff

noncomputable def conjugationLinearMap : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  fderiv ℝ (homCoordinates e e (MulAut.conj a).toMonoidHom) 0

theorem homCoordinates_conjugation_eq :
    homCoordinates e e (MulAut.conj a).toMonoidHom = conjugationLinearMap e a := by
  funext v
  exact homCoordinates_eq_fderiv e e (MulAut.conj a).toMonoidHom (continuous_conjugation e a)
    ((contDiff_conjugationCoordinates e a 1).differentiable one_ne_zero).differentiableAt v

theorem conjugationLinearMap_coordinates (x : NilpotentLieBCHGroup L s hnil) :
    conjugationLinearMap e a (basisHomeomorph e x) = basisHomeomorph e (a * x * a⁻¹) := by
  rw [← homCoordinates_conjugation_eq, homCoordinates_apply]
  rfl

theorem conjugationLinearMap_basis [DecidableEq ι] (i k : ι) :
    conjugationLinearMap e a (Pi.single i 1) k =
      e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k := by
  have he : basisHomeomorph (hnil := hnil) e ⟨e i⟩ = Pi.single i 1 := by
    funext j
    simpa only [basisHomeomorph_apply, Pi.single_apply, eq_comm] using e.equivFun_self i j
  rw [← he, conjugationLinearMap_coordinates]
  rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI
