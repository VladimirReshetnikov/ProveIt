/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily

namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

noncomputable def principalSliceSlope (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) : ℝ :=
  c b * width (b, i) * ∏ j ∈ Finset.univ.erase i,
    (lower (b, j) + width (b, j) * x (b, j))

theorem principalSliceValue_fderiv_single (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) :
    fderiv ℝ (principalSliceValue c lower width) x (Pi.single (b, i) 1) =
      principalSliceSlope c lower width x b i := by
  let g := fun b j (y : B × F → ℝ) => lower (b, j) + width (b, j) * y (b, j)
  have hd (b : B) (j : F) : HasFDerivAt (g b j)
      (width (b, j) • (ContinuousLinearMap.proj (b, j) : (B × F → ℝ) →L[ℝ] ℝ)) x := by
    have he : HasFDerivAt (fun y : B × F → ℝ => y (b, j))
        (ContinuousLinearMap.proj (b, j) : (B × F → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_apply (b, j) x
    simpa only [g] using (he.const_mul (width (b, j))).const_add (lower (b, j))
  have hp (b : B) := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd b j)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hp b).const_mul (c b))
  change fderiv ℝ (fun y => ∑ b, c b * ∏ j, g b j y) x (Pi.single (b, i) 1) = _
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one, principalSliceSlope, g]
      ring
    · intro j _ hji
      simp [hji]
    · simp
  · intro b' _ hbb
    simp [hbb]
  · simp

omit [Fintype B] [DecidableEq B] in
theorem principalSliceSlope_lower (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) {a δ r : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hc : a ≤ |c b|)
    (hw : ∀ j, δ ≤ width (b, j))
    (hlower : ∀ j ≠ i, 0 ≤ lower (b, j)) (hx : ∀ j ≠ i, r ≤ x (b, j)) :
    a * δ * (δ * r) ^ (Fintype.card F - 1) ≤ |principalSliceSlope c lower width x b i| := by
  have hfactor (j) (hj : j ∈ Finset.univ.erase i) :
      δ * r ≤ lower (b, j) + width (b, j) * x (b, j) := by
    have hji := Finset.ne_of_mem_erase hj
    exact (mul_le_mul (hw j) (hx j hji) hr (hδ.trans (hw j))).trans
      (le_add_of_nonneg_left (hlower j hji))
  have hprod : (δ * r) ^ (Fintype.card F - 1) ≤
      ∏ j ∈ Finset.univ.erase i, (lower (b, j) + width (b, j) * x (b, j)) := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ.erase i)
      (fun _ _ => mul_nonneg hδ hr) hfactor
    simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ] using h
  have hp0 := (pow_nonneg (mul_nonneg hδ hr) (Fintype.card F - 1)).trans hprod
  rw [principalSliceSlope, abs_mul, abs_mul, abs_of_nonneg (hδ.trans (hw i)),
    abs_of_nonneg hp0]
  exact mul_le_mul (mul_le_mul hc (hw i) hδ (ha.trans hc)) hprod
    (pow_nonneg (mul_nonneg hδ hr) _) (mul_nonneg (abs_nonneg _) (hδ.trans (hw i)))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

theorem scalar_identity_inverse_abs_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible ∧
      ‖(a • ContinuousLinearMap.id ℝ E).inverse‖ ≤ |a|⁻¹ := by
  let A := a • ContinuousLinearMap.id ℝ E
  let B := a⁻¹ • ContinuousLinearMap.id ℝ E
  have hAB : A.comp B = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ha]
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ha]
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hAB hBA, ?_⟩
  change ‖A.inverse‖ ≤ _
  rw [ContinuousLinearMap.inverse_eq hAB hBA]
  calc
    ‖B‖ = |a|⁻¹ * ‖ContinuousLinearMap.id ℝ E‖ := by
      simp only [B, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |a|⁻¹ := mul_le_of_le_one_right (inv_nonneg.mpr (abs_nonneg _))
      ContinuousLinearMap.norm_id_le

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceSingleton (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) : Unit → ℝ := fun _ => principalSliceValue c lower width x

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceSingleton_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceSingleton c lower width) :=
  contDiff_pi.mpr (fun _ => principalSliceValue_contDiff c lower width)

theorem principalSliceSingleton_selectedDerivative (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) :
    selectedDerivative (principalSliceSingleton c lower width)
      (coordinateInjection (fun _ : Unit => (b, i))) x =
      principalSliceSlope c lower width x b i • ContinuousLinearMap.id ℝ (Unit → ℝ) := by
  have hd := (principalSliceSingleton_contDiff c lower width).differentiable (by norm_num)
  have hh := principalSliceValue_fderiv_single c lower width x b i
  change fderiv ℝ (fun y => principalSliceSingleton c lower width y ()) x
    (Pi.single (b, i) 1) = _ at hh
  rw [fderiv_apply (hd x) ()] at hh
  change (fderiv ℝ (principalSliceSingleton c lower width) x (Pi.single (b, i) 1)) () =
    principalSliceSlope c lower width x b i at hh
  ext y u
  cases u
  have hJ : coordinateInjection (fun _ : Unit => (b, i)) y =
      y () • (Pi.single (b, i) 1 : B × F → ℝ) := by
    simp only [coordinateInjection_apply, Fintype.sum_unique, ← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [selectedDerivative, ContinuousLinearMap.comp_apply, hJ, map_smul,
    smul_apply, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply, hh]
  ring

theorem principalSliceSingleton_inverse_bound (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) {κ : ℝ} (hκ : 0 < κ)
    (hbound : κ ≤ |principalSliceSlope c lower width x b i|) :
    (selectedDerivative (principalSliceSingleton c lower width)
      (coordinateInjection (fun _ : Unit => (b, i))) x).IsInvertible ∧
      ‖(selectedDerivative (principalSliceSingleton c lower width)
        (coordinateInjection (fun _ : Unit => (b, i))) x).inverse‖ ≤ κ⁻¹ := by
  rw [principalSliceSingleton_selectedDerivative]
  have h := scalar_identity_inverse_abs_bound
    (E := Unit → ℝ) (abs_pos.mp (hκ.trans_le hbound))
  exact ⟨h.1, h.2.trans (inv_anti₀ hκ hbound)⟩

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedPrincipal (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :=
  sigmaAxisSampler (fun d => principalSliceSingleton (c d) (lower d) (width d))

noncomputable def jointSlicedInjection (b : ∀ d, B d) (i : ∀ d, F d) :=
  sigmaAxisOperator (fun d => coordinateInjection (fun _ : Unit => (b d, i d)))

theorem jointSlicedInjection_norm_le (b : ∀ d, B d) (i : ∀ d, F d) :
    ‖jointSlicedInjection b i‖ ≤ 1 :=
  sigmaAxisOperator_norm_le _ zero_le_one
    (fun _ => coordinateInjection_norm_le _ (Function.injective_of_subsingleton _))

omit [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)] in
theorem jointSlicedPrincipal_contDiff (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    ContDiff ℝ ∞ (jointSlicedPrincipal c lower width) :=
  sigmaAxisSampler_contDiff _ (fun d => principalSliceSingleton_contDiff (c d) (lower d) (width d))

theorem jointSlicedPrincipal_inverse_bound (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (b : ∀ d, B d) (i : ∀ d, F d)
    (x : (Σ d, B d × F d) → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hbound : ∀ d, κ ≤ |principalSliceSlope (c d) (lower d) (width d)
      (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d)|) :
    (selectedDerivative (jointSlicedPrincipal c lower width) (jointSlicedInjection b i) x).IsInvertible ∧
      ‖(selectedDerivative (jointSlicedPrincipal c lower width) (jointSlicedInjection b i) x).inverse‖ ≤ κ⁻¹ := by
  have hi (d) := principalSliceSingleton_inverse_bound (c d) (lower d) (width d)
    (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d) hκ (hbound d)
  exact sigmaAxisSampler_inverse_bound _ _ x
    (fun d => (principalSliceSingleton_contDiff (c d) (lower d) (width d)).differentiable
      (by norm_num) _) (fun d => (hi d).1) (inv_nonneg.mpr hκ.le) (fun d => (hi d).2)

theorem jointSlicedPrincipal_perturbed_inverse (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (b : ∀ d, B d) (i : ∀ d, F d)
    (x : (Σ d, B d × F d) → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hbound : ∀ d, κ ≤ |principalSliceSlope (c d) (lower d) (width d)
      (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d)|)
    (V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ))
    (hsmall : κ⁻¹ * ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ 1 / 2) :
    (selectedDerivative V (jointSlicedInjection b i) x).IsInvertible ∧
      ‖(selectedDerivative V (jointSlicedInjection b i) x).inverse‖ ≤ 2 * κ⁻¹ := by
  have hi := jointSlicedPrincipal_inverse_bound c lower width b i x hκ hbound
  apply selected_inverse_perturbation _ V (jointSlicedInjection b i) x hi.1
    ⟨κ⁻¹, inv_nonneg.mpr hκ.le⟩ hi.2
  exact (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_right (norm_nonneg _) (jointSlicedInjection_norm_le b i))
      (inv_nonneg.mpr hκ.le)).trans hsmall

end Joint

end Erdos3

end

end OAI
