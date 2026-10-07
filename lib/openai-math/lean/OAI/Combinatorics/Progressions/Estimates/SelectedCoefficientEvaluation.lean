import Mathlib.Data.Matrix.ColumnRowPartitioned
import OAI.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
import OAI.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
import OAI.Combinatorics.Progressions.Probability.PivotDensityCap

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

noncomputable def splitFreeColumns (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) : (J ⊕ N → ℝ) →L[ℝ] (I → ℝ) :=
  B.comp (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (.inl j)) +
    C.comp (ContinuousLinearMap.pi fun n => ContinuousLinearMap.proj (.inr n))

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeColumns_apply (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) (y : J ⊕ N → ℝ) :
    splitFreeColumns B C y = B (fun j => y (.inl j)) + C (fun n => y (.inr n)) := rfl

noncomputable def splitFreeProfile (f : (J → ℝ) × (I → ℝ) → ℝ)
    (g : (N → ℝ) → ℝ) (p : (J ⊕ N → ℝ) × (I → ℝ)) : ℝ :=
  f ((fun j => p.1 (.inl j)), p.2) * g (fun n => p.1 (.inr n))

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_continuous {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (splitFreeProfile f g) := by
  unfold splitFreeProfile
  fun_prop

omit [Fintype I] [Fintype J] [Fintype N] in
theorem splitFreeProfile_nonneg {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ n, 0 ≤ g n) (p) :
    0 ≤ splitFreeProfile f g p := mul_nonneg (hf _) (hg _)

theorem splitFreeProfile_zero_outside {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {R S : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (hg : ∀ n, S < ‖n‖ → g n = 0)
    (p : (J ⊕ N → ℝ) × (I → ℝ)) (hp : max R S < ‖p‖) :
    splitFreeProfile f g p = 0 := by
  let y : J → ℝ := fun j => p.1 (.inl j)
  let n : N → ℝ := fun n => p.1 (.inr n)
  by_cases hy : R < ‖(y, p.2)‖
  · exact mul_eq_zero_of_left (hf _ hy) _
  · have hn : S < ‖n‖ := by
      by_contra! hn
      have hy' : ‖(y, p.2)‖ ≤ R := le_of_not_gt hy
      have hnorm : ‖p‖ ≤ max R S := by
        rw [Prod.norm_def]
        apply max_le
        · rw [← splitCoordinates_norm p.1, Prod.norm_def]
          exact max_le ((norm_fst_le (y, p.2)).trans (hy'.trans (le_max_left _ _)))
            (hn.trans (le_max_right _ _))
        · exact (norm_snd_le (y, p.2)).trans (hy'.trans (le_max_left _ _))
      exact (not_le_of_gt hp) hnorm
    exact mul_eq_zero_of_right _ (hg _ hn)

theorem splitFreeProfile_slice_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    Integrable (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by
  have hc : Continuous (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J → ℝ) × (N → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  apply hp
  have heq : ‖Sum.elim p.1 p.2‖ = ‖p‖ := (splitCoordinates_norm (Sum.elim p.1 p.2)).symm
  have hz := splitFreeProfile_zero_outside hfs hgs
    (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))
    (h.trans_le (heq ▸ norm_fst_le
      (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))))
  exact hz

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem normalizedIntegerColumns_fromCols (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P =
      Matrix.fromCols (normalizedIntegerColumns B T P) (normalizedIntegerColumns C Q P) := by
  ext i k
  cases k <;> simp [normalizedIntegerColumns_entry]

omit [DecidableEq I] [DecidableEq J] [DecidableEq N] in
theorem matrixSupCLM_fromCols (B : Matrix I J ℝ) (C : Matrix I N ℝ) :
    matrixSupCLM (Matrix.fromCols B C) = splitFreeColumns (matrixSupCLM B) (matrixSupCLM C) := by
  apply ContinuousLinearMap.ext
  intro y
  rw [matrixSupCLM_apply, splitFreeColumns_apply, matrixSupCLM_apply, matrixSupCLM_apply]
  exact Matrix.fromCols_mulVec B C y

theorem normalizedIntegerColumns_split (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    matrixSupCLM (normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P) =
      splitFreeColumns (matrixSupCLM (normalizedIntegerColumns B T P))
        (matrixSupCLM (normalizedIntegerColumns C Q P)) := by
  rw [normalizedIntegerColumns_fromCols, matrixSupCLM_fromCols]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeCoordinates_norm_le (p : (J ⊕ N → ℝ) × (I → ℝ)) :
    ‖((fun j => p.1 (.inl j)), p.2)‖ ≤ ‖p‖ ∧
      ‖fun n => p.1 (.inr n)‖ ≤ ‖p‖ := by
  have hleft : ‖fun j => p.1 (.inl j)‖ ≤ ‖p.1‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm p.1 (.inl j)
  have hright : ‖fun n => p.1 (.inr n)‖ ≤ ‖p.1‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun n => norm_le_pi_norm p.1 (.inr n)
  refine ⟨?_, hright.trans (norm_fst_le p)⟩
  rw [Prod.norm_def]
  exact max_le (hleft.trans (norm_fst_le p)) (norm_snd_le p)

theorem splitFreeProfile_lipschitz {f : (J → ℝ) × (I → ℝ) → ℝ}
    {g : (N → ℝ) → ℝ} {Kf Kg Hf Hg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfcap : ∀ p, ‖f p‖ ≤ Hf) (hgcap : ∀ n, ‖g n‖ ≤ Hg) :
    LipschitzWith (Hf * Kg + Hg * Kf) (splitFreeProfile f g) := by
  let F := fun p : (J ⊕ N → ℝ) × (I → ℝ) => f ((fun j => p.1 (.inl j)), p.2)
  let G := fun p : (J ⊕ N → ℝ) × (I → ℝ) => g (fun n => p.1 (.inr n))
  have hkernel : LipschitzWith 1 (fun p : (J ⊕ N → ℝ) × (I → ℝ) =>
      ((fun j => p.1 (.inl j)), p.2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitFreeCoordinates_norm_le (p - q)).1
  have hnonkernel : LipschitzWith 1 (fun p : (J ⊕ N → ℝ) × (I → ℝ) =>
      fun n => p.1 (.inr n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact (splitFreeCoordinates_norm_le (p - q)).2
  have hF : LipschitzWith Kf F := by simpa only [mul_one, Function.comp_def] using hf.comp hkernel
  have hG : LipschitzWith Kg G := by simpa only [mul_one, Function.comp_def] using hg.comp hnonkernel
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (F p * G p) (F q * G q) ≤ _
  rw [dist_eq_norm]
  have heq : F p * G p - F q * G q = F p * (G p - G q) + (F p - F q) * G q := by ring
  rw [heq]
  calc
    _ ≤ ‖F p * (G p - G q)‖ + ‖(F p - F q) * G q‖ := norm_add_le _ _
    _ = ‖F p‖ * ‖G p - G q‖ + ‖F p - F q‖ * ‖G q‖ := by rw [norm_mul, norm_mul]
    _ ≤ Hf * (Kg * dist p q) + (Kf * dist p q) * Hg := by
      apply add_le_add
      · exact mul_le_mul (hfcap _) (by simpa only [dist_eq_norm] using hG.dist_le_mul p q)
          (norm_nonneg _) Hf.coe_nonneg
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hF.dist_le_mul p q) (hgcap _)
          (norm_nonneg _) (mul_nonneg Kf.coe_nonneg dist_nonneg)
    _ = _ := by push_cast; ring

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

theorem normalizedIntegerColumns_entry_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) {H C : ℝ}
    (hH : 0 < H) (hT : ∀ j, 0 ≤ T j) (hA : ∀ i j, |(A i j : ℝ)| * T j ≤ C * H) :
    ∀ i j, |normalizedIntegerColumns A T (fun _ => H) i j| ≤ C := by
  intro i j
  rw [normalizedIntegerColumns_entry_div, abs_div, abs_mul, abs_of_nonneg (hT j), abs_of_pos hH]
  exact (div_le_iff₀ hH).mpr (hA i j)

theorem normalizedIntegerColumns_norm_bound {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) {H C : ℝ}
    (hH : 0 < H) (hC : 0 ≤ C) (hT : ∀ j, 0 ≤ T j)
    (hA : ∀ i j, |(A i j : ℝ)| * T j ≤ C * H) :
    ‖matrixSupCLM (normalizedIntegerColumns A T (fun _ => H))‖ ≤ Fintype.card J * C :=
  matrixSupCLM_norm_le _ hC (normalizedIntegerColumns_entry_bound A T hH hT hA)

theorem normalizedIntegerColumns_displacement {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) {H C R : ℝ}
    (hH : 0 < H) (hC : 0 ≤ C) (_hR : 0 ≤ R) (hT : ∀ j, 0 ≤ T j)
    (hA : ∀ i j, |(A i j : ℝ)| * T j ≤ C * H)
    (g : (J → ℝ) → ℝ) (hg : ∀ x, R < ‖x‖ → g x = 0) :
    ∀ x, g x ≠ 0 → ‖matrixSupCLM (normalizedIntegerColumns A T (fun _ => H)) x‖ ≤
      Fintype.card J * C * R := by
  intro x hx
  have hnorm : ‖x‖ ≤ R := le_of_not_gt (fun h => hx (hg x h))
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul (normalizedIntegerColumns_norm_bound A T hH hC hT hA) hnorm
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def smoothSplitProfile (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  smoothProductProfile J p.1 * smoothProductProfile I p.2

theorem smoothSplitProfile_join (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    smoothSplitProfile J I p = smoothProductProfile (J ⊕ I) (Sum.elim p.1 p.2) :=
  (smoothProductProfile_sum J I p.1 p.2).symm

theorem smoothSplitProfile_contDiff (J I : Type*) [Fintype J] [Fintype I] :
    ContDiff ℝ ∞ (smoothSplitProfile J I) :=
  ((smoothProductProfile_contDiff J).comp contDiff_fst).mul
    ((smoothProductProfile_contDiff I).comp contDiff_snd)

theorem smoothSplitProfile_range (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) :
    0 ≤ smoothSplitProfile J I p ∧ smoothSplitProfile J I p ≤ 1 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_range _ _

theorem smoothSplitProfile_norm_le (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ‖smoothSplitProfile J I p‖ ≤ 1 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_norm_le _ _

theorem sumElim_norm {J I : Type*} [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ‖Sum.elim p.1 p.2‖ = ‖p‖ :=
  (splitCoordinates_norm (Sum.elim p.1 p.2)).symm

theorem smoothSplitProfile_zero_outside (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) (hp : 1 < ‖p‖) : smoothSplitProfile J I p = 0 := by
  rw [smoothSplitProfile_join]
  exact smoothProductProfile_zero_outside _ _ (by rwa [sumElim_norm])

theorem smoothSplitProfile_integral (J I : Type*) [Fintype J] [Fintype I] :
    (∫ p, smoothSplitProfile J I p) = 1 := by
  change (∫ p : (J → ℝ) × (I → ℝ), smoothProductProfile J p.1 * smoothProductProfile I p.2
    ∂(volume.prod volume)) = 1
  rw [integral_prod_mul, smoothProductProfile_integral, smoothProductProfile_integral, one_mul]

theorem smoothSplitProfile_lipschitz (J I : Type*) [Fintype J] [Fintype I] :
    LipschitzWith ((Fintype.card J + Fintype.card I) * probabilityProfileLipschitz)
      (smoothSplitProfile J I) := by
  have hj : LipschitzWith 1 (fun p : (J → ℝ) × (I → ℝ) => Sum.elim p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have he : Sum.elim p.1 p.2 - Sum.elim q.1 q.2 = Sum.elim (p-q).1 (p-q).2 := by
      funext k
      cases k <;> rfl
    rw [he, sumElim_norm]
  have h := (smoothProductProfile_lipschitz (J ⊕ I)).comp hj
  simpa only [mul_one, Fintype.card_sum, Nat.cast_add, Function.comp_def,
    ← smoothSplitProfile_join] using h

theorem splitFreeProfile_smooth (J I N : Type*) [Fintype J] [Fintype I] [Fintype N] :
    splitFreeProfile (smoothSplitProfile J I) (smoothProductProfile N) =
      smoothSplitProfile (J ⊕ N) I := by
  funext p
  have h := smoothProductProfile_sum J N (fun j => p.1 (.inl j)) (fun n => p.1 (.inr n))
  have he : Sum.elim (fun j => p.1 (.inl j)) (fun n => p.1 (.inr n)) = p.1 := by
    funext k
    cases k <;> rfl
  rw [he] at h
  simp only [splitFreeProfile, smoothSplitProfile, h]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def selectedFreeFirstEquiv {I J : Type*} [Fintype I] (s : I ↪ J) :
    UnselectedColumn s ⊕ I ≃ J :=
  (Equiv.sumComm _ _).trans (selectedColumnEquiv s)

noncomputable def selectedCoefficientEquiv {I J : Type*} [Fintype I]
    (s : I ↪ J) (R : Type*) : (UnselectedColumn s → R) × (I → R) ≃ (J → R) :=
  (Equiv.sumPiEquivProdPi (fun _ : UnselectedColumn s ⊕ I => R)).symm.trans
    (Equiv.arrowCongr (selectedFreeFirstEquiv s) (Equiv.refl R))

theorem selectedCoefficientEquiv_apply {I J R : Type*} [Fintype I]
    (s : I ↪ J) (p : (UnselectedColumn s → R) × (I → R)) (j : J) :
    selectedCoefficientEquiv s R p j =
      Sum.elim p.1 p.2 ((selectedFreeFirstEquiv s).symm j) := rfl

theorem selectedCoefficientEquiv_norm {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (p : (UnselectedColumn s → ℝ) × (I → ℝ)) :
    ‖selectedCoefficientEquiv s ℝ p‖ = ‖p‖ := by
  change ‖(Sum.elim p.1 p.2) ∘ (selectedFreeFirstEquiv s).symm‖ = _
  exact ((selectedFreeFirstEquiv s).symm.surjective.pi_norm_comp (Sum.elim p.1 p.2)).trans
    (sumElim_norm p)

theorem selectedCoefficientEquiv_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) : LipschitzWith 1 (selectedCoefficientEquiv s ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have he : selectedCoefficientEquiv s ℝ p - selectedCoefficientEquiv s ℝ q =
      selectedCoefficientEquiv s ℝ (p - q) := by
    funext j
    simp only [Pi.sub_apply, selectedCoefficientEquiv_apply]
    cases (selectedFreeFirstEquiv s).symm j <;> rfl
  rw [he, selectedCoefficientEquiv_norm]

noncomputable def selectedCoefficientProfile {I J : Type*} [Fintype I]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) : (UnselectedColumn s → ℝ) × (I → ℝ) → ℝ :=
  f ∘ selectedCoefficientEquiv s ℝ

theorem selectedCoefficientProfile_nonneg {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ p, 0 ≤ selectedCoefficientProfile s f p := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_norm_le {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {H : ℝ} (hf : ∀ x, ‖f x‖ ≤ H) :
    ∀ p, ‖selectedCoefficientProfile s f p‖ ≤ H := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (selectedCoefficientProfile s f) := by
  simpa only [mul_one, selectedCoefficientProfile] using hf.comp (selectedCoefficientEquiv_lipschitz s)

theorem selectedCoefficientProfile_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) :
    ∀ p, R < ‖p‖ → selectedCoefficientProfile s f p = 0 := by
  intro p hp
  exact hf _ (by rwa [selectedCoefficientEquiv_norm])

theorem selectedCoefficientProfile_integral {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (f : (J → ℝ) → ℝ) :
    (∫ p, selectedCoefficientProfile s f p) = ∫ x, f x := by
  let e := selectedFreeFirstEquiv s
  have hsum := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : UnselectedColumn s ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : UnselectedColumn s ⊕ I => ℝ)).symm.measurableEmbedding
    (fun z => f (z ∘ e.symm))
  have hpi := (volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) e).integral_comp
    (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e).measurableEmbedding f
  apply hsum.trans
  simpa only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
    Equiv.coe_fn_symm_mk, eq_rec_constant, Function.comp_def] using hpi

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

theorem selectedCoefficientEquiv_on_selected
    (p : (UnselectedColumn s → R) × (I → R)) (i : I) :
    selectedCoefficientEquiv s R p (s i) = p.2 i := by
  have h : selectedFreeFirstEquiv s (Sum.inr i) = s i := rfl
  rw [← h, selectedCoefficientEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem selectedCoefficientEquiv_on_unselected
    (p : (UnselectedColumn s → R) × (I → R)) (i : UnselectedColumn s) :
    selectedCoefficientEquiv s R p i.val = p.1 i := by
  have h : selectedFreeFirstEquiv s (Sum.inl i) = i.val := rfl
  rw [← h, selectedCoefficientEquiv_apply, Equiv.symm_apply_apply]
  rfl

theorem selectedCoefficientEquiv_eq_of_coordinates
    (f : J → R) (p : (UnselectedColumn s → R) × (I → R))
    (hfree : ∀ i : UnselectedColumn s, f i.val = p.1 i)
    (hselected : ∀ i, f (s i) = p.2 i) :
    f = selectedCoefficientEquiv s R p := by
  classical
  funext j
  by_cases hj : j ∈ Set.range s
  · obtain ⟨i, rfl⟩ := hj
    exact (hselected i).trans (selectedCoefficientEquiv_on_selected s p i).symm
  · exact (hfree ⟨j, hj⟩).trans (selectedCoefficientEquiv_on_unselected s p ⟨j, hj⟩).symm

end Erdos3

end

end OAI
