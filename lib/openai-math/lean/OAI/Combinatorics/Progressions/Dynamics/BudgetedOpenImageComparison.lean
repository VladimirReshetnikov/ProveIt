import OAI.Combinatorics.Progressions.Estimates.BoundedInequalityGoodCutoff
import OAI.Combinatorics.Progressions.Estimates.InverseDerivativeBound

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weighted_divergence_pointwise
    (w : (ι → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (V : ι → (ι → ℝ) → ℝ)
    (hV : ∀ i x, x ∈ tsupport w → ContDiffAt ℝ 1 (V i) x)
    (K L : ℝ≥0) (hK : ∀ i x, x ∈ tsupport w → |V i x| ≤ K)
    (hL : ∀ i x, x ∈ tsupport w → |fderiv ℝ (V i) x (Pi.single i 1)| ≤ L)
    (x : ι → ℝ) :
    |coordinateDivergence (fun i x => w x * V i x) x| ≤
      (K : ℝ) * (∑ i, |fderiv ℝ w x (Pi.single i 1)|) +
        (Fintype.card ι : ℝ) * L * |w x| := by
  by_cases hx : x ∈ tsupport w
  · have hp (i : ι) : |fderiv ℝ (fun x => w x * V i x) x (Pi.single i 1)| ≤
        (K : ℝ) * |fderiv ℝ w x (Pi.single i 1)| + L * |w x| := by
      rw [fderiv_fun_mul (hw.differentiable (by norm_num) x)
        ((hV i x hx).differentiableAt (by norm_num))]
      simp only [add_apply, smul_apply, smul_eq_mul]
      have h := abs_add_le (w x * fderiv ℝ (V i) x (Pi.single i 1))
        (V i x * fderiv ℝ w x (Pi.single i 1))
      simp only [abs_mul] at h
      have ha := mul_le_mul_of_nonneg_left (hL i x hx) (abs_nonneg (w x))
      have hb := mul_le_mul_of_nonneg_right (hK i x hx) (abs_nonneg (fderiv ℝ w x (Pi.single i 1)))
      linarith
    calc
      |coordinateDivergence (fun i x => w x * V i x) x| ≤
          ∑ i, |fderiv ℝ (fun x => w x * V i x) x (Pi.single i 1)| := by
        have h := norm_sum_le Finset.univ
          (fun i : ι => fderiv ℝ (fun x => w x * V i x) x (Pi.single i 1))
        simp only [Real.norm_eq_abs] at h
        exact h
      _ ≤ ∑ i, ((K : ℝ) * |fderiv ℝ w x (Pi.single i 1)| + L * |w x|) :=
        Finset.sum_le_sum (fun i _ => hp i)
      _ = (K : ℝ) * (∑ i, |fderiv ℝ w x (Pi.single i 1)|) +
          (Fintype.card ι : ℝ) * L * |w x| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  · have hs : tsupport (coordinateDivergence (fun i x => w x * V i x)) ⊆ tsupport w :=
      coordinateDivergence_tsupport_subset _ (isClosed_tsupport w)
        (fun i => tsupport_smul_subset_left w (V i))
    rw [image_eq_zero_of_notMem_tsupport (f := coordinateDivergence (fun i x => w x * V i x))
      (fun h => hx (hs h)), abs_zero]
    positivity

theorem coordinate_derivative_integrable
    (w : (ι → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (i : ι) :
    Integrable (fun x => |fderiv ℝ w x (Pi.single i 1)|) := by
  have hi : Integrable (fun x => fderiv ℝ w x (Pi.single i 1)) volume :=
    ((hw.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (Pi.single i 1))
  simpa only [Real.norm_eq_abs] using hi.norm

theorem weighted_divergence_integral_bound
    (w : (ι → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (V : ι → (ι → ℝ) → ℝ) (hV : ∀ i x, x ∈ tsupport w → ContDiffAt ℝ 1 (V i) x)
    (K L : ℝ≥0) (hK : ∀ i x, x ∈ tsupport w → |V i x| ≤ K)
    (hL : ∀ i x, x ∈ tsupport w → |fderiv ℝ (V i) x (Pi.single i 1)| ≤ L) :
    (∫ x, |coordinateDivergence (fun i x => w x * V i x) x|) ≤
      (K : ℝ) * (∑ i, ∫ x, |fderiv ℝ w x (Pi.single i 1)|) +
        (Fintype.card ι : ℝ) * L * ∫ x, |w x| := by
  have hQi (i : ι) : ContDiff ℝ 1 (fun x => w x * V i x) :=
    contDiff_mul_of_local_right hw (hV i)
  have hdi : Integrable (coordinateDivergence (fun i x => w x * V i x)) volume :=
    (coordinateDivergence_continuous _ hQi).integrable_of_hasCompactSupport
      (coordinateDivergence_hasCompactSupport _ (fun _ => hs.mul_right))
  have hleft : Integrable (fun x => |coordinateDivergence (fun i x => w x * V i x) x|) := by
    simpa only [Real.norm_eq_abs] using hdi.norm
  have hgrad : Integrable (fun x => ∑ i, |fderiv ℝ w x (Pi.single i 1)|) :=
    integrable_finsetSum _ (fun i _ => coordinate_derivative_integrable w hw hs i)
  have hwi : Integrable (fun x => |w x|) volume := by
    have hi : Integrable w volume := hw.continuous.integrable_of_hasCompactSupport hs
    simpa only [Real.norm_eq_abs] using hi.norm
  have h := integral_mono hleft ((hgrad.const_mul (K : ℝ)).add
    (hwi.const_mul ((Fintype.card ι : ℝ) * L))) (weighted_divergence_pointwise w hw V hV K L hK hL)
  simp only [Pi.add_apply] at h
  rw [integral_add (hgrad.const_mul (K : ℝ)) (hwi.const_mul ((Fintype.card ι : ℝ) * L)),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => coordinate_derivative_integrable w hw hs i)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem selectedInverseField_norm_le (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (i : ι) (j : κ) (x : κ → ℝ) :
    |selectedInverseField U J i j x| ≤ ‖J‖ * ‖(selectedDerivative U J x).inverse‖ := by
  calc
    |selectedInverseField U J i j x| ≤ ‖J ((selectedDerivative U J x).inverse (Pi.single i 1))‖ :=
      by
        have h := norm_le_pi_norm (J ((selectedDerivative U J x).inverse (Pi.single i 1))) j
        simp only [Real.norm_eq_abs] at h
        exact h
    _ ≤ ‖J‖ * ‖(selectedDerivative U J x).inverse (Pi.single i 1)‖ := J.le_opNorm _
    _ ≤ ‖J‖ * (‖(selectedDerivative U J x).inverse‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) :=
      mul_le_mul_of_nonneg_left ((selectedDerivative U J x).inverse.le_opNorm _) (norm_nonneg _)
    _ = ‖J‖ * ‖(selectedDerivative U J x).inverse‖ := by simp only [Pi.norm_single, norm_one, mul_one]

theorem selectedInverseField_derivative_norm_le (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ} (hU : ContDiffAt ℝ 2 U x)
    (hinv : (selectedDerivative U J x).IsInvertible) (i : ι) (j : κ) (v : κ → ℝ) :
    |fderiv ℝ (selectedInverseField U J i j) x v| ≤
      ‖J‖ * ‖(selectedDerivative U J x).inverse‖ ^ 2 * ‖fderiv ℝ (selectedDerivative U J) x v‖ := by
  let A := selectedDerivative U J
  let W := fun y => J ((A y).inverse (Pi.single i 1))
  have hA : ContDiffAt ℝ 1 A x := (hU.fderiv_right (by norm_num)).clm_comp contDiffAt_const
  have hi : DifferentiableAt ℝ (fun y => (A y).inverse) x :=
    (hinv.contDiffAt_map_inverse.comp x hA).differentiableAt (by norm_num)
  have hinner : DifferentiableAt ℝ (fun y => (A y).inverse (Pi.single i 1)) x :=
    hi.clm_apply (differentiableAt_const _)
  have hW : DifferentiableAt ℝ W x := J.differentiableAt.comp x hinner
  have hcoord : fderiv ℝ (selectedInverseField U J i j) x v = (fderiv ℝ W x v) j := by
    change fderiv ℝ (fun y => W y j) x v = _
    rw [fderiv_apply hW j]
    rfl
  have hvec : fderiv ℝ W x v = J ((fderiv ℝ (fun y => (A y).inverse) x v) (Pi.single i 1)) := by
    change fderiv ℝ (J ∘ (fun y => (A y).inverse (Pi.single i 1))) x v = _
    rw [fderiv_comp x J.differentiableAt hinner, J.fderiv, ContinuousLinearMap.comp_apply,
      fderiv_clm_apply hi (differentiableAt_const _)]
    simp
  rw [hcoord]
  calc
    |(fderiv ℝ W x v) j| ≤ ‖fderiv ℝ W x v‖ := by
      have h := norm_le_pi_norm (fderiv ℝ W x v) j
      simp only [Real.norm_eq_abs] at h
      exact h
    _ = ‖J ((fderiv ℝ (fun y => (A y).inverse) x v) (Pi.single i 1))‖ := by rw [hvec]
    _ ≤ ‖J‖ * ‖(fderiv ℝ (fun y => (A y).inverse) x v) (Pi.single i 1)‖ := J.le_opNorm _
    _ ≤ ‖J‖ * (‖fderiv ℝ (fun y => (A y).inverse) x v‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ (fun y => (A y).inverse) x v).le_opNorm _) (norm_nonneg _)
    _ = ‖J‖ * ‖fderiv ℝ (fun y => (A y).inverse) x v‖ := by
      simp only [Pi.norm_single, norm_one, mul_one]
    _ ≤ ‖J‖ * (‖(A x).inverse‖ ^ 2 * ‖fderiv ℝ A x v‖) :=
      mul_le_mul_of_nonneg_left (inverseMap_fderiv_norm_le A (hA.differentiableAt (by norm_num)) hinv v)
        (norm_nonneg _)
    _ = _ := by ring

theorem selected_inverse_divergence_bound [DecidableEq κ]
    (U : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 2 U x)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (K H : ℝ≥0) (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hH : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H) (i : ι) :
    (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField U J i j x) x|) ≤
      (‖J‖ * K) * (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) +
        (Fintype.card κ : ℝ) * (‖J‖ * K ^ 2 * H) * ∫ x, |w x| := by
  have hval (j : κ) (x : κ → ℝ) (hx : x ∈ tsupport w) :
      |selectedInverseField U J i j x| ≤ (‖J‖₊ * K : ℝ≥0) := by
    exact (selectedInverseField_norm_le U J i j x).trans
      (mul_le_mul_of_nonneg_left (hK x hx) (norm_nonneg _))
  have hder (j : κ) (x : κ → ℝ) (hx : x ∈ tsupport w) :
      |fderiv ℝ (selectedInverseField U J i j) x (Pi.single j 1)| ≤ (‖J‖₊ * K ^ 2 * H : ℝ≥0) := by
    have hA : ‖fderiv ℝ (selectedDerivative U J) x (Pi.single j 1)‖ ≤ (H : ℝ) := by
      have h := (fderiv ℝ (selectedDerivative U J) x).le_opNorm (Pi.single j 1)
      simp only [Pi.norm_single, norm_one, mul_one] at h
      exact h.trans (hH x hx)
    have hpow : ‖(selectedDerivative U J x).inverse‖ ^ 2 ≤ (K : ℝ) ^ 2 := by
      gcongr
      exact hK x hx
    apply (selectedInverseField_derivative_norm_le U J (hU x hx) (hinv x hx) i j (Pi.single j 1)).trans
    change _ ≤ ‖J‖ * (K : ℝ) ^ 2 * (H : ℝ)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (norm_nonneg J)) hA (norm_nonneg _)
      (mul_nonneg (norm_nonneg J) (sq_nonneg (K : ℝ)))
  exact weighted_divergence_integral_bound w hw hs (selectedInverseField U J i)
    (fun j x hx => selectedInverseField_contDiffAt_of_local U J (hU x hx) (hinv x hx) i j)
    (‖J‖₊ * K) (‖J‖₊ * K ^ 2 * H) hval hder

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem imageTranslationBound_of_inverse_budget
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1)
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∫ x, |w x|) ≤ 1)
    (K H S B : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hH : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    (hB : (K : ℝ) * S + (Fintype.card κ : ℝ) * ((K : ℝ) ^ 2 * H) ≤ B) :
    ImageTranslationBound (realDensityMeasure volume w) U ((Fintype.card ι : ℝ≥0) * B) := by
  have hsum : (∑ _ : ι, B) = (Fintype.card ι : ℝ≥0) * B := by simp
  rw [← hsum]
  apply imageTranslationBound_of_selected_inverse U hU J w hw hs hw0 hinv (fun _ => B)
  intro i
  apply (selected_inverse_divergence_bound U J w hw hs (fun _ _ => hU.contDiffAt)
    hinv K H hK hH i).trans
  apply le_trans _ hB
  have hJK : ‖J‖ * (K : ℝ) ≤ K := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ K.coe_nonneg
  have hJH : ‖J‖ * (K : ℝ) ^ 2 * H ≤ (K : ℝ) ^ 2 * H := by
    have ht := mul_le_mul_of_nonneg_right hJ (sq_nonneg (K : ℝ))
    rw [one_mul] at ht
    exact mul_le_mul_of_nonneg_right ht H.coe_nonneg
  have hsum0 : 0 ≤ ∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)| :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  refine add_le_add (mul_le_mul hJK hS hsum0 K.coe_nonneg) ?_
  calc
    _ ≤ (Fintype.card κ : ℝ) * ((K : ℝ) ^ 2 * H) * ∫ x, |w x| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJH (Nat.cast_nonneg _))
        (integral_nonneg (fun _ => abs_nonneg _))
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hmass

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem open_domain_image_comparison_of_inverse_bounds
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (Ω : Set (κ → ℝ)) (hΩ : IsOpen Ω) (ρ χ : (κ → ℝ) → ℝ)
    (hρ : Measurable ρ) (hρi : IntegrableOn ρ Ω) (hρ0 : ∀ x ∈ Ω, 0 ≤ ρ x)
    (hρmass : (∫ x in Ω, ρ x) = 1) (hχ : Measurable χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => Ω.indicator ρ x * χ x))
    (hws : HasCompactSupport (fun x => Ω.indicator ρ x * χ x))
    (hwsΩ : tsupport (fun x => Ω.indicator ρ x * χ x) ⊆ Ω)
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hF : ∀ t, ContDiffOn ℝ 2 (F t) Ω)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ t x, x ∈ tsupport (fun x => Ω.indicator ρ x * χ x) →
      (selectedDerivative (F t) J x).IsInvertible)
    (K H : ℝ≥0)
    (hK : ∀ t x, x ∈ tsupport (fun x => Ω.indicator ρ x * χ x) →
      ‖(selectedDerivative (F t) J x).inverse‖ ≤ K)
    (hH : ∀ t x, x ∈ tsupport (fun x => Ω.indicator ρ x * χ x) →
      ‖fderiv ℝ (selectedDerivative (F t) J) x‖ ≤ H)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hbudget : (‖J‖ * K) * (∑ j, ∫ x, |fderiv ℝ (fun x => Ω.indicator ρ x * χ x) x (Pi.single j 1)|) +
      (Fintype.card κ : ℝ) * (‖J‖ * K ^ 2 * H) * (∫ x, |Ω.indicator ρ x * χ x|) ≤ B)
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ x in Ω, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, Ω.indicator ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x in Ω, ρ x * φ (F 0 x)) - ∫ x in Ω, ρ x * φ (F 1 x)| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  let w := fun x => Ω.indicator ρ x * χ x
  have hdiv (t : Fin 2) (i : ι) : (∫ x in Ω,
      |coordinateDivergence (fun j x => w x * selectedInverseField (F t) J i j x) x|) ≤ B := by
    have h := selected_inverse_divergence_bound (F t) J w hw hws
      (fun x hx => (hF t).contDiffAt (hΩ.mem_nhds (hwsΩ hx))) (hinv t) K H (hK t) (hH t) i
    rw [integral_abs_divergence_eq_setIntegral
      (fun j x => w x * selectedInverseField (F t) J i j x) w
      (fun j => tsupport_smul_subset_left w (selectedInverseField (F t) J i j)) hwsΩ] at h
    exact h.trans hbudget
  exact open_domain_image_comparison_sqrt Ω hΩ ρ χ hρ hρi hρ0 hρmass hχ hχ01 hw hws hwsΩ F hF J
    hinv B hB hdiv hε hcut hclose φ hφ hbound

end Erdos3

end

end OAI
