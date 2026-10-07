import OAI.Combinatorics.Progressions.Estimates.GroupedSiteTensor
import OAI.Combinatorics.Progressions.Estimates.MaskedIntervalApproximation
import OAI.Combinatorics.Progressions.Probability.MaskedDensityTranslation

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def spatialStarDensity {I : Type*} (f : ((Unit ⊕ I) → ℝ) → ℝ)
    (y : (Unit ⊕ I) → ℝ) : ℂ := f (spatialUnstar y)

theorem spatialStarDensity_lipschitz {I : Type*} [Fintype I]
    {f : ((Unit ⊕ I) → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (2 * K) (spatialStarDensity f) := by
  unfold spatialStarDensity
  have h := Complex.isometry_ofReal.lipschitzWith.comp (hf.comp (spatialUnstar_lipschitz I))
  simpa only [one_mul, mul_comm K 2, Function.comp_def] using h

theorem spatialStarDensity_bound {I : Type*} (f : ((Unit ⊕ I) → ℝ) → ℝ) {C : ℝ}
    (hf : ∀ y, |f y| ≤ C) (y : (Unit ⊕ I) → ℝ) : ‖spatialStarDensity f y‖ ≤ C := by
  simpa only [spatialStarDensity, Complex.norm_real, Real.norm_eq_abs] using hf (spatialUnstar y)

noncomputable def spatialSiteApprox {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ)
    (v : (Unit ⊕ I) → ℤ) : ℂ :=
  maskedIntervalApprox b r H m (spatialStarDensity f) (latticeStarMask (pivotFullImage A B) m)
    (spatialStar v)

theorem spatialSiteApprox_error {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {G b r : ℝ} (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hb : 0 < b) (hr : 0 < r) (H : ℝ) (v : (Unit ⊕ I) → ℤ)
    (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖(maskedIntegerImageDensity A B (fun _ => H) f v : ℂ) - spatialSiteApprox A B m f H b r v‖ ≤
      4 * G * K * r := by
  rw [maskedIntegerImageDensity_star A B m hperiod H f v]
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have h := maskedIntervalApprox_error hb hr H m (spatialStarDensity f)
    (latticeStarMask (pivotFullImage A B) m) (spatialStarDensity_lipschitz hf) hG
    (latticeStarMask_bound _ _ hindex) (spatialStar v) hv
  exact h.trans_eq (by push_cast; ring)

theorem spatialSiteApprox_coefficient_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) {G C : ℝ}
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G) (hf : ∀ y, |f y| ≤ C) :
    (∑ a : (Unit ⊕ I) → ZMod m, ∑ k : (Unit ⊕ I) → Fin (intervalSiteCount b r),
      ‖latticeStarMask (pivotFullImage A B) m a *
        spatialStarDensity f (fun i => intervalSiteCenter b r (k i))‖) ≤
      (m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ I) * (G * C) :=
  maskedIntervalApprox_coefficient_sum b r m (spatialStarDensity f)
    (latticeStarMask (pivotFullImage A B) m) ((Nat.cast_nonneg _).trans hindex)
    (latticeStarMask_bound _ _ hindex) (spatialStarDensity_bound f hf)

noncomputable def spatialSiteRadius (G K ε : ℝ) : ℝ := ε / (4 * (1 + G) * (1 + K))

theorem spatialSiteRadius_pos {G K ε : ℝ} (hG : 0 ≤ G) (hK : 0 ≤ K) (hε : 0 < ε) :
    0 < spatialSiteRadius G K ε := by unfold spatialSiteRadius; positivity

theorem spatialSiteRadius_error {G K ε : ℝ} (hG : 0 ≤ G) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    4 * G * K * spatialSiteRadius G K ε ≤ ε := by
  have hd : 0 < 4 * (1 + G) * (1 + K) := by positivity
  unfold spatialSiteRadius
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem intervalTensorApprox_zero_outside {S : Type*} [Fintype S] [DecidableEq S]
    (B r : ℝ) (hr : 0 < r) (F : (S → ℝ) → ℂ) (a : ℝ)
    (hsupport : ∀ x, (∃ i, a < |x i|) → F x = 0)
    (x : S → ℝ) (hx : ∃ i, a + 2 * r < |x i|) :
    intervalTensorApprox B r F x = 0 := by
  unfold intervalTensorApprox
  apply Finset.sum_eq_zero
  intro k _
  by_cases hw : intervalTensorWeight B r k x = 0
  · simp only [hw, Complex.ofReal_zero, zero_mul]
  · have hp : 0 < intervalTensorWeight B r k x :=
      lt_of_le_of_ne (intervalTensorWeight_nonneg B hr k x) (Ne.symm hw)
    have hn := intervalTensorWeight_near hr k x hp
    obtain ⟨i, hi⟩ := hx
    have hdist := (dist_le_pi_dist x (fun i => intervalSiteCenter B r (k i)) i).trans hn
    have hcenter : a < |intervalSiteCenter B r (k i)| := by
      rw [Real.dist_eq] at hdist
      have ht : |x i| ≤ |x i - intervalSiteCenter B r (k i)| + |intervalSiteCenter B r (k i)| := by
        simpa only [sub_add_cancel] using abs_add_le (x i - intervalSiteCenter B r (k i)) (intervalSiteCenter B r (k i))
      linarith
    rw [hsupport _ ⟨i, hcenter⟩, mul_zero]

theorem spatialSiteApprox_zero_outside {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r a : ℝ) (hr : 0 < r)
    (hsupport : ∀ v, (∃ i, a < |spatialStar v i|) → f v = 0)
    (v : (Unit ⊕ I) → ℤ)
    (hv : ∃ i, a + 2 * r < |((spatialStar v i : ℤ) : ℝ) / H|) :
    spatialSiteApprox A B m f H b r v = 0 := by
  unfold spatialSiteApprox
  rw [maskedIntervalApprox_eq]
  have hzero := intervalTensorApprox_zero_outside b r hr (spatialStarDensity f) a
    (fun x hx => by
      unfold spatialStarDensity
      rw [hsupport _ (by simpa only [spatialStar_unstar] using hx), Complex.ofReal_zero])
    (fun i => ((spatialStar v i : ℤ) : ℝ) / H) hv
  rw [hzero, mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem intervalTensorApprox_norm_le {S : Type*} [Fintype S] [DecidableEq S]
    {B r C : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ C) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖intervalTensorApprox B r F x‖ ≤ C := by
  unfold intervalTensorApprox
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x * C := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (intervalTensorWeight_nonneg B hr k x)]
      exact mul_le_mul_of_nonneg_left (hF _) (intervalTensorWeight_nonneg B hr k x)
    _ = C := by rw [← Finset.sum_mul, intervalTensorWeight_sum hB hr x hx, one_mul]

theorem maskedIntegerImageDensity_abs_le {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    {G C : ℝ} (hC : 0 ≤ C)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ y, |f y| ≤ C) (v : I → ℤ) :
    |maskedIntegerImageDensity A B P f v| ≤ G * C := by
  unfold maskedIntegerImageDensity
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul hindex (hf _) (abs_nonneg _) ((Nat.cast_nonneg _).trans hindex)
  · simpa using mul_nonneg ((Nat.cast_nonneg _).trans hindex) hC

theorem spatialSiteApprox_norm_le {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H : ℝ)
    {b r G C : ℝ} (hb : 0 < b) (hr : 0 < r)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ y, |f y| ≤ C) (v : (Unit ⊕ I) → ℤ)
    (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖spatialSiteApprox A B m f H b r v‖ ≤ G * C := by
  rw [spatialSiteApprox, maskedIntervalApprox_eq, norm_mul]
  exact mul_le_mul (latticeStarMask_bound _ _ hindex _)
    (intervalTensorApprox_norm_le hb hr _ (spatialStarDensity_bound f hf) _ hv)
    (norm_nonneg _) ((Nat.cast_nonneg _).trans hindex)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_weighted_complex_mean_sub_le {V : Type*} (t : Finset V)
    (D : V → ℝ) (a b φ : V → ℂ) {ε : ℝ}
    (hD : ∀ v ∈ t, 0 ≤ D v) (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (he : ∀ v ∈ t, ‖a v - b v‖ ≤ ε) :
    ‖(𝔼 v ∈ t, (D v : ℂ) * a v * φ v) - (𝔼 v ∈ t, (D v : ℂ) * b v * φ v)‖ ≤
      ε * (𝔼 v ∈ t, D v) := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  calc
    _ ≤ 𝔼 v ∈ t, ε * D v := by
      apply Finset.expect_le_expect
      intro v hv
      have hid : (D v : ℂ) * a v * φ v - (D v : ℂ) * b v * φ v =
          (D v : ℂ) * (a v - b v) * φ v := by ring
      rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD v hv)]
      calc
        _ ≤ D v * ‖a v - b v‖ * 1 :=
          mul_le_mul_of_nonneg_left (hφ v hv) (mul_nonneg (hD v hv) (norm_nonneg _))
        _ ≤ ε * D v := by rw [mul_one, mul_comm ε]; exact mul_le_mul_of_nonneg_left (he v hv) (hD v hv)
    _ = _ := (Finset.mul_expect _ _ _).symm

theorem norm_site_family_replacement {R V : Type*} [Fintype R] (t : Finset V)
    (D : R → V → ℝ) (a b : R → V → ℂ) (φ : V → ℂ) {ε : ℝ}
    (hD : ∀ r v, v ∈ t → 0 ≤ D r v) (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (he : ∀ r v, v ∈ t → ‖a r v - b r v‖ ≤ ε) :
    ‖(∑ r, 𝔼 v ∈ t, (D r v : ℂ) * a r v * φ v) -
      (∑ r, 𝔼 v ∈ t, (D r v : ℂ) * b r v * φ v)‖ ≤
      ε * (∑ r, 𝔼 v ∈ t, D r v) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, ε * (𝔼 v ∈ t, D r v) := Finset.sum_le_sum (fun r _ =>
      norm_weighted_complex_mean_sub_le t (D r) (a r) (b r) φ (hD r) hφ (he r))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem norm_fiber_site_replacement {X R V : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R) (t : Finset V)
    (D : X → V → ℝ) (a b : R → V → ℂ) (φ : V → ℂ) {ε : ℝ}
    (hD : ∀ x v, 0 ≤ D x v) (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (he : ∀ r v, v ∈ t → ‖a r v - b r v‖ ≤ ε) :
    ‖(∑ r, 𝔼 v ∈ t, (p.fiberMean F r (fun x => D x v) : ℂ) * a r v * φ v) -
      (∑ r, 𝔼 v ∈ t, (p.fiberMean F r (fun x => D x v) : ℂ) * b r v * φ v)‖ ≤
      ε * p.mean (fun x => 𝔼 v ∈ t, D x v) := by
  have hmass : (∑ r, 𝔼 v ∈ t, p.fiberMean F r (fun x => D x v)) =
      p.mean (fun x => 𝔼 v ∈ t, D x v) := by
    rw [← Finset.expect_sum_comm]
    simp_rw [p.sum_fiberMean]
    unfold FiniteProbabilityWeights.mean
    simp_rw [Finset.mul_expect]
    exact Finset.expect_sum_comm _ _ _
  have h := norm_site_family_replacement t (fun r v => p.fiberMean F r (fun x => D x v))
    a b φ (fun r v _ => p.fiberMean_nonneg F r _ (fun x => hD x v)) hφ he
  rwa [hmass] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev SpatialSiteLabel (I : Type*) (m : ℕ) (b r : ℝ) :=
  ((Unit ⊕ I) → ZMod m) × ((Unit ⊕ I) → Fin (intervalSiteCount b r))

noncomputable def spatialSiteCoefficient {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) (t : SpatialSiteLabel I m b r) : ℂ :=
  latticeStarMask (pivotFullImage A B) m t.1 *
    spatialStarDensity f (fun i => intervalSiteCenter b r (t.2 i))

theorem spatialSiteApprox_sum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r : ℝ) (v : (Unit ⊕ I) → ℤ) :
    spatialSiteApprox A B m f H b r v =
      ∑ t : SpatialSiteLabel I m b r, spatialSiteCoefficient A B m f b r t *
        ∏ i, (residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) : ℂ) := by
  simp only [spatialSiteApprox, maskedIntervalApprox, Fintype.sum_prod_type,
    spatialSiteCoefficient, Complex.ofReal_prod]

theorem spatialSiteCoefficient_sum_bound {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) {G C : ℝ}
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G) (hf : ∀ y, |f y| ≤ C) :
    (∑ t : SpatialSiteLabel I m b r, ‖spatialSiteCoefficient A B m f b r t‖) ≤
      (m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ I) * (G*C) := by
  simpa only [Fintype.sum_prod_type, spatialSiteCoefficient] using
    spatialSiteApprox_coefficient_sum A B m f b r hindex hf

theorem vectorSpatialSiteExpansion {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : D → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (H : D → ℝ)
    (b r : ℝ) (v : D → (Unit ⊕ I) → ℤ) :
    (∏ d, spatialSiteApprox A (B d) m (f d) (H d) b r (v d)) =
      ∑ t : D → SpatialSiteLabel I m b r,
        (∏ d, spatialSiteCoefficient A (B d) m (f d) b r (t d)) *
          ∏ i, vectorResidueSiteWeight b r H (fun d => (t d).1 i) (fun d => (t d).2 i)
            (fun d => spatialStar (v d) i) := by
  simp_rw [spatialSiteApprox_sum]
  exact siteFactorTensor_identity _ _ _

theorem vectorSpatialSiteCoefficient_sum_bound {D I J : Type*}
    [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : D → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m] (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (b r : ℝ) {G C : ℝ}
    (hindex : ∀ d, ((pivotFullImage A (B d)).toAddSubgroup.index : ℝ) ≤ G)
    (hf : ∀ d y, |f d y| ≤ C) :
    (∑ t : D → SpatialSiteLabel I m b r,
      ‖∏ d, spatialSiteCoefficient A (B d) m (f d) b r (t d)‖) ≤
      ((m : ℝ)^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r : ℝ)^Fintype.card (Unit ⊕ I) *
        (G*C))^Fintype.card D := by
  have h := siteFactorTensor_coefficient_bound
    (fun d => spatialSiteCoefficient A (B d) m (f d) b r) _
    (fun d => spatialSiteCoefficient_sum_bound A (B d) m (f d) b r (hindex d) (hf d))
  simpa only [Finset.prod_const, Finset.card_univ] using h

theorem vectorSpatialSiteLabel_card {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
    (m : ℕ) [NeZero m] (b r : ℝ) :
    Fintype.card (D → SpatialSiteLabel I m b r) =
      (m^Fintype.card (Unit ⊕ I) * (intervalSiteCount b r)^Fintype.card (Unit ⊕ I))^Fintype.card D := by
  classical
  simp only [SpatialSiteLabel, Fintype.card_fun, Fintype.card_prod, ZMod.card, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialSiteTerm_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r a : ℝ) (hr : 0 < r)
    (hsupport : ∀ v, (∃ i, a < |spatialStar v i|) → f v = 0)
    (t : SpatialSiteLabel I m b r) (v : (Unit ⊕ I) → ℤ)
    (hv : ∃ i, a + 2 * r < |((spatialStar v i : ℤ) : ℝ) / H|) :
    spatialSiteCoefficient A B m f b r t *
      (∏ i, (residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) : ℂ)) = 0 := by
  by_cases hc : spatialSiteCoefficient A B m f b r t = 0
  · rw [hc, zero_mul]
  by_cases hw : (∏ i, (residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) : ℂ)) = 0
  · rw [hw, mul_zero]
  obtain ⟨i, hi⟩ := hv
  have hwi := (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  have hreal : residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) ≠ 0 := by
    exact_mod_cast hwi
  have hweight : intervalSiteWeight b r (t.2 i) ((spatialStar v i : ℤ) / H) ≠ 0 :=
    (mul_ne_zero_iff.mp hreal).2
  have hnear := intervalSiteWeight_near b r (t.2 i) ((spatialStar v i : ℤ) / H)
    (lt_of_le_of_ne (intervalSiteWeight_range b hr _ _).1 hweight.symm)
  have hcenter : a < |intervalSiteCenter b r (t.2 i)| := by
    rw [Real.dist_eq] at hnear
    have ht := abs_add_le (((spatialStar v i : ℤ) : ℝ) / H - intervalSiteCenter b r (t.2 i))
      (intervalSiteCenter b r (t.2 i))
    rw [sub_add_cancel] at ht
    linarith only [hi, hnear, ht]
  have hz : spatialStarDensity f (fun j => intervalSiteCenter b r (t.2 j)) = 0 := by
    unfold spatialStarDensity
    rw [hsupport _ (by simpa only [spatialStar_unstar] using (show ∃ j, a < |intervalSiteCenter b r (t.2 j)| from ⟨i, hcenter⟩))]
    rfl
  exact (hc (by simp only [spatialSiteCoefficient, hz, mul_zero])).elim

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem vectorSpatialSiteApprox_error {D I J : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : D → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : ∀ d, integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A (B d))
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ d, LipschitzWith K (f d))
    (H : D → ℝ) (mass : D → ((Unit ⊕ I) → ℤ) → ℝ)
    {G C E b r : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) (hE : 0 ≤ E) (hb : 0 < b) (hr : 0 < r)
    (hi : ∀ d, ((pivotFullImage A (B d)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ d y, |f d y| ≤ C)
    (hmass : ∀ d v, |mass d v - maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) v| ≤ E)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    ‖((∏ d, mass d (v d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox A (B d) m (f d) (H d) b r (v d)‖ ≤
      Fintype.card D * (E + 4*G*K*r) * (1 + G*C + E)^Fintype.card D := by
  have hGC := mul_nonneg hG hC
  have hcapmass (d : D) : ‖(mass d (v d) : ℂ)‖ ≤ 1 + G*C + E := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hw := maskedIntegerImageDensity_abs_le A (B d) (fun _ => H d) (f d) hC (hi d) (hcap d) (v d)
    have ht := abs_add_le
      (mass d (v d) - maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) (v d))
      (maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) (v d))
    rw [sub_add_cancel] at ht
    linarith [hmass d (v d)]
  have hdiff (d : D) : ‖(mass d (v d) : ℂ) -
      spatialSiteApprox A (B d) m (f d) (H d) b r (v d)‖ ≤ E + 4*G*K*r := by
    have h₁ : ‖(mass d (v d) : ℂ) -
        (maskedIntegerImageDensity A (B d) (fun _ => H d) (f d) (v d) : ℂ)‖ ≤ E := by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hmass d (v d)
    have h₂ := spatialSiteApprox_error A (B d) m (hp d) (f d) (hf d) (hi d) hb hr (H d) (v d) (hv d)
    apply le_trans _ (add_le_add h₁ h₂)
    simp only [← dist_eq_norm]
    exact dist_triangle _ _ _
  have h := norm_finset_prod_sub_prod_le Finset.univ
    (fun d => (mass d (v d) : ℂ))
    (fun d => spatialSiteApprox A (B d) m (f d) (H d) b r (v d))
    (show 1 ≤ 1 + G*C + E by linarith) (show 0 ≤ E + 4*G*K*r by positivity)
    (fun d _ => hcapmass d)
    (fun d _ => (spatialSiteApprox_norm_le A (B d) m (f d) (H d) hb hr
      (hi d) (hcap d) (v d) (hv d)).trans (by linarith)) (fun d _ => hdiff d)
  simpa only [Complex.ofReal_prod, Finset.card_univ] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem spatialSiteApprox_remesh {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (H : ℝ) {G b r r' : ℝ}
    (hi : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hb : 0 < b) (hr : 0 < r) (hr' : 0 < r')
    (v : (Unit ⊕ I) → ℤ) (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b) :
    ‖spatialSiteApprox A B m f H b r v - spatialSiteApprox A B m f H b r' v‖ ≤
      4 * G * K * (r + r') := by
  have he := spatialSiteApprox_error A B m hp f hf hi hb hr H v hv
  have he' := spatialSiteApprox_error A B m hp f hf hi hb hr' H v hv
  calc
    _ ≤ ‖spatialSiteApprox A B m f H b r v -
          (maskedIntegerImageDensity A B (fun _ => H) f v : ℂ)‖ +
        ‖(maskedIntegerImageDensity A B (fun _ => H) f v : ℂ) -
          spatialSiteApprox A B m f H b r' v‖ := by
      simp only [← dist_eq_norm]
      exact dist_triangle _ _ _
    _ ≤ 4 * G * K * r + 4 * G * K * r' := by
      rw [norm_sub_rev (spatialSiteApprox A B m f H b r v)]
      exact add_le_add he he'
    _ = _ := by ring

theorem vectorSpatialSiteApprox_remesh {X I J : Type*}
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : X → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : ∀ x, integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A (B x))
    (f : X → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ x, LipschitzWith K (f x))
    (H : X → ℝ) {G C b r r' : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hi : ∀ x, ((pivotFullImage A (B x)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ x y, |f x y| ≤ C) (hb : 0 < b) (hr : 0 < r) (hr' : 0 < r')
    (v : X → (Unit ⊕ I) → ℤ)
    (hv : ∀ x i, |((spatialStar (v x) i : ℤ) : ℝ) / H x| ≤ b) :
    ‖(∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)) -
      ∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r' (v x)‖ ≤
      Fintype.card X * (4 * G * K * (r + r')) * (1 + G * C)^Fintype.card X := by
  have hGC := mul_nonneg hG hC
  have h := norm_finset_prod_sub_prod_le Finset.univ
    (fun x => spatialSiteApprox A (B x) m (f x) (H x) b r (v x))
    (fun x => spatialSiteApprox A (B x) m (f x) (H x) b r' (v x))
    (show 1 ≤ 1 + G * C by linarith)
    (show 0 ≤ 4 * G * K * (r + r') by positivity)
    (fun x _ => (spatialSiteApprox_norm_le A (B x) m (f x) (H x) hb hr
      (hi x) (hcap x) (v x) (hv x)).trans (by linarith))
    (fun x _ => (spatialSiteApprox_norm_le A (B x) m (f x) (H x) hb hr'
      (hi x) (hcap x) (v x) (hv x)).trans (by linarith))
    (fun x _ => spatialSiteApprox_remesh A (B x) m (hp x) (f x) (hf x) (H x)
      (hi x) hb hr hr' (v x) (hv x))
  simpa only [Finset.card_univ] using h

theorem weightedSpatialSiteApprox_remesh {X I J : Type*}
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : X → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : ∀ x, integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A (B x))
    (f : X → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ x, LipschitzWith K (f x))
    (H : X → ℝ) {G C b r r' : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hi : ∀ x, ((pivotFullImage A (B x)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ x y, |f x y| ≤ C) (hb : 0 < b) (hr : 0 < r) (hr' : 0 < r')
    (window : Finset (X → (Unit ⊕ I) → ℤ))
    (weight : (X → (Unit ⊕ I) → ℤ) → ℝ)
    (test : (X → (Unit ⊕ I) → ℤ) → ℂ)
    (hweight : ∀ v ∈ window, 0 ≤ weight v) (htest : ∀ v ∈ window, ‖test v‖ ≤ 1)
    (hwindow : ∀ v ∈ window, ∀ x i, |((spatialStar (v x) i : ℤ) : ℝ) / H x| ≤ b) :
    ‖(𝔼 v ∈ window, (weight v : ℂ) *
        (∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)) * test v) -
      (𝔼 v ∈ window, (weight v : ℂ) *
        (∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r' (v x)) * test v)‖ ≤
      (Fintype.card X * (4 * G * K * (r + r')) * (1 + G * C)^Fintype.card X) *
        (𝔼 v ∈ window, weight v) := by
  apply norm_weighted_complex_mean_sub_le window weight _ _ test hweight htest
  intro v hv
  exact vectorSpatialSiteApprox_remesh A B m hp f hf H hG hC hi hcap hb hr hr' v (hwindow v hv)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem spatialSiteApprox_shift {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (H : ℝ) {G b r ε : ℝ}
    (hi : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hb : 0 < b) (hr : 0 < r)
    (v s : (Unit ⊕ I) → ℤ) (hs : s ∈ pivotFullImage A B)
    (hsize : ‖fun i => (s i : ℝ) / H‖ ≤ ε)
    (hv : ∀ i, |((spatialStar v i : ℤ) : ℝ) / H| ≤ b)
    (hvs : ∀ i, |((spatialStar (v + s) i : ℤ) : ℝ) / H| ≤ b) :
    ‖spatialSiteApprox A B m f H b r (v + s) - spatialSiteApprox A B m f H b r v‖ ≤
      G * K * (8 * r + ε) := by
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hi
  have hleft := spatialSiteApprox_error A B m hp f hf hi hb hr H (v + s) hvs
  have hright := spatialSiteApprox_error A B m hp f hf hi hb hr H v hv
  have hmove := (maskedIntegerImageDensity_shift_error A B (fun _ => H) f hf s hs hi v).trans
    (mul_le_mul_of_nonneg_left hsize (mul_nonneg hG K.coe_nonneg))
  let density := fun w => (maskedIntegerImageDensity A B (fun _ => H) f w : ℂ)
  have hmiddle : ‖density (v + s) - density v‖ ≤ G * K * ε := by
    simpa only [density, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hmove
  calc
    _ ≤ ‖spatialSiteApprox A B m f H b r (v + s) - density (v + s)‖ +
        ‖density (v + s) - spatialSiteApprox A B m f H b r v‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * G * K * r + (G * K * ε + 4 * G * K * r) := by
      apply add_le_add
      · rw [norm_sub_rev]
        exact hleft
      · exact (norm_sub_le_norm_sub_add_norm_sub _ (density v) _).trans
          (add_le_add hmiddle hright)
    _ = _ := by ring

theorem vectorSpatialSiteApprox_shift {X I J : Type*}
    [Fintype X] [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : X → Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : ∀ x, integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A (B x))
    (f : X → ((Unit ⊕ I) → ℝ) → ℝ) {K : ℝ≥0} (hf : ∀ x, LipschitzWith K (f x))
    (H : X → ℝ) {G C b r ε : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hi : ∀ x, ((pivotFullImage A (B x)).toAddSubgroup.index : ℝ) ≤ G)
    (hcap : ∀ x y, |f x y| ≤ C) (hb : 0 < b) (hr : 0 < r)
    (v s : X → (Unit ⊕ I) → ℤ)
    (hs : ∀ x, s x ∈ pivotFullImage A (B x))
    (hsize : ∀ x, ‖fun i => (s x i : ℝ) / H x‖ ≤ ε)
    (hv : ∀ x i, |((spatialStar (v x) i : ℤ) : ℝ) / H x| ≤ b)
    (hvs : ∀ x i, |((spatialStar (v x + s x) i : ℤ) : ℝ) / H x| ≤ b) :
    ‖(∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x + s x)) -
      ∏ x, spatialSiteApprox A (B x) m (f x) (H x) b r (v x)‖ ≤
      Fintype.card X * (G * K * (8 * r + ε)) * (1 + G * C)^Fintype.card X := by
  have hGC := mul_nonneg hG hC
  have h := norm_finset_prod_sub_prod_le Finset.univ
    (fun x => spatialSiteApprox A (B x) m (f x) (H x) b r (v x + s x))
    (fun x => spatialSiteApprox A (B x) m (f x) (H x) b r (v x))
    (show 1 ≤ 1 + G * C by linarith)
    (show 0 ≤ G * K * (8 * r + ε) by positivity)
    (fun x _ => (spatialSiteApprox_norm_le A (B x) m (f x) (H x) hb hr
      (hi x) (hcap x) (v x + s x) (hvs x)).trans (by linarith))
    (fun x _ => (spatialSiteApprox_norm_le A (B x) m (f x) (H x) hb hr
      (hi x) (hcap x) (v x) (hv x)).trans (by linarith))
    (fun x _ => spatialSiteApprox_shift A (B x) m (hp x) (f x) (hf x) (H x)
      (hi x) hb hr (v x) (s x) (hs x) (hsize x) (hv x) (hvs x))
  simpa only [Finset.card_univ] using h

end Erdos3

end

end OAI
