/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Lattices.ResidueIntervalFactors

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def vectorIntervalSiteWeight {D : Type*} [Fintype D] (b r : ℝ)
    (k : D → Fin (intervalSiteCount b r)) (x : D → ℝ) : ℂ :=
  ∏ d, (intervalSiteWeight b r (k d) (x d) : ℂ)

theorem vectorIntervalSiteWeight_bound {D : Type*} [Fintype D] (b : ℝ)
    {r : ℝ} (hr : 0 < r) (k : D → Fin (intervalSiteCount b r)) (x : D → ℝ) :
    ‖vectorIntervalSiteWeight b r k x‖ ≤ 1 := by
  unfold vectorIntervalSiteWeight
  apply siteFactorTensor_factor_bound (fun d y => (intervalSiteWeight b r (k d) y : ℂ))
  intro d y
  rw [Complex.norm_real, Real.norm_of_nonneg (intervalSiteWeight_range b hr _ _).1]
  exact (intervalSiteWeight_range b hr _ _).2

theorem vectorIntervalSiteWeight_lipschitz {D : Type*} [Fintype D] (b : ℝ)
    {r : ℝ≥0} (hr : 0 < r) (k : D → Fin (intervalSiteCount b r)) :
    LipschitzWith (Fintype.card D * ((2 * intervalSiteCount b r + 1) / r))
      (vectorIntervalSiteWeight b r k) := by
  unfold vectorIntervalSiteWeight
  apply siteFactorTensor_factor_lipschitz (fun d y => (intervalSiteWeight b r (k d) y : ℂ))
  · intro d
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (intervalSiteWeight_lipschitz b hr (k d))
  · intro d y
    have hw := intervalSiteWeight_range b (show (0 : ℝ) < r from hr) (k d) y
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2

noncomputable def vectorResidueSiteWeight {D : Type*} [Fintype D] (b r : ℝ) (H : D → ℝ)
    {m : ℕ} (a : D → ZMod m) (k : D → Fin (intervalSiteCount b r)) (u : D → ℤ) : ℂ :=
  ∏ d, (residueIntervalSiteWeight b r (H d) (a d) (k d) (u d) : ℂ)

theorem vectorResidueSiteWeight_eq {D : Type*} [Fintype D] (b r : ℝ) (H : D → ℝ)
    {m : ℕ} (a : D → ZMod m) (k : D → Fin (intervalSiteCount b r)) (u : D → ℤ) :
    vectorResidueSiteWeight b r H a k u =
      (if (fun d => (u d : ZMod m)) = a then 1 else 0) *
        vectorIntervalSiteWeight b r k (fun d => (u d : ℝ) / H d) := by
  unfold vectorResidueSiteWeight vectorIntervalSiteWeight residueIntervalSiteWeight
  simp only [Complex.ofReal_mul, Finset.prod_mul_distrib, ← Complex.ofReal_prod,
    prod_residueSiteIndicator]
  split_ifs <;> simp

theorem vectorResidueSiteWeight_bound {D : Type*} [Fintype D] (b : ℝ) {r : ℝ}
    (hr : 0 < r) (H : D → ℝ) {m : ℕ} (a : D → ZMod m)
    (k : D → Fin (intervalSiteCount b r)) (u : D → ℤ) :
    ‖vectorResidueSiteWeight b r H a k u‖ ≤ 1 := by
  rw [vectorResidueSiteWeight_eq]
  split_ifs
  · simpa using vectorIntervalSiteWeight_bound b hr k _
  · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

noncomputable def groupedSiteCoefficient (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    (k : S × D → Fin (intervalSiteCount B r)) : ℂ :=
  F (fun s d => intervalSiteCenter B r (k (s, d)))

noncomputable def groupedSiteFactor (B r : ℝ)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) : ℂ :=
  vectorIntervalSiteWeight B r (fun d => k (s, d)) x

noncomputable def groupedSiteApprox [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    (x : S → D → ℝ) : ℂ :=
  ∑ k : S × D → Fin (intervalSiteCount B r),
    groupedSiteCoefficient B r F k * ∏ s, groupedSiteFactor B r k s (x s)

theorem siteCurry_lipschitz :
    LipschitzWith 1 (fun x : S × D → ℝ => fun s d => x (s, d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro s
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  exact dist_le_pi_dist x y (s, d)

theorem groupedSiteApprox_eq_interval [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ) (x : S → D → ℝ) :
    groupedSiteApprox B r F x =
      intervalTensorApprox B r (fun y : S × D → ℝ => F (fun s d => y (s, d)))
        (fun p => x p.1 p.2) := by
  unfold groupedSiteApprox intervalTensorApprox groupedSiteCoefficient
  apply Finset.sum_congr rfl
  intro k _
  simp only [groupedSiteFactor, vectorIntervalSiteWeight, intervalTensorWeight,
    Complex.ofReal_prod, Fintype.prod_prod_type]
  ring

theorem groupedSiteApprox_error [DecidableEq S] [DecidableEq D]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → D → ℝ) → ℂ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (x : S → D → ℝ)
    (hx : ∀ s d, |x s d| ≤ B) :
    ‖F x-groupedSiteApprox B r F x‖ ≤ 2*K*r := by
  rw [groupedSiteApprox_eq_interval]
  exact intervalTensorApprox_error hB hr _
    (by simpa only [mul_one] using hF.comp (siteCurry_lipschitz (S := S) (D := D)))
    (fun p : S × D => x p.1 p.2) (fun p : S × D => hx p.1 p.2)

theorem groupedSiteCoefficient_sum [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S × D → Fin (intervalSiteCount B r), ‖groupedSiteCoefficient B r F k‖) ≤
      (intervalSiteCount B r : ℝ)^(Fintype.card S*Fintype.card D)*A := by
  calc
    _ ≤ ∑ _k : S × D → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp [Fintype.card_prod]

omit [Fintype S] in
theorem groupedSiteFactor_bound (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) :
    ‖groupedSiteFactor B r k s x‖ ≤ 1 :=
  vectorIntervalSiteWeight_bound B hr _ _

omit [Fintype S] in
theorem groupedSiteFactor_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) :
    LipschitzWith (Fintype.card D*((2*intervalSiteCount B r+1)/r))
      (groupedSiteFactor B r k s) :=
  vectorIntervalSiteWeight_lipschitz B hr _

end Erdos3

end

end OAI
