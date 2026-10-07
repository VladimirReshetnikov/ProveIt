import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem tiny_product_quarter_le {u v kappa : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    (hsmall : u ≤ kappa ∨ v ≤ kappa) :
    u * v ≤ kappa ^ (3 / 4 : ℝ) * (u * v) ^ (1 / 4 : ℝ) := by
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have huvK : u * v ≤ kappa := by
    rcases hsmall with hsmall | hsmall
    · calc
        u * v ≤ u := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hu
        _ ≤ kappa := hsmall
    · calc
        u * v ≤ v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu1 hv
        _ ≤ kappa := hsmall
  by_cases hzero : u * v = 0
  · simp only [hzero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero, le_refl]
  have hpos : 0 < u * v := lt_of_le_of_ne huv (Ne.symm hzero)
  calc
    _ = (u * v) ^ (3 / 4 : ℝ) * (u * v) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hpos]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow huv huvK (by norm_num)) (Real.rpow_nonneg huv _)

variable {G : Type*} [AddCommGroup G]

theorem tiny_cell_integral_le (B : Finset G) (hB : B.Nonempty) (a f g : G → ℝ) (origin : G)
    {M kappa : ℝ} (hM : 0 ≤ M) (ha : ∀ r, a r ≤ M)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (htiny : min (𝔼 r ∈ B, f r) (𝔼 r ∈ B, g r) < kappa) :
    bilinearIntegral B B (fun r => a (origin + r)) f g ≤
      (M * kappa ^ (3 / 4 : ℝ)) * ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  have hu : 0 ≤ 𝔼 r ∈ B, f r := Finset.expect_nonneg (fun r _ => (hf r).1)
  have hv : 0 ≤ 𝔼 r ∈ B, g r := Finset.expect_nonneg (fun r _ => (hg r).1)
  have hu1 : (𝔼 r ∈ B, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ B) => (hf r).2)).trans_eq (Finset.expect_const hB 1)
  have hv1 : (𝔼 r ∈ B, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ B) => (hg r).2)).trans_eq (Finset.expect_const hB 1)
  have hprod := tiny_product_quarter_le hu hv hu1 hv1 ((min_lt_iff.mp htiny).imp le_of_lt le_of_lt)
  have h := bilinearIntegral_le B B (fun r => a (origin + r)) f g
    (fun r => ha (origin + r)) (fun r => (hf r).1) (fun r => (hg r).1)
  have hscaled := mul_le_mul_of_nonneg_left hprod hM
  nlinarith only [h, hscaled]

omit [AddCommGroup G] in
theorem quarter_cell_potential_mono (B : Finset G) (f f' g g' : G → ℝ)
    (hf' : ∀ r, 0 ≤ f' r) (hg' : ∀ r, 0 ≤ g' r)
    (hff' : ∀ r, f' r ≤ f r) (hgg' : ∀ r, g' r ≤ g r) :
    ((𝔼 r ∈ B, f' r) * (𝔼 r ∈ B, g' r)) ^ (1 / 4 : ℝ) ≤
      ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  have hF := Finset.expect_nonneg (s := B) (fun r _ => hf' r)
  have hG := Finset.expect_nonneg (s := B) (fun r _ => hg' r)
  have hFl := Finset.expect_le_expect (s := B) (fun r _ => hff' r)
  have hGl := Finset.expect_le_expect (s := B) (fun r _ => hgg' r)
  exact Real.rpow_le_rpow (mul_nonneg hF hG) (mul_le_mul hFl hGl hG (hF.trans hFl)) (by norm_num)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem cutoff_sq_le_quarter_potential {u v cutoff : ℝ}
    (hcutoff : 0 ≤ cutoff) (hu : cutoff ≤ u) (hv : cutoff ≤ v)
    (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    cutoff ^ 2 ≤ (u * v) ^ (1 / 4 : ℝ) := by
  have hu0 : 0 ≤ u := hcutoff.trans hu
  have hv0 : 0 ≤ v := hcutoff.trans hv
  have hprod : u * v ≤ 1 := by nlinarith
  calc
    cutoff ^ 2 ≤ u * v := by
      simpa only [pow_two] using mul_le_mul hu hv hcutoff hu0
    _ ≤ _ := Real.self_le_rpow_of_le_one (mul_nonneg hu0 hv0) hprod (by norm_num)

theorem refinement_error_le_potential {u v cutoff K error loss : ℝ}
    (hcutoff : 0 < cutoff) (hK : 0 < K) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (hu : cutoff ≤ u) (hv : cutoff ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    error + loss * ((u + v) / (K * cutoff)) ≤
      (error / cutoff ^ 2 + 2 * loss / (K * cutoff ^ 3)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hpotential := cutoff_sq_le_quarter_potential hcutoff.le hu hv hu1 hv1
  have he : error ≤ error / cutoff ^ 2 * (u * v) ^ (1 / 4 : ℝ) := by
    calc
      error = error / cutoff ^ 2 * cutoff ^ 2 := by
        exact (div_mul_cancel₀ error (pow_ne_zero 2 hcutoff.ne')).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hpotential (div_nonneg herror (sq_nonneg cutoff))
  have hl : loss * ((u + v) / (K * cutoff)) ≤
      (2 * loss / (K * cutoff ^ 3)) * (u * v) ^ (1 / 4 : ℝ) := by
    calc
      loss * ((u + v) / (K * cutoff)) ≤ loss * (2 / (K * cutoff)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith)
          (mul_pos hK hcutoff).le) hloss
      _ = (2 * loss / (K * cutoff ^ 3)) * cutoff ^ 2 := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpotential (by positivity)
  nlinarith only [he, hl]

variable {G : Type*} [AddCommGroup G]

theorem cellBilinearBound_of_refinement
    (C : Finset G) (hC : C.Nonempty) (a : G → ℝ)
    {W cutoff K T epsilon error loss : ℝ}
    (hW : 0 ≤ W) (ha : ∀ r, a r ≤ W) (hcutoff : 0 < cutoff) (hK : 0 < K)
    (hT : 0 ≤ T) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ epsilon)
    (hstep : ∀ origin : G, ∀ f g : G → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      (∀ r, r ∉ C → f r = 0) → (∀ r, r ∉ C → g r = 0) →
      cutoff ≤ (𝔼 r ∈ C, f r) → cutoff ≤ (𝔼 r ∈ C, g r) →
      bilinearIntegral C C (fun r => a (origin + r)) f g ≤
        (T + epsilon) * ((𝔼 r ∈ C, f r) * (𝔼 r ∈ C, g r)) ^ (1 / 4 : ℝ) + error +
          loss * (((𝔼 r ∈ C, f r) + 𝔼 r ∈ C, g r) / (K * cutoff))) :
    CellBilinearBound C a
      (T + epsilon + error / cutoff ^ 2 + 2 * loss / (K * cutoff ^ 3)) := by
  intro origin f g hf hg hfs hgs
  have hu1 : (𝔼 r ∈ C, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ C) => (hf r).2)).trans_eq (Finset.expect_const hC 1)
  have hv1 : (𝔼 r ∈ C, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ C) => (hg r).2)).trans_eq (Finset.expect_const hC 1)
  have hPhi : 0 ≤ ((𝔼 r ∈ C, f r) * (𝔼 r ∈ C, g r)) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun r _ => (hf r).1))
      (Finset.expect_nonneg (fun r _ => (hg r).1))) _
  by_cases hsmall : min (𝔼 r ∈ C, f r) (𝔼 r ∈ C, g r) < cutoff
  · have h := tiny_cell_integral_le C hC a f g origin hW ha hf hg hsmall
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hPhi
    have he : 0 ≤ error / cutoff ^ 2 := by positivity
    have hl : 0 ≤ 2 * loss / (K * cutoff ^ 3) := by positivity
    linarith
  · obtain ⟨hu, hv⟩ := le_min_iff.mp (le_of_not_gt hsmall)
    have h := hstep origin f g hf hg hfs hgs hu hv
    have he := refinement_error_le_potential hcutoff hK herror hloss hu hv hu1 hv1
    nlinarith only [h, he]

end Erdos3.CellRefinement

end

end OAI
