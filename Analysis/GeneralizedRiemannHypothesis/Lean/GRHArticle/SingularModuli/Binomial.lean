import GRHArticle.SingularModuli.Support
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Binomial annihilators and the degree-two support criterion

A nonzero binomial root has a positive power in the coefficient field.
All of its conjugate values therefore have the same complex modulus, as
used in the quadratic case of `smd:prop:small`.
-/

namespace GRHArticle.SingularModuli

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An element admits a binomial annihilator precisely when some positive
power belongs to the image of its coefficient field. -/
theorem hasSparseAnnihilator_two_iff (x : L) :
    HasSparseAnnihilator K x 2 ↔ ∃ d : ℕ, 0 < d ∧ x ^ d ∈ (algebraMap K L).range := by
  constructor
  · rintro ⟨P, hP, hsize, hzero⟩
    by_cases h1 : P.support.card ≤ 1
    · have hx := (hasSparseAnnihilator_one_iff (K := K) x).mp ⟨P, hP, h1, hzero⟩
      exact ⟨1, by decide, 0, by simp [hx]⟩
    by_cases hx : x = 0
    · exact ⟨1, by decide, 0, by simp [hx]⟩
    obtain ⟨k, m, hkm, a, b, _, hb, rfl⟩ := card_support_eq_two.mp (show P.support.card = 2 by omega)
    simp only [map_add, map_mul, aeval_C, map_pow, aeval_X] at hzero
    have hsplit : x ^ m = x ^ k * x ^ (m - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkm.le]
    rw [hsplit] at hzero
    have hrel : algebraMap K L a + algebraMap K L b * x ^ (m - k) = 0 :=
      (mul_eq_zero.mp (show x ^ k * (algebraMap K L a + algebraMap K L b * x ^ (m - k)) = 0 by
        linear_combination hzero)).resolve_left (pow_ne_zero _ hx)
    refine ⟨m - k, by omega, -a / b, ?_⟩
    rw [map_div₀, map_neg, div_eq_iff ((_root_.map_ne_zero (algebraMap K L)).mpr hb)]
    linear_combination -hrel
  · rintro ⟨d, hd, a, ha⟩
    refine ⟨X ^ d - C a, (monic_X_pow_sub_C _ hd.ne').ne_zero, ?_, by simp [ha]⟩
    have hs := Finset.card_le_card (support_binomial_subset d 0 (1 : K) (-a))
    simpa [sub_eq_add_neg, hd.ne'] using hs

/-- Distinct moduli of two conjugate images rule out a binomial equation. -/
theorem not_hasSparseAnnihilator_two_of_norm_ne [Algebra K ℂ]
    (σ τ : L →ₐ[K] ℂ) (x : L) (hne : ‖σ x‖ ≠ ‖τ x‖) : ¬ HasSparseAnnihilator K x 2 := by
  rintro h
  obtain ⟨d, hd, a, ha⟩ := (hasSparseAnnihilator_two_iff x).mp h
  have he : σ x ^ d = τ x ^ d := by
    calc
      _ = σ (x ^ d) := (map_pow _ _ _).symm
      _ = algebraMap K ℂ a := by rw [← ha, AlgHom.commutes]
      _ = τ (x ^ d) := by rw [← ha, AlgHom.commutes]
      _ = _ := map_pow _ _ _
  exact hne ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').mp
    (by simpa only [norm_pow] using congrArg norm he))

theorem minimumSupport_eq_three_of_quadratic_norm_ne [Algebra K ℂ]
    (σ τ : L →ₐ[K] ℂ) {x : L} (hx : IsIntegral K x) (hdegree : (minpoly K x).natDegree = 2)
    (hne : ‖σ x‖ ≠ ‖τ x‖) : minimumSupport hx = 3 := by
  have upper := minimumSupport_le_natDegree_add_one hx
  rw [hdegree] at upper
  have lower := not_hasSparseAnnihilator_two_of_norm_ne σ τ x hne
  rw [← minimumSupport_le_iff hx] at lower
  omega

/-- At degree two the principal conjugate and a conjugate with leading
coefficient at least two have distinct moduli already for `D ≥ 15`,
given the two cusp estimates in the article. -/
theorem norm_lt_principal_of_cusp_estimates {D a : ℕ} (hD : 15 ≤ D) (ha : 2 ≤ a)
    (z w : ℂ) (hz : |‖z‖ - Real.exp (Real.pi * Real.sqrt D)| ≤ 2079)
    (hw : |‖w‖ - Real.exp (Real.pi * Real.sqrt D / a)| ≤ 2079) : ‖w‖ < ‖z‖ := by
  have hD' : (15 : ℝ) ≤ D := by exact_mod_cast hD
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : (10 / 3 : ℝ) < Real.sqrt D := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (by positivity)]
    linarith
  let u := Real.pi * Real.sqrt D / 2
  have hu : 5 < u := by
    have h := mul_lt_mul_of_pos_right Real.pi_gt_three (show 0 < Real.sqrt D by linarith)
    dsimp [u]
    linarith
  have h5 : (100 : ℝ) < Real.exp 5 := by
    calc
      (100 : ℝ) < (8 / 3 : ℝ) ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := by gcongr; linarith only [Real.exp_one_gt_d9]
      _ = _ := by norm_num [← Real.exp_nat_mul]
  have hlarge := h5.trans (Real.exp_lt_exp.mpr hu)
  have hprincipal : Real.exp (Real.pi * Real.sqrt D) = Real.exp u ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [u]
    ring
  have hother : Real.exp (Real.pi * Real.sqrt D / a) ≤ Real.exp u :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) (by norm_num) ha')
  have hz' := (abs_le.mp hz).1
  have hw' := (abs_le.mp hw).2
  rw [hprincipal] at hz'
  nlinarith only [hz', hw', hother, hlarge, sq_nonneg (Real.exp u - 100)]

end GRHArticle.SingularModuli
