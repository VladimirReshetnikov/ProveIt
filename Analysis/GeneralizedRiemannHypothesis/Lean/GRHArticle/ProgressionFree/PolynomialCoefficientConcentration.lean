import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# An explicit search cutoff for a positive convolution coefficient

A nonnegative coefficient sequence is tilted at a positive real point and normalized
to total mass one. Its mean and variance control how much positive convolution mass
lies beyond a finite cutoff.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

/-- The value at `z` of the convergent coefficient series. -/
noncomputable def coefficientMass (z : ℝ) (H : ℕ → ℝ) : ℝ :=
  ∑' n, H n * z ^ n

/-- The normalized weight of coefficient `n` at the tilt `z`. -/
noncomputable def coefficientWeight (z : ℝ) (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  H n * z ^ n / coefficientMass z H

/-- The mean of the normalized coefficient weights. -/
noncomputable def coefficientMean (z : ℝ) (H : ℕ → ℝ) : ℝ :=
  ∑' n, coefficientWeight z H n * n

/-- The variance of the normalized coefficient weights. -/
noncomputable def coefficientVariance (z : ℝ) (H : ℕ → ℝ) : ℝ :=
  ∑' n, coefficientWeight z H n * ((n : ℝ) - coefficientMean z H) ^ 2

/-- Coefficient `n` of the product `H * (P - Q)`. -/
def signedCoefficientConvolution {A : Type*} [Ring A] (H P Q : ℕ → A) (n : ℕ) : A :=
  ∑ d ∈ Finset.range (n + 1), (P d - Q d) * H (n - d)

private theorem coefficient_prefix_lower {w : ℕ → ℝ} {μ t : ℝ} {r : ℕ}
    (hw : Summable w) (hw₀ : ∀ n, 0 ≤ w n) (hunit : ∑' n, w n = 1)
    (hvar : Summable (fun n ↦ w n * ((n : ℝ) - μ) ^ 2))
    (ht : 0 < t) (hr : μ + t ≤ r) :
    1 - (∑' n, w n * ((n : ℝ) - μ) ^ 2) / t ^ 2 ≤
      ∑ n ∈ Finset.range (r + 1), w n := by
  let truncated (n : ℕ) := if n ≤ r then w n else 0
  have hsupport : ∀ n ∉ Finset.range (r + 1), truncated n = 0 := by
    intro n hn
    exact if_neg (fun h ↦ hn (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  have hs : Summable truncated := summable_of_ne_finset_zero hsupport
  have hpref : (∑' n, truncated n) = ∑ n ∈ Finset.range (r + 1), w n := by
    rw [tsum_eq_sum hsupport]
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have ht₂ : 0 < t ^ 2 := pow_pos ht _
  have hpoint (n : ℕ) : w n ≤ truncated n + w n * ((n : ℝ) - μ) ^ 2 / t ^ 2 := by
    by_cases hn : n ≤ r
    · rw [show truncated n = w n from if_pos hn]
      exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (hw₀ _) (sq_nonneg _)) ht₂.le)
    · have hnr : (r : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
      have htn : t ≤ (n : ℝ) - μ := by linarith only [hr, hnr]
      have hsq : t ^ 2 ≤ ((n : ℝ) - μ) ^ 2 := pow_le_pow_left₀ ht.le htn _
      rw [show truncated n = 0 from if_neg hn, zero_add]
      exact (le_div_iff₀ ht₂).2 (mul_le_mul_of_nonneg_left hsq (hw₀ _))
  have hsum := hw.tsum_le_tsum hpoint (hs.add (hvar.div_const (t ^ 2)))
  rw [hs.tsum_add (hvar.div_const (t ^ 2)), tsum_div_const, hpref, hunit] at hsum
  linarith only [hsum]

/-- Reindex a finite triangular coefficient sum by the degree contributed by the
second factor. -/
private theorem sum_triangular {A : Type*} [CommSemiring A] (R : ℕ) (a w : ℕ → A) :
    (∑ n ∈ Finset.range (R + 1), ∑ d ∈ Finset.range (n + 1), a d * w (n - d)) =
      ∑ d ∈ Finset.range (R + 1), a d * ∑ k ∈ Finset.range (R - d + 1), w k := by
  have hindex (n d : ℕ) :
      n ∈ Finset.range (R + 1) ∧ d ∈ Finset.range (n + 1) ↔
        n ∈ Finset.Ico d (R + 1) ∧ d ∈ Finset.range (R + 1) := by
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  rw [Finset.sum_comm' hindex]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : d ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum, show R + 1 - d = R - d + 1 by omega]
  simp

/-- The normalized truncated coefficient sum is positive under the concentration
inequality from the article. The moment assumptions use the actual mean and variance
of the tilted coefficient weights. -/
theorem truncated_signedCoefficientConvolution_pos {H P Q : ℕ → ℝ} {z U V t C γ : ℝ}
    {L R : ℕ} (hz : 0 < z) (hH₀ : ∀ n, 0 ≤ H n) (hP₀ : ∀ n, 0 ≤ P n)
    (hQ₀ : ∀ n, 0 ≤ Q n) (hH : Summable (fun n ↦ H n * z ^ n))
    (hHpos : 0 < coefficientMass z H) (hQ : Summable (fun n ↦ Q n * z ^ n))
    (hPsupp : ∀ n, L < n → P n = 0)
    (hfirst : Summable (fun n ↦ coefficientWeight z H n * n))
    (hsecond : Summable (fun n ↦ coefficientWeight z H n *
      ((n : ℝ) - coefficientMean z H) ^ 2))
    (hmean : coefficientMean z H ≤ U) (hvar : coefficientVariance z H ≤ V)
    (hgain : γ < coefficientMass z P - coefficientMass z Q) (hPbound : coefficientMass z P ≤ C)
    (ht : 0 < t) (herror : C * V / t ^ 2 < γ) (hR : (L : ℝ) + U + t ≤ R) :
    0 < ∑ n ∈ Finset.range (R + 1),
      signedCoefficientConvolution H P Q n * z ^ n / coefficientMass z H := by
  let w := coefficientWeight z H
  let μ := coefficientMean z H
  have hw : Summable w := hH.div_const _
  have hw₀ (n : ℕ) : 0 ≤ w n := div_nonneg (mul_nonneg (hH₀ _) (pow_nonneg hz.le _)) hHpos.le
  have hwunit : ∑' n, w n = 1 := by
    change (∑' n, H n * z ^ n / coefficientMass z H) = 1
    rw [tsum_div_const, ← coefficientMass, div_self hHpos.ne']
  have hp₀ (d : ℕ) : 0 ≤ P d * z ^ d := mul_nonneg (hP₀ d) (pow_nonneg hz.le _)
  have hq₀ (d : ℕ) : 0 ≤ Q d * z ^ d := mul_nonneg (hQ₀ d) (pow_nonneg hz.le _)
  have hμ₀ : 0 ≤ μ := hfirst.hasSum.nonneg (fun n ↦ mul_nonneg (hw₀ n) (Nat.cast_nonneg n))
  have hV₀ : 0 ≤ V := (hsecond.hasSum.nonneg (fun n ↦ mul_nonneg (hw₀ n) (sq_nonneg _))).trans hvar
  have hL : L ≤ R := by
    have hLR : (L : ℝ) ≤ R := by linarith only [hμ₀, hmean, ht, hR]
    exact_mod_cast hLR
  have hp_mass : coefficientMass z P = ∑ d ∈ Finset.range (L + 1), P d * z ^ d := by
    apply tsum_eq_sum
    intro d hd
    rw [hPsupp d (by simpa using hd), zero_mul]
  have hscale (n : ℕ) :
      signedCoefficientConvolution H P Q n * z ^ n / coefficientMass z H =
        ∑ d ∈ Finset.range (n + 1), (P d * z ^ d - Q d * z ^ d) * w (n - d) := by
    rw [signedCoefficientConvolution, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hpow : z ^ d * z ^ (n - d) = z ^ n := by rw [← pow_add, Nat.add_sub_of_le hdn]
    rw [← hpow]
    simp only [w, coefficientWeight, div_eq_mul_inv]
    ring
  simp_rw [hscale]
  rw [sum_triangular]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hprefix (r : ℕ) : (∑ k ∈ Finset.range (r + 1), w k) ≤ 1 := by
    rw [← hwunit]
    exact hw.sum_le_tsum _ (fun k _ ↦ hw₀ k)
  have hneg : (∑ d ∈ Finset.range (R + 1),
      Q d * z ^ d * ∑ k ∈ Finset.range (R - d + 1), w k) ≤ coefficientMass z Q := by
    calc
      _ ≤ ∑ d ∈ Finset.range (R + 1), Q d * z ^ d := by
        apply Finset.sum_le_sum
        intro d _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hprefix (R - d)) (hq₀ d)
      _ ≤ _ := hQ.sum_le_tsum _ (fun d _ ↦ hq₀ d)
  have hpos : coefficientMass z P * (1 - V / t ^ 2) ≤
      ∑ d ∈ Finset.range (R + 1), P d * z ^ d * ∑ k ∈ Finset.range (R - d + 1), w k := by
    rw [hp_mass, Finset.sum_mul]
    have hsubset : Finset.range (L + 1) ⊆ Finset.range (R + 1) :=
      Finset.range_mono (Nat.succ_le_succ hL)
    rw [← Finset.sum_subset hsubset (f := fun d ↦ P d * z ^ d *
      ∑ k ∈ Finset.range (R - d + 1), w k) (by
        intro d _ hd
        rw [hPsupp d (by simpa using hd), zero_mul, zero_mul])]
    apply Finset.sum_le_sum
    intro d hd
    have hdL : d ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hdR : d ≤ R := hdL.trans hL
    have hdL' : (d : ℝ) ≤ L := by exact_mod_cast hdL
    have hdr : μ + t ≤ (R - d : ℕ) := by
      rw [Nat.cast_sub hdR]
      linarith only [hmean, hdL', hR]
    apply mul_le_mul_of_nonneg_left _ (hp₀ d)
    apply le_trans _ (coefficient_prefix_lower hw hw₀ hwunit hsecond ht hdr)
    apply sub_le_sub_left
    exact (div_le_div_iff_of_pos_right (pow_pos ht _)).2 hvar
  have herr : coefficientMass z P * V / t ^ 2 ≤ C * V / t ^ 2 :=
    (div_le_div_iff_of_pos_right (pow_pos ht _)).2 (mul_le_mul_of_nonneg_right hPbound hV₀)
  have heq : coefficientMass z P * (1 - V / t ^ 2) =
      coefficientMass z P - coefficientMass z P * V / t ^ 2 := by ring
  rw [heq] at hpos
  linarith only [hpos, hneg, herr, hgain, herror]

/-- If the normalized truncated sum of the real convolution of integer coefficients
is positive, one coefficient at an index at most the cutoff is at least one. -/
theorem exists_pos_int_signedCoefficientConvolution_le {H P Q : ℕ → ℤ} {z : ℝ} {R : ℕ}
    (hz : 0 < z) (hHpos : 0 < coefficientMass z (fun n ↦ H n))
    (hpos : 0 < ∑ n ∈ Finset.range (R + 1),
      signedCoefficientConvolution (fun n ↦ (H n : ℝ)) (fun n ↦ (P n : ℝ))
        (fun n ↦ (Q n : ℝ)) n * z ^ n / coefficientMass z (fun n ↦ H n)) :
    ∃ n ≤ R, 1 ≤ signedCoefficientConvolution H P Q n := by
  have hsum : (∑ _n ∈ Finset.range (R + 1), (0 : ℝ)) <
      ∑ n ∈ Finset.range (R + 1), signedCoefficientConvolution
        (fun n ↦ (H n : ℝ)) (fun n ↦ (P n : ℝ)) (fun n ↦ (Q n : ℝ)) n *
          z ^ n / coefficientMass z (fun n ↦ H n) := by simpa only [Finset.sum_const_zero] using hpos
  obtain ⟨n, hn, hnpos⟩ := Finset.exists_lt_of_sum_lt hsum
  have hreal : 0 < signedCoefficientConvolution (fun n ↦ (H n : ℝ))
      (fun n ↦ (P n : ℝ)) (fun n ↦ (Q n : ℝ)) n :=
    pos_of_mul_pos_left ((div_pos_iff_of_pos_right hHpos).mp hnpos) (pow_nonneg hz.le _)
  have hcast : (↑(signedCoefficientConvolution H P Q n) : ℝ) =
      signedCoefficientConvolution (fun n ↦ (H n : ℝ)) (fun n ↦ (P n : ℝ)) (fun n ↦ (Q n : ℝ)) n := by
    simp only [signedCoefficientConvolution, Int.cast_sum, Int.cast_mul, Int.cast_sub]
  rw [← hcast] at hreal
  exact ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), Int.add_one_le_iff.mpr (Int.cast_pos.mp hreal)⟩

/-- The finite convolution agrees with the coefficient of the formal product. -/
theorem signedCoefficientConvolution_eq_coeff {A : Type*} [CommRing A] (H P Q : ℕ → A) (n : ℕ) :
    signedCoefficientConvolution H P Q n =
      PowerSeries.coeff n (PowerSeries.mk H * (PowerSeries.mk P - PowerSeries.mk Q)) := by
  rw [mul_comm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [signedCoefficientConvolution]

/-- Under the concentration hypotheses, the actual integer power-series product
has a coefficient at least one through the cutoff. -/
theorem exists_pos_int_coeff_product_le {H P Q : ℕ → ℤ} {z U V t C γ : ℝ}
    {L R : ℕ} (hz : 0 < z) (hH₀ : ∀ n, 0 ≤ H n) (hP₀ : ∀ n, 0 ≤ P n)
    (hQ₀ : ∀ n, 0 ≤ Q n) (hH : Summable (fun n ↦ (H n : ℝ) * z ^ n))
    (hHpos : 0 < coefficientMass z (fun n ↦ H n)) (hQ : Summable (fun n ↦ (Q n : ℝ) * z ^ n))
    (hPsupp : ∀ n, L < n → P n = 0)
    (hfirst : Summable (fun n ↦ coefficientWeight z (fun k ↦ H k) n * n))
    (hsecond : Summable (fun n ↦ coefficientWeight z (fun k ↦ H k) n *
      ((n : ℝ) - coefficientMean z (fun k ↦ H k)) ^ 2))
    (hmean : coefficientMean z (fun n ↦ H n) ≤ U)
    (hvar : coefficientVariance z (fun n ↦ H n) ≤ V)
    (hgain : γ < coefficientMass z (fun n ↦ P n) - coefficientMass z (fun n ↦ Q n))
    (hPbound : coefficientMass z (fun n ↦ P n) ≤ C)
    (ht : 0 < t) (herror : C * V / t ^ 2 < γ) (hR : (L : ℝ) + U + t ≤ R) :
    ∃ n ≤ R, 1 ≤ PowerSeries.coeff n (PowerSeries.mk H * (PowerSeries.mk P - PowerSeries.mk Q)) := by
  have hpos := truncated_signedCoefficientConvolution_pos
    (H := fun n ↦ (H n : ℝ)) (P := fun n ↦ (P n : ℝ)) (Q := fun n ↦ (Q n : ℝ))
    hz (fun n ↦ by exact_mod_cast hH₀ n) (fun n ↦ by exact_mod_cast hP₀ n)
    (fun n ↦ by exact_mod_cast hQ₀ n) hH hHpos hQ (fun n hn ↦ by simp [hPsupp n hn])
    hfirst hsecond hmean hvar hgain hPbound ht herror hR
  obtain ⟨n, hn, hcoeff⟩ := exists_pos_int_signedCoefficientConvolution_le hz hHpos hpos
  exact ⟨n, hn, signedCoefficientConvolution_eq_coeff H P Q n ▸ hcoeff⟩

end GRHArticle.ProgressionFree
