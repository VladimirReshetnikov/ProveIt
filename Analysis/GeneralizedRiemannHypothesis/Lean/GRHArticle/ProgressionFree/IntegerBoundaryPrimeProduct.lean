import GRHArticle.ProgressionFree.IntegerPrimeGapCertificate

/-!
# Lower bound for the rough density at the exchange cutoff

Multiply the finite Euler factors in a balanced tree. Round down at every
multiplication on the same integer scale to keep the certificate small.
-/

namespace GRHArticle.ProgressionFree

open Finset

private def scale : ℕ := 10^14
private theorem scale_pos : (0:ℝ) < scale := by norm_num [scale]

private def candidate (p : ℕ) : Bool :=
  if p ≤ 83 then decide p.Prime else decide (p.Coprime (Nat.factorial 83))

private theorem prime_candidate {p : ℕ} (hp : p.Prime) : candidate p = true := by
  unfold candidate
  split
  · exact decide_eq_true hp
  · exact decide_eq_true (hp.coprime_factorial_of_lt (by omega))

private def scaledFactor (p : ℕ) : ℕ :=
  if p ≤ 6619 ∧ candidate p = true then scale*(p-1)/p else scale

private noncomputable def localFactor (p : ℕ) : ℝ :=
  if p ≤ 6619 ∧ p.Prime then 1-(p:ℝ)⁻¹ else 1

private theorem scaledDiv_le (a b : ℕ) (hb : 0 < b) :
    ((a/b:ℕ):ℝ) ≤ (a:ℝ)/b := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hb)).mpr
  exact_mod_cast Nat.div_mul_le_self a b

private theorem scaledFactor_le (p : ℕ) : (scaledFactor p : ℝ)/scale ≤ localFactor p := by
  by_cases h : p ≤ 6619 ∧ p.Prime
  · rw [scaledFactor,localFactor,if_pos ⟨h.1, prime_candidate h.2⟩,if_pos h,div_le_iff₀ scale_pos]
    apply (scaledDiv_le _ _ h.2.pos).trans
    rw [Nat.cast_mul, Nat.cast_sub h.2.one_lt.le, Nat.cast_one]
    apply le_of_eq
    field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast h.2.ne_zero]
  · rw [localFactor,if_neg h,scaledFactor]
    split
    · apply (div_le_one scale_pos).mpr
      have hm : scale * (p-1) ≤ p * scale := by simpa only [Nat.mul_comm p scale] using Nat.mul_le_mul_left scale (Nat.sub_le p 1)
      exact_mod_cast Nat.div_le_of_le_mul hm
    · rw [div_self scale_pos.ne']

private abbrev scaledProduct := integerDyadicScaledProduct scale scaledFactor

private theorem scaledProduct_le (k a : ℕ) : (scaledProduct k a : ℝ)/scale ≤
    ∏ i ∈ range (2^k), localFactor (a+i) := by
  induction k generalizing a with
  | zero => simpa [scaledProduct,integerDyadicScaledProduct] using scaledFactor_le a
  | succ k ih =>
    rw [show scaledProduct (k+1) a = scaledProduct k a * scaledProduct k (a+2^k) / scale by rfl, pow_succ, Nat.mul_two, prod_range_add]
    simp only [← Nat.add_assoc]
    calc
      _ ≤ (((scaledProduct k a * scaledProduct k (a+2^k) : ℕ):ℝ)/scale)/scale :=
        div_le_div_of_nonneg_right (scaledDiv_le _ _ (by decide)) scale_pos.le
      _ = ((scaledProduct k a : ℝ)/scale) * ((scaledProduct k (a+2^k) : ℝ)/scale) := by
        push_cast
        ring
      _ ≤ _ := mul_le_mul (ih _) (ih _) (by positivity) ((show 0 ≤ (scaledProduct k a : ℝ)/scale by positivity).trans (ih a))

set_option Elab.async false
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem product_certificate : 6372823000000 ≤ scaledProduct 13 0 := by decide +kernel

theorem integerSmoothDensityFactor_6619_lower :
    (6372823:ℝ)/10^8 ≤ integerSmoothDensityFactor 6619 := by
  have h := scaledProduct_le 13 0
  simp only [Nat.zero_add, localFactor, ← prod_filter] at h
  have hset : (range (2^13)).filter (fun p ↦ p ≤ 6619 ∧ p.Prime) = Nat.primesLE 6619 := by
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primesLE]
    exact ⟨And.right,fun h ↦ ⟨lt_of_le_of_lt h.1 (by decide),h⟩⟩
  rw [hset] at h
  apply le_trans _ h
  have hw : (6372823000000:ℝ) ≤ scaledProduct 13 0 := by exact_mod_cast product_certificate
  norm_num [scale]
  linarith

end GRHArticle.ProgressionFree
