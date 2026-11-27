import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp

/-!
# A finite logarithmic lower bound for prime reciprocal sums

A finite Euler product dominates the harmonic sum. Taking logarithms costs
at most one beyond the sum of prime reciprocals, since the correction is
bounded by the telescoping sum of `1 / (n * (n - 1))`.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

private theorem one_lt_prime_cast {p : ℕ} (hp : p.Prime) : 1 < (p : ℝ) := by
  exact_mod_cast hp.one_lt

private theorem sub_prime_recip_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have h := one_lt_prime_cast hp
  apply sub_pos.mpr
  rw [div_lt_iff₀ (by linarith only [h]), one_mul]
  exact h

private noncomputable def natReciprocal : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by
    simp only [Nat.cast_mul, mul_inv_rev]
    exact mul_comm _ _

private theorem harmonic_as_Icc (Y : ℕ) :
    (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ := by
  have hI : Finset.Ico 1 (Y + 1) = Finset.Icc 1 Y := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [← hI, Finset.sum_Ico_eq_sum_range, harmonic]
  push_cast
  simp only [add_comm]

private theorem harmonic_le_finitePrimeEulerProduct (Y : ℕ) :
    (harmonic Y : ℝ) ≤ ∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  have hnorm {p : ℕ} (hp : p.Prime) : ‖natReciprocal p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← one_div]
    exact sub_pos.mp (sub_prime_recip_pos hp)
  have hprod :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hnorm (Y + 1)).2
  let I := Finset.Icc 1 Y
  let i : ↥I ↪ ↥(Nat.smoothNumbers (Y + 1)) :=
    ⟨fun n => ⟨n.val, by
      obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp n.property
      exact Nat.mem_smoothNumbers_of_lt h₁ (Nat.lt_succ_of_le h₂)⟩,
      fun _ _ h => Subtype.ext (congrArg (fun q : ↥(Nat.smoothNumbers (Y + 1)) => q.val) h)⟩
  have hle : (∑ q ∈ Finset.univ.map i, natReciprocal q.val) ≤
      ∑' q : ↥(Nat.smoothNumbers (Y + 1)), natReciprocal q.val :=
    hprod.summable.sum_le_tsum (Finset.univ.map i) (fun q _ =>
      show 0 ≤ natReciprocal q.val from inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [hprod.tsum_eq, Finset.sum_map, Finset.univ_eq_attach] at hle
  have hs : (∑ x ∈ I.attach, natReciprocal (i x).val) =
      ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹ :=
    Finset.sum_attach I (fun n : ℕ => (n : ℝ)⁻¹)
  rw [harmonic_as_Icc, ← hs]
  simpa only [Nat.primesLE, natReciprocal, MonoidHom.coe_mk, OneHom.coe_mk, one_div] using hle

private theorem sum_prime_log_remainder_le_one (Y : ℕ) (hY : 1 ≤ Y) :
    (∑ p ∈ Nat.primesLE Y, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  let f (p : ℕ) : ℝ := 1 / ((p : ℝ) * ((p : ℝ) - 1))
  have hsubset : Nat.primesLE Y ⊆ Finset.Icc 2 Y := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨Nat.two_le_of_mem_primesLE hp, Nat.le_of_mem_primesLE hp⟩
  have hinterval : Finset.Ico (1 + 1) (Y + 1) = Finset.Icc 2 Y := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hshift := Finset.sum_Ico_add' f 1 Y 1
  rw [hinterval] at hshift
  calc
    (∑ p ∈ Nat.primesLE Y, f p) ≤ ∑ p ∈ Finset.Icc 2 Y, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun n hn _ => by
        have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        exact one_div_nonneg.mpr (mul_nonneg (by linarith only [h]) (by linarith only [h]))
    _ = ∑ n ∈ Finset.Ico 1 Y, f (n + 1) := hshift.symm
    _ = ∑ n ∈ Finset.Ico 1 Y, (1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ico.mp hn).1
      have hs : 0 < (n : ℝ) + 1 := by linarith only [hn₀]
      simp only [f, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      field_simp [hn₀.ne', hs.ne']
      ring
    _ = 1 - 1 / (Y : ℝ) := by
      calc
        _ = -(∑ n ∈ Finset.Ico 1 Y, (1 / ((n + 1 : ℕ) : ℝ) - 1 / (n : ℝ))) := by
          simp only [← Finset.sum_neg_distrib, neg_sub]
        _ = _ := by
          rw [Finset.sum_Ico_sub (fun n : ℕ => 1 / (n : ℝ)) hY, neg_sub, Nat.cast_one, div_one]
    _ ≤ _ := sub_le_self _ (by positivity)

private theorem log_primeEulerFactor_le {p : ℕ} (hp : p.Prime) :
    Real.log ((1 - 1 / (p : ℝ))⁻¹) ≤ 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have h₁ := one_lt_prime_cast hp
  have hp₀ : 0 < (p : ℝ) := by linarith only [h₁]
  have hsub : 0 < (p : ℝ) - 1 := sub_pos.mpr h₁
  calc
    _ ≤ (1 - 1 / (p : ℝ))⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr (sub_prime_recip_pos hp))
    _ = _ := by
      field_simp [hp₀.ne', hsub.ne']
      ring

/-- The reciprocal sum over the primes up to `Y` is at least `log (log Y) - 1`. -/
theorem log_log_le_primeReciprocalSum_add_one (Y : ℕ) (hY : 1 < Y) :
    Real.log (Real.log (Y : ℝ)) ≤ (∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ)) + 1 := by
  have hlog₀ : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hharm : Real.log (Y : ℝ) ≤ (harmonic Y : ℝ) := by
    have h := log_add_one_le_harmonic Y
    have hY₀ : 0 < (Y : ℝ) := Nat.cast_pos.mpr (by omega)
    exact (Real.log_le_log hY₀ (by push_cast; linarith)).trans h
  calc
    _ ≤ Real.log (∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ))⁻¹) :=
      Real.log_le_log hlog₀ (hharm.trans (harmonic_le_finitePrimeEulerProduct Y))
    _ = ∑ p ∈ Nat.primesLE Y, Real.log ((1 - 1 / (p : ℝ))⁻¹) :=
      Real.log_prod fun p hp => inv_ne_zero (sub_prime_recip_pos (Nat.prime_of_mem_primesLE hp)).ne'
    _ ≤ ∑ p ∈ Nat.primesLE Y, (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
      Finset.sum_le_sum fun p hp => log_primeEulerFactor_le (Nat.prime_of_mem_primesLE hp)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      linarith only [sum_prime_log_remainder_le_one Y hY.le]

end GRHArticle.ProgressionFree
