import GRHArticle.ProgressionFree.PolynomialSearchCutoff

/-!
# Integer bounds on the tilted smooth-polynomial moments

Each degree contributes one term to the integer budgets. The multiplicity of
that degree is the number of monic irreducibles of that degree.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

private theorem sum_polynomialSmoothPrimes_by_degree (F : Type*) [Field F] [Fintype F]
    (L : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ polynomialSmoothPrimes F L, w p.natDegree) =
      ∑ d ∈ Finset.Icc 1 L, (polynomialIrreducibleCount F d : ℝ) * w d := by
  classical
  have hdegree (p : Polynomial F) (hp : p ∈ polynomialSmoothPrimes F L) :
      p.natDegree ∈ Finset.Icc 1 L :=
    let h := mem_polynomialSmoothPrimes.mp hp
    Finset.mem_Icc.mpr ⟨h.2.1.natDegree_pos, h.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hdegree]
  apply Finset.sum_congr rfl
  intro d hd
  have hL := (Finset.mem_Icc.mp hd).2
  have hfiber : (polynomialSmoothPrimes F L).filter (fun p ↦ p.natDegree = d) =
      (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d) := by
    ext p
    simp only [Finset.mem_filter, mem_polynomialSmoothPrimes]
    constructor <;> rintro ⟨⟨hm, hi, _⟩, he⟩
    · exact ⟨⟨hm, hi, he.le⟩, he⟩
    · exact ⟨⟨hm, hi, he.le.trans hL⟩, he⟩
  calc
    _ = ∑ _p ∈ (polynomialSmoothPrimes F L).filter (fun p ↦ p.natDegree = d), w d :=
      Finset.sum_congr rfl (fun _ hp ↦ by rw [(Finset.mem_filter.mp hp).2])
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hfiber, polynomialIrreducibleCount]

private theorem polynomialMomentBudgets_eq_sums (mass : ℕ → ℕ) (L : ℕ) :
    (polynomialMomentBudgets mass L).1 =
      (∑ d ∈ Finset.Icc 1 L, polynomialMeanCeilTerm d (mass d)) ∧
    (polynomialMomentBudgets mass L).2 =
      (∑ d ∈ Finset.Icc 1 L, polynomialVarianceCeilTerm d (mass d)) := by
  induction L with
  | zero => simp [polynomialMomentBudgets]
  | succ d ih =>
    have hd : 1 ≤ d + 1 := Nat.succ_pos d
    simp only [polynomialMomentBudgets, Finset.sum_Icc_succ_top hd, ih.1, ih.2, and_self]

private theorem cast_div_le_ceilDiv (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ ((a ⌈/⌉ b : ℕ) : ℝ) := by
  have h : a ≤ b * (a ⌈/⌉ b) := (ceilDiv_le_iff_le_mul hb).mp le_rfl
  apply (div_le_iff₀ (by exact_mod_cast hb : 0 < (b : ℝ))).2
  exact_mod_cast (by simpa only [Nat.mul_comm b] using h : a ≤ (a ⌈/⌉ b) * b)

private theorem geometric_moments_le_ceilTerms {d : ℕ} (hd : 0 < d) (c : ℕ) :
    let z : ℝ := 127 / 128
    (c : ℝ) * ((d : ℝ) * z ^ d / (1 - z ^ d)) ≤
      (polynomialMeanCeilTerm d (d * c) : ℝ) ∧
    (c : ℝ) * ((d : ℝ) ^ 2 * z ^ d / (1 - z ^ d) ^ 2) ≤
      (polynomialVarianceCeilTerm d (d * c) : ℝ) := by
  have hpow : (127 : ℕ) ^ d < 128 ^ d := Nat.pow_lt_pow_left (by decide) hd.ne'
  have hden := Nat.sub_pos_of_lt hpow
  let a := (127 : ℝ) ^ d
  let b := (128 : ℝ) ^ d
  have ha_eq : (127 : ℝ) ^ d = a := rfl
  have hb_eq : (128 : ℝ) ^ d = b := rfl
  have hb : b ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcast : ((128 ^ d - 127 ^ d : ℕ) : ℝ) = b - a := by
    simp only [Nat.cast_sub hpow.le, Nat.cast_pow, Nat.cast_ofNat, a, b]
  have hdiff : b - a ≠ 0 := by
    rw [← hcast]
    exact_mod_cast hden.ne'
  have hratio : ((127 : ℝ) / 128) ^ d = a / b := div_pow _ _ _
  have hgap : 1 - a / b = (b - a) / b := by rw [sub_div, div_self hb]
  change (c : ℝ) * ((d : ℝ) * ((127 : ℝ) / 128) ^ d /
      (1 - ((127 : ℝ) / 128) ^ d)) ≤ (polynomialMeanCeilTerm d (d * c) : ℝ) ∧
    (c : ℝ) * ((d : ℝ) ^ 2 * ((127 : ℝ) / 128) ^ d /
      (1 - ((127 : ℝ) / 128) ^ d) ^ 2) ≤ (polynomialVarianceCeilTerm d (d * c) : ℝ)
  rw [hratio, hgap]
  constructor
  · calc
      _ = ((d * c * 127 ^ d : ℕ) : ℝ) / ((128 ^ d - 127 ^ d : ℕ) : ℝ) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hcast, ha_eq]
        field_simp [hb, hdiff]
      _ ≤ _ := cast_div_le_ceilDiv _ _ hden
  · calc
      _ = ((d * c * d * 127 ^ d * 128 ^ d : ℕ) : ℝ) /
          (((128 ^ d - 127 ^ d) ^ 2 : ℕ) : ℝ) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hcast, ha_eq, hb_eq]
        field_simp [hb, hdiff]
      _ ≤ _ := cast_div_le_ceilDiv _ _ (pow_pos hden _)

/-- The geometric means and variances summed over the smooth primes are bounded
by the corresponding integer moment budgets. -/
theorem polynomialSmoothPrimes_momentBudgets (F : Type*) [Field F] [Fintype F] (L : ℕ) :
    let z : ℝ := 127 / 128
    let B := polynomialMomentBudgets (fun d ↦ d * polynomialIrreducibleCount F d) L
    (∑ p ∈ polynomialSmoothPrimes F L, (p.natDegree : ℝ) * z ^ p.natDegree /
      (1 - z ^ p.natDegree)) ≤ (B.1 : ℝ) ∧
    (∑ p ∈ polynomialSmoothPrimes F L, (p.natDegree : ℝ) ^ 2 * z ^ p.natDegree /
      (1 - z ^ p.natDegree) ^ 2) ≤ (B.2 : ℝ) := by
  dsimp only
  obtain ⟨hmean, hvar⟩ := polynomialMomentBudgets_eq_sums (fun d ↦ d * polynomialIrreducibleCount F d) L
  constructor
  · rw [sum_polynomialSmoothPrimes_by_degree F L
      (fun d ↦ (d : ℝ) * ((127 : ℝ) / 128) ^ d / (1 - ((127 : ℝ) / 128) ^ d)),
      hmean, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact (geometric_moments_le_ceilTerms (Finset.mem_Icc.mp hd).1 _).1
  · rw [sum_polynomialSmoothPrimes_by_degree F L
      (fun d ↦ (d : ℝ) ^ 2 * ((127 : ℝ) / 128) ^ d / (1 - ((127 : ℝ) / 128) ^ d) ^ 2),
      hvar, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact (geometric_moments_le_ceilTerms (Finset.mem_Icc.mp hd).1 _).2

/-- A positive degree cutoff includes the positive variance contribution from all
linear monic irreducibles. -/
theorem polynomialMomentBudgets_variance_pos (F : Type*) [Field F] [Fintype F] (L : ℕ) (hL : 0 < L) :
    0 < (polynomialMomentBudgets (fun d ↦ d * polynomialIrreducibleCount F d) L).2 := by
  have hcard : polynomialIrreducibleCount F 1 = Fintype.card F := by
    simpa [Nat.divisors_one] using sum_divisors_mul_polynomialIrreducibleCount (F := F) 1 (by decide)
  have hone : 0 < polynomialVarianceCeilTerm 1 (1 * polynomialIrreducibleCount F 1) := by
    simp only [polynomialVarianceCeilTerm, one_mul, mul_one, hcard, pow_one]
    norm_num [ceilDiv_one]
    exact Fintype.card_pos
  rw [(polynomialMomentBudgets_eq_sums _ L).2]
  exact hone.trans_le (Finset.single_le_sum
    (f := fun d ↦ polynomialVarianceCeilTerm d (d * polynomialIrreducibleCount F d))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_Icc.mpr ⟨le_rfl, hL⟩))

end GRHArticle.ProgressionFree
