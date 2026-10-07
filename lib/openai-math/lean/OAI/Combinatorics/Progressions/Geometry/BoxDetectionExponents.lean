import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

def boxModeBudget (a : ℕ) (p : ℝ) : ℝ := p + (p + 1 + a) ^ a + 2

def boxInductionInputBudget (a b : ℕ) (p : ℝ) : ℝ :=
  (p + 1 + b) ^ b + 2 * boxModeBudget a p + 2 * p + 3

def boxRetainedBudget (a : ℕ) (p : ℝ) : ℝ := 2 * boxModeBudget a p + 2 * p + 6

def boxDetectionStepBudget (s a b c : ℕ) (p : ℝ) : ℝ :=
  ((s + 2) ^ (s + 2) : ℕ) * p + (s + 1 : ℕ) * (boxRetainedBudget a p + p) +
    (2 ^ (s + 1) : ℕ) * (boxInductionInputBudget a b p + c) ^ c + boxRetainedBudget a p

theorem boxModeBudget_nonneg (a : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ boxModeBudget a p := by
  unfold boxModeBudget
  positivity

theorem le_boxModeBudget (a : ℕ) {p : ℝ} (hp : 0 ≤ p) : p + 1 ≤ boxModeBudget a p := by
  have h : 0 ≤ (p + 1 + a) ^ a := by positivity
  unfold boxModeBudget
  linarith

theorem boxInductionInputBudget_bounds (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + 1 + b) ^ b ≤ boxInductionInputBudget a b p ∧
    2 * boxModeBudget a p + 1 ≤ boxInductionInputBudget a b p ∧
    p ≤ boxInductionInputBudget a b p := by
  have hmode := boxModeBudget_nonneg a hp
  have hpow : 0 ≤ (p + 1 + b) ^ b := by positivity
  unfold boxInductionInputBudget
  constructor
  · linarith
  constructor <;> linarith

theorem boxDetectionStepBudget_nonneg (s a b c : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ boxDetectionStepBudget s a b c p := by
  unfold boxDetectionStepBudget boxRetainedBudget boxInductionInputBudget boxModeBudget
  positivity

theorem exists_boxDetectionStepBudget_bound (s a b c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → boxDetectionStepBudget s a b c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 1 + Polynomial.C a) ^ a + 2
  let K := (X + 1 + Polynomial.C b) ^ b + 2 * R + 2 * X + 3
  let V := 2 * R + 2 * X + 6
  let P := Polynomial.C ((s + 2) ^ (s + 2)) * X + Polynomial.C (s + 1) * (V + X) +
    Polynomial.C (2 ^ (s + 1)) * (K + Polynomial.C c) ^ c + V
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, V, K, R, X, Polynomial.eval₂_pow, boxDetectionStepBudget,
    boxRetainedBudget, boxInductionInputBudget, boxModeBudget] using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exp_sub_one_le_half_exp (x : ℝ) : Real.exp (x - 1) ≤ Real.exp x / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ Real.exp (x - 1) * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem two_pow_le_exp_of_le (d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    (2 : ℝ) ^ d ≤ Real.exp p := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) htwo d
    _ = Real.exp d := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ _ := Real.exp_le_exp.mpr hd

theorem exp_neg_nat_mul_le_inverse_pow (N d : ℕ) (hN : 0 < N) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    Real.exp (-(N : ℝ) * p) ≤ ((1 : ℝ) / N) ^ d := by
  have hbase : (N : ℝ) ≤ Real.exp N := by linarith [Real.add_one_le_exp (N : ℝ)]
  have hpow : (N : ℝ) ^ d ≤ Real.exp ((N : ℝ) * p) := by
    calc
      _ ≤ (Real.exp N) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg N) hbase d
      _ = Real.exp ((d : ℝ) * N) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N])
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := one_div_le_one_div_of_le (pow_pos hn d) hpow
  simpa only [div_pow, one_pow, neg_mul, Real.exp_neg, one_div, inv_pow] using hi

theorem retained_exponential_weight (d : ℕ) {p r : ℝ} (hd : (d : ℝ) ≤ p) :
    let L := 2 * r + 2 * p + 6
    Real.exp (-L) ≤ Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
      (2 : ℝ) ^ d * Real.exp (-(L + p)) := by
  let L := 2 * r + 2 * p + 6
  have hloss : (2 : ℝ) ^ d * Real.exp (-(L + p)) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp p * Real.exp (-(L + p)) :=
        mul_le_mul_of_nonneg_right (two_pow_le_exp_of_le d hd) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : Real.exp (-r) ^ 2 / (2 * Real.exp (p + 1) ^ 2) =
      Real.exp 4 / 2 * Real.exp (-L) := by
    calc
      _ = (Real.exp (-r) ^ 2 / Real.exp (p + 1) ^ 2) / 2 := by ring
      _ = Real.exp (2 * (-r) - 2 * (p + 1)) / 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub]
        norm_num
      _ = (Real.exp 4 * Real.exp (-L)) / 2 := by
        rw [← Real.exp_add]
        congr 2
        dsimp [L]
        ring
      _ = _ := by ring
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  change Real.exp (-L) ≤ _
  rw [he]
  nlinarith [Real.exp_pos (-L)]

theorem exp_neg_le_of_pow {x P : ℝ} {n : ℕ} (hx : 0 ≤ x) (hP : 0 ≤ P) (hn : n ≠ 0)
    (h : Real.exp (-P) ≤ x ^ n) : Real.exp (-P) ≤ x := by
  have ht : Real.exp (-P) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : ∀ k : ℕ, Real.exp (-P) ^ (k + 1) ≤ Real.exp (-P) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul ih ht (Real.exp_nonneg _) (Real.exp_nonneg _)).trans_eq (mul_one _)
  cases n with
  | zero => exact False.elim (hn rfl)
  | succ k => exact le_of_pow_le_pow_left₀ (Nat.succ_ne_zero k) hx ((hp k).trans h)

theorem box_detection_exponential_product (s a b c d : ℕ) {p : ℝ} (hd : (d : ℝ) ≤ p) :
    Real.exp (-boxDetectionStepBudget s a b c p) ≤
      ((1 : ℝ) / ((s : ℝ) + 2) ^ (s + 2)) ^ d *
        Real.exp (-(boxRetainedBudget a p + p)) ^ (s + 1) *
        Real.exp (-((boxInductionInputBudget a b p + c) ^ c)) ^ (2 ^ (s + 1)) *
        Real.exp (-boxRetainedBudget a p) := by
  have hc : Real.exp (-(((s + 2) ^ (s + 2) : ℕ) : ℝ) * p) ≤
      ((1 : ℝ) / ((s : ℝ) + 2) ^ (s + 2)) ^ d := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
      exp_neg_nat_mul_le_inverse_pow ((s + 2) ^ (s + 2)) d (by positivity) hd
  calc
    _ = Real.exp (-(((s + 2) ^ (s + 2) : ℕ) : ℝ) * p) *
        Real.exp (-(boxRetainedBudget a p + p)) ^ (s + 1) *
        Real.exp (-((boxInductionInputBudget a b p + c) ^ c)) ^ (2 ^ (s + 1)) *
        Real.exp (-boxRetainedBudget a p) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold boxDetectionStepBudget
      ring
    _ ≤ _ := by gcongr

end Erdos3

end

end OAI
