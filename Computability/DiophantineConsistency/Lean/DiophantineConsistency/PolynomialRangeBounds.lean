import DiophantineConsistency.SelectiveCoefficientBounds

/-!
# Polynomial range bounds before binary digit recovery

The source radix need only be an integer at least two. Positivity and the
coarse evaluation bounds therefore apply before a ratio theorem has recovered
that the radix is a power of two.
-/

namespace DiophantineConsistency.PolynomialRangeBounds

open Polynomial Finset
open scoped BigOperators

theorem geometric_identity (B : ℤ) (d : ℕ) :
    (B - 1) * (∑ i ∈ range d, B ^ i) = B ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem geometric_lt_two_top {B : ℤ} (hB : 2 ≤ B) (d : ℕ) :
    (∑ i ∈ range (d + 1), B ^ i) < 2 * B ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ]
    have hp : 0 < B ^ d := by positivity
    have hnext : B ^ (d + 1) = B ^ d * B := pow_succ _ _
    nlinarith

theorem abs_eval_lt {B H : ℤ} (hB : 2 ≤ B) (hH : 0 < H)
    (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (hc : ∀ i, |p.coeff i| ≤ H) :
    |p.eval B| < 2 * H * B ^ d := by
  rw [eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
  calc
    |∑ i ∈ range (d + 1), p.coeff i * B ^ i| ≤
        ∑ i ∈ range (d + 1), |p.coeff i * B ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (d + 1), H * B ^ i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ B ^ i)]
      exact mul_le_mul_of_nonneg_right (hc i) (by positivity)
    _ = H * (∑ i ∈ range (d + 1), B ^ i) := (Finset.mul_sum _ _ _).symm
    _ < H * (2 * B ^ d) := mul_lt_mul_of_pos_left (geometric_lt_two_top hB d) hH
    _ = _ := by ring

/-- A leading coefficient two dominates all lower signed coefficients in a
radix larger than their uniform bound plus one. -/
theorem eval_gt_top_power {B H : ℤ} (hB : 2 ≤ B) (hBH : H ≤ B - 1)
    (p : ℤ[X]) {d : ℕ} (hd : p.natDegree ≤ d) (hc : ∀ i, |p.coeff i| ≤ H)
    (htop : p.coeff d = 2) : B ^ d < p.eval B := by
  have hg0 : 0 ≤ ∑ i ∈ range d, B ^ i := Finset.sum_nonneg (fun i _ => by positivity)
  have hlow : -H * (∑ i ∈ range d, B ^ i) ≤ ∑ i ∈ range d, p.coeff i * B ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (neg_le_neg (hc i)).trans (neg_abs_le _)
  have hgeom := geometric_identity B d
  have hscaled := mul_le_mul_of_nonneg_right hBH hg0
  rw [hgeom] at hscaled
  rw [eval_eq_sum_range' (by omega : p.natDegree < d + 1), sum_range_succ, htop]
  linarith

/-- For the supplied scale, no integrality or binary-base conclusion is
needed to show that its radix is larger than the low digit cap. -/
theorem scale_gt_four_digits {H b : ℤ} (hH : 0 < H) (hb : 1 ≤ b) :
    4 * b < 4096 * H * b ^ 2 := by
  have hH1 : 1 ≤ H := by omega
  have hmul : b ^ 2 ≤ H * b ^ 2 := by nlinarith [sq_nonneg b]
  nlinarith [sq_nonneg (b - 1)]

/-- The weak soundness cap already places g inside the entire low block. -/
theorem weak_cap_lt_low_block {B b g : ℤ} (hB : 2 ≤ B)
    (hscale : 4 * b < B) (W : ℕ) (hg : g < 4 * b * B ^ W) :
    g < B ^ (W + 1) := by
  have hp : 0 < B ^ W := by positivity
  rw [pow_succ]
  nlinarith

/-- The literal dense-padded high word in the selected source. -/
def highWord (p : ℤ[X]) (B g : ℤ) (padding D W : ℕ) : ℤ :=
  2 * (B ^ padding + g) ^ 2 * p.eval B +
    B * (∑ i ∈ range (D + 2 * W + 1), B ^ i)

/-- Positivity holds for every nonnegative candidate code, independently of
the cap that the later ratio theorem will recover. -/
theorem highWord_pos {B H g : ℤ} (hB : 2 ≤ B) (hBH : H ≤ B - 1) (hg : 0 ≤ g)
    (p : ℤ[X]) {D W padding : ℕ} (hd : p.natDegree ≤ D)
    (hc : ∀ i, |p.coeff i| ≤ H) (htop : p.coeff D = 2) :
    0 < highWord p B g padding D W := by
  have hp : 0 < p.eval B := (by positivity : 0 < B ^ D).trans
    (eval_gt_top_power hB hBH p hd hc htop)
  have hmain : 0 < 2 * (B ^ padding + g) ^ 2 * p.eval B := by positivity
  have hoff : 0 ≤ B * (∑ i ∈ range (D + 2 * W + 1), B ^ i) := by positivity
  unfold highWord
  exact add_pos_of_pos_of_nonneg hmain hoff

/-- A bound on arbitrary weak-cap assignments, established before binary
decoding or the parent equations. The whole high word fits `4 B^(K+1)`. -/
theorem highWord_bounds {B H b g : ℤ} (hB : 2 ≤ B) (hH : 0 < H) (hb : 1 ≤ b)
    (hscale : B = 4096 * H * b ^ 2) (hg : 0 ≤ g)
    (p : ℤ[X]) {D W padding : ℕ} (hd : p.natDegree ≤ D)
    (hc : ∀ i, |p.coeff i| ≤ H) (htop : p.coeff D = 2)
    (hpadding : padding ≤ W) (hcap : g < 4 * b * B ^ W) :
    0 < highWord p B g padding D W ∧ highWord p B g padding D W <
      4 * B ^ (D + 2 * W + 1) := by
  have hb2 : 1 ≤ b ^ 2 := by nlinarith
  have hH1 : 1 ≤ H := by omega
  have hHb : H ≤ H * b ^ 2 := by nlinarith [mul_nonneg hH.le (sub_nonneg.mpr hb2)]
  have hBH : H ≤ B - 1 := by nlinarith
  have hDp : 0 < p.eval B := (by positivity : 0 < B ^ D).trans
    (eval_gt_top_power hB hBH p hd hc htop)
  have hDu : p.eval B < 2 * H * B ^ D := (le_abs_self _).trans_lt
    (abs_eval_lt hB hH p hd hc)
  have hpow : 0 < B ^ W := by positivity
  have hpad : B ^ padding ≤ B ^ W := pow_le_pow_right₀ (by linarith) hpadding
  have hC0 : 0 < B ^ padding + g := by positivity
  have hbmul : B ^ W ≤ b * B ^ W := by nlinarith
  have hCu : B ^ padding + g < 5 * b * B ^ W := by linarith
  have hC2 : (B ^ padding + g) ^ 2 ≤ (5 * b * B ^ W) ^ 2 :=
    pow_le_pow_left₀ hC0.le hCu.le 2
  have hprod : 2 * (B ^ padding + g) ^ 2 * p.eval B ≤
      100 * H * b ^ 2 * B ^ (D + 2 * W) := by
    calc
      _ ≤ (2 * (5 * b * B ^ W) ^ 2) * (2 * H * B ^ D) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC2 (by decide)) hDu.le hDp.le (by positivity)
      _ = _ := by rw [pow_add, pow_mul]; ring
  have hsmall : 100 * H * b ^ 2 < B := by nlinarith [mul_pos hH (by positivity : 0 < b ^ 2)]
  have hmain : 2 * (B ^ padding + g) ^ 2 * p.eval B < B ^ (D + 2 * W + 1) := by
    calc
      _ ≤ 100 * H * b ^ 2 * B ^ (D + 2 * W) := hprod
      _ < B * B ^ (D + 2 * W) := mul_lt_mul_of_pos_right hsmall (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hoff : B * (∑ i ∈ range (D + 2 * W + 1), B ^ i) <
      2 * B ^ (D + 2 * W + 1) := by
    have h := mul_lt_mul_of_pos_left (geometric_lt_two_top hB (D + 2 * W)) (by linarith : 0 < B)
    simpa only [pow_succ, mul_left_comm, mul_comm, mul_assoc] using h
  have hoff0 : 0 ≤ B * (∑ i ∈ range (D + 2 * W + 1), B ^ i) := by positivity
  have hmain0 : 0 < 2 * (B ^ padding + g) ^ 2 * p.eval B := by positivity
  unfold highWord
  constructor
  · linarith
  · have hp : 0 < B ^ (D + 2 * W + 1) := by positivity
    linarith

end DiophantineConsistency.PolynomialRangeBounds
