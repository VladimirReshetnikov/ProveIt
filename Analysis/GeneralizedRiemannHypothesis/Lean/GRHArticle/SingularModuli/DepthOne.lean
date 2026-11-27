import GRHArticle.SingularModuli.DiskRootTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Depth one bounds for sparse polynomials

For any odd prime, Legendre's digit formula gives the two estimates in
`smd:cor:coarse`, including the logarithmic error when there are many terms.
-/

namespace GRHArticle.SingularModuli

variable {p : ℕ} [hp : Fact p.Prime]

private theorem weight_one_digits (n : ℕ) :
    ((p : ℝ) - 1) * (n - (padicValNat p n.factorial : ℝ)) =
      ((p : ℝ) - 2) * n + (p.digits n).sum := by
  have h := Nat.sub_add_cancel (Nat.digit_sum_le p n)
  rw [← sub_one_mul_padicValNat_factorial] at h
  have h' : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) + (p.digits n).sum = n := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.out.one_le]
    exact_mod_cast h
  linarith

private theorem digit_sum_le_log (n : ℕ) :
    ((p.digits n).sum : ℝ) ≤ ((p : ℝ) - 1) * (1 + Real.logb p n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
    exact_mod_cast hp.out.one_le
  have hlist (l : List ℕ) (hl : ∀ d ∈ l, d < p) : l.sum ≤ (p - 1) * l.length := by
    induction l with
    | nil => simp
    | cons d l ih =>
      have hd := hl d (by simp)
      have hrest := ih (fun i hi => hl i (by simp [hi]))
      simp only [List.sum_cons, List.length_cons, Nat.mul_succ]
      omega
  have h := hlist (p.digits n) (fun _ hd => Nat.digits_lt_base hp.out.one_lt hd)
  rw [Nat.length_digits p n hp.out.one_lt hn] at h
  have hr : ((p.digits n).sum : ℝ) ≤ ((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1) := by
    rw [← Nat.cast_one, ← Nat.cast_sub hp.out.one_le]
    exact_mod_cast h
  rw [add_comm 1]
  exact hr.trans (mul_le_mul_of_nonneg_left (add_le_add_left (Real.natLog_le_logb n p) 1)
    (sub_nonneg.mpr (by exact_mod_cast hp.out.one_le)))

omit hp in
private theorem one_exceeds_exponential_threshold (hp3 : 3 ≤ p) : 1 / ((p : ℚ) - 1) < 1 := by
  have h : (3 : ℚ) ≤ p := by exact_mod_cast hp3
  rw [div_lt_one (by linarith)]
  linarith

/-- The two depth-one bounds for the article's greatest admissible index.
There is no restriction on the number of terms relative to the prime. -/
theorem sparseDiskRootBound_one_le {t : ℕ} (ht : 0 < t) (hp3 : 3 ≤ p) {hr : 1 / ((p : ℚ) - 1) < 1} :
    let B := sparseDiskRootBound p t 1 ht hr
    B ≤ ⌊((p : ℝ) - 1) / (p - 2) * (t - 1)⌋₊ ∧
    B ≤ ⌊(t : ℝ) - 1 + ((p : ℝ) - 1) / (p - 2) * (1 + Real.logb p t)⌋₊ := by
  intro B
  have hmax := (isGreatest_sparseDiskRootBound (p := p) ht (one_exceeds_exponential_threshold hp3)).1
  obtain ⟨i, hi⟩ := hmax
  change factorialWeight p 1 B ≤ factorialWeight p 1 i at hi
  simp only [factorialWeight, one_mul] at hi
  have h : (B : ℝ) - (padicValNat p B.factorial : ℝ) ≤
      (i.val : ℝ) - (padicValNat p i.val.factorial : ℝ) := by exact_mod_cast hi
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hi' : (i.val : ℝ) + 1 ≤ t := by exact_mod_cast i.isLt
  have hpos : 0 < (p : ℝ) - 2 := by linarith
  have h1 := mul_le_mul_of_nonneg_left h (show 0 ≤ (p : ℝ) - 1 by linarith)
  rw [weight_one_digits B] at h1
  have hdB : (0 : ℝ) ≤ (p.digits B).sum := by positivity
  constructor
  · apply Nat.le_floor
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    have hh := mul_le_mul_of_nonneg_left (show (i.val : ℝ) - (padicValNat p i.val.factorial : ℝ) ≤
      t - 1 by
        have hv : (0 : ℝ) ≤ padicValNat p i.val.factorial := by positivity
        linarith only [hv, hi'])
      (show 0 ≤ (p : ℝ) - 1 by linarith)
    linarith
  · apply Nat.le_floor
    rw [div_mul_eq_mul_div, ← sub_le_iff_le_add', le_div_iff₀ hpos]
    rw [weight_one_digits i.val] at h1
    have hlo : ((p.digits i.val).sum : ℝ) ≤ ((p : ℝ) - 1) * (1 + Real.logb p t) := by
      apply (digit_sum_le_log i.val).trans
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply add_le_add_right
      by_cases hi0 : i.val = 0
      · rw [hi0, Nat.cast_zero, Real.logb_zero]
        exact Real.logb_nonneg (by linarith) (by exact_mod_cast ht : (1 : ℝ) ≤ t)
      · exact Real.logb_le_logb_of_le (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hi0)
          (by exact_mod_cast i.isLt.le)
    have hh := mul_le_mul_of_nonneg_left (show (i.val : ℝ) ≤ t - 1 by linarith) hpos.le
    linarith

/-- Both upper bounds of `smd:cor:coarse` for distinct roots in a closed
depth-one disk in an algebraic normed extension of the p-adic rationals. -/
theorem encard_polynomialDiskRoots_depth_one {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] K]
    (P : Polynomial K) (hP : P ≠ 0) (a : K) (ha : a ≠ 0) (hp3 : 3 ≤ p) :
    let t : ℝ := P.support.card
    let N := {x : K | ‖x / a - 1‖ ≤ (p : ℝ)⁻¹ ∧ P.eval x = 0}.encard
    N ≤ (⌊((p : ℝ) - 1) / (p - 2) * (t - 1)⌋₊ : ℕ∞) ∧
    N ≤ (⌊t - 1 + ((p : ℝ) - 1) / (p - 2) * (1 + Real.logb p t)⌋₊ : ℕ∞) := by
  have hr := one_exceeds_exponential_threshold hp3
  have ht := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
  obtain ⟨h₁, h₂⟩ := sparseDiskRootBound_one_le ht hp3 (hr := hr)
  have h := encard_polynomialDiskRoots_le_padicAlgebraicExtension P hP a ha hr
  simpa [Real.rpow_neg_one] using And.intro (h.trans (Nat.cast_le.mpr h₁)) (h.trans (Nat.cast_le.mpr h₂))

end GRHArticle.SingularModuli
