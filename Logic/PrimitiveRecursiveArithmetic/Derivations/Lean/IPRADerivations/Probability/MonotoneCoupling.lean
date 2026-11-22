import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite monotone coupling

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/realization.tex`, Lemma
`lem:monotone-coupling`, cleared of denominators: the two laws are given by nondecreasing tables
`f, g : Fin R → ℕ` of `R` equally weighted rows (the sorted consecutive allocation of the fair-bit table) with
values on the integer grid `[0, K]`, and the (unnormalized) CDFs are the row counts
`F_f(t) = #{r : f r ≤ t}` (`cdf`):

* `sum_ind`, `abs_eq_sum`: "`|x − y|` is the length of the set of thresholds where `1_{x ≤ t}` and `1_{y ≤ t}`
  differ";
* `nested`, `threshold`: "At every threshold, each of the two sets of rows is an initial segment. Their
  symmetric difference therefore has mass `|F_μ(t) − F_ν(t)|`";
* `coupling`: "Interchange the two finite sums": `∑_r |f r − g r| = ∑_{t<K} |F_f(t) − F_g(t)|`, the exact
  step-function form of `I|Q_μ − Q_ν| = ∫ |F_μ − F_ν|`;
* `coupling_bound`: "The upper bound multiplies the interval length by the largest integrand value".
-/

namespace LeanProofs.IPRA.Probability.MonotoneCoupling

open Finset

/-- The threshold indicator `1_{c ≤ t}`. -/
def ind (c t : ℕ) : ℤ := if c ≤ t then 1 else 0

/-- `∑_{t<K} 1_{c ≤ t} = K − c` for `c ≤ K`. -/
theorem sum_ind {c K : ℕ} (h : c ≤ K) : ∑ t ∈ range K, ind c t = (K : ℤ) - c := by
  induction K with
  | zero =>
    obtain rfl : c = 0 := by omega
    simp
  | succ K ih =>
    rw [sum_range_succ]
    rcases Nat.lt_or_ge K c with hK | hK
    · obtain rfl : c = K + 1 := by omega
      have h₀ : ∀ t ∈ range K, ind (K + 1) t = 0 := fun t ht => by
        rw [mem_range] at ht
        unfold ind
        rw [if_neg (by omega)]
      rw [sum_eq_zero h₀]
      unfold ind
      rw [if_neg (by omega)]
      push_cast
      ring
    · rw [ih hK]
      unfold ind
      rw [if_pos hK]
      push_cast
      ring

/-- `|a − b|` counts the thresholds where `1_{a ≤ t}` and `1_{b ≤ t}` differ. -/
theorem abs_eq_sum {a b K : ℕ} (ha : a ≤ K) (hb : b ≤ K) :
    |(a : ℤ) - b| = ∑ t ∈ range K, (ind a t + ind b t - 2 * ind (max a b) t) := by
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_ind ha, sum_ind hb, sum_ind (max_le ha hb)]
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (by omega)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (by omega)]
    ring

/-- The row count `F_f(t) = #{r : f r ≤ t}`. -/
def cdf {R : ℕ} (f : Fin R → ℕ) (t : ℕ) : ℤ := ∑ r, ind (f r) t

/-- The rows below a threshold form initial segments, so the two sets are nested. -/
theorem nested {R : ℕ} {f g : Fin R → ℕ} (hf : Monotone f) (hg : Monotone g) (t : ℕ) :
    (∀ r, f r ≤ t → g r ≤ t) ∨ (∀ r, g r ≤ t → f r ≤ t) := by
  by_contra h
  rw [not_or, not_forall, not_forall] at h
  obtain ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩ := h
  rw [Classical.not_imp] at h₁ h₂
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  rcases le_total r₁ r₂ with hr | hr
  · have := hg hr
    omega
  · have := hf hr
    omega

theorem term {a b t : ℕ} (h : a ≤ t → b ≤ t) :
    ind a t + ind b t - 2 * ind (max a b) t = ind b t - ind a t := by
  unfold ind
  split_ifs <;> omega

theorem term_nonneg {a b t : ℕ} (h : a ≤ t → b ≤ t) : 0 ≤ ind b t - ind a t := by
  unfold ind
  split_ifs <;> omega

/-- At one threshold the rows where the indicators differ have mass `|F_f(t) − F_g(t)|`. -/
theorem threshold {R : ℕ} {f g : Fin R → ℕ} (hf : Monotone f) (hg : Monotone g) (t : ℕ) :
    ∑ r, (ind (f r) t + ind (g r) t - 2 * ind (max (f r) (g r)) t) = |cdf f t - cdf g t| := by
  unfold cdf
  rcases nested hf hg t with h | h
  · rw [sum_congr rfl fun r _ => term (h r), sum_sub_distrib, abs_sub_comm,
      abs_of_nonneg (by rw [← sum_sub_distrib]; exact sum_nonneg fun r _ => term_nonneg (h r))]
  · rw [sum_congr rfl fun r _ => (show ind (f r) t + ind (g r) t - 2 * ind (max (f r) (g r)) t =
        ind (f r) t - ind (g r) t by rw [add_comm, max_comm]; exact term (h r)), sum_sub_distrib,
      abs_of_nonneg (by rw [← sum_sub_distrib]; exact sum_nonneg fun r _ => term_nonneg (h r))]

/-- `lem:monotone-coupling`: `∑_r |f r − g r| = ∑_{t<K} |F_f(t) − F_g(t)|`. -/
theorem coupling {R K : ℕ} {f g : Fin R → ℕ} (hf : Monotone f) (hg : Monotone g) (hfK : ∀ r, f r ≤ K)
    (hgK : ∀ r, g r ≤ K) : ∑ r, |(f r : ℤ) - g r| = ∑ t ∈ range K, |cdf f t - cdf g t| := by
  rw [sum_congr rfl fun r _ => abs_eq_sum (hfK r) (hgK r), sum_comm]
  exact sum_congr rfl fun t _ => threshold hf hg t

/-- The coupling cost is at most the interval length times the largest CDF discrepancy. -/
theorem coupling_bound {R K : ℕ} {f g : Fin R → ℕ} (hf : Monotone f) (hg : Monotone g)
    (hfK : ∀ r, f r ≤ K) (hgK : ∀ r, g r ≤ K) {M : ℤ} (hM : ∀ t < K, |cdf f t - cdf g t| ≤ M) :
    ∑ r, |(f r : ℤ) - g r| ≤ K * M := by
  rw [coupling hf hg hfK hgK]
  calc ∑ t ∈ range K, |cdf f t - cdf g t| ≤ ∑ _t ∈ range K, M :=
        sum_le_sum fun t ht => hM t (mem_range.mp ht)
    _ = K * M := by rw [sum_const, card_range, nsmul_eq_mul]

end LeanProofs.IPRA.Probability.MonotoneCoupling
