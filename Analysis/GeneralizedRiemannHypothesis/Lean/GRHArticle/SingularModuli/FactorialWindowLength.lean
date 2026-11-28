import GRHArticle.SingularModuli.FullSupportIntervals
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# A logarithmic finite window for the full-support interval test

At depth one every sufficiently long interval crossing a given degree
passes automatically. Its starting and ending points need no search outside
a logarithmic distance from that degree.
-/

namespace GRHArticle.SingularModuli

variable {p : ℕ} [hp : Fact p.Prime]

private theorem sum_valuations_add_factorial (u d : ℕ) :
    (∑ j ∈ Finset.range d, padicValNat p (u+j+1)) + padicValNat p u.factorial =
      padicValNat p (u+d).factorial := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ,Nat.add_succ u d,Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
    simp only [Nat.succ_eq_add_one] at *
    omega

private theorem digit_sum_le_length (n : ℕ) : (p.digits n).sum ≤ (p-1)*(p.digits n).length := by
  have aux (l : List ℕ) (hl : ∀ a ∈ l, a < p) : l.sum ≤ (p-1)*l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha := hl a (by simp)
      have h := ih (fun i hi ↦ hl i (by simp [hi]))
      simp only [List.sum_cons,List.length_cons,Nat.mul_succ]
      omega
  exact aux _ (fun _ ha ↦ Nat.digits_lt_base hp.out.one_lt ha)

/-- Above a logarithmic length the full-support interval inequality at
depth one holds for every interval starting at or below `h`. -/
theorem interval_valuation_sum_lt_length_of_log {u d h : ℕ} (hu : u ≤ h) (hh : h ≠ 0)
    (hp3 : 3 ≤ p) (hlen : (p-1)*(Nat.log p h+1) < (p-2)*d) :
    (∑ j ∈ Finset.range d, padicValNat p (u+j+1)) < d := by
  have hdig : (p.digits u).sum ≤ (p-1)*(Nat.log p h+1) := by
    rw [← Nat.length_digits p h hp.out.one_lt hh]
    exact (digit_sum_le_length u).trans (Nat.mul_le_mul_left _ (Nat.le_length_digits_le p u h hu))
  have hleg (n : ℕ) : (p-1)*padicValNat p n.factorial + (p.digits n).sum = n := by
    rw [sub_one_mul_padicValNat_factorial, Nat.sub_add_cancel (Nat.digit_sum_le p n)]
  have hv := hleg (u+d)
  rw [← sum_valuations_add_factorial, Nat.mul_add] at hv
  by_contra! hs
  have hs' := Nat.mul_le_mul_left (p-1) hs
  have h' : p-1 = (p-2)+1 := by omega
  conv at hs' => lhs; rw [h',Nat.add_mul,one_mul]
  have hu' := hleg u
  omega

/-- The test for every interval crossing the degree needs only the lengths
up to the explicit logarithmic cutoff. -/
theorem sparseDiskRootBound_one_eq_pred_iff_short_intervals {h : ℕ} (hh : 0 < h) (hp3 : 3 ≤ p)
    (hb : 1 / ((p:ℚ)-1) < 1) :
    sparseDiskRootBound p h 1 hh hb = h-1 ↔
      ∀ u d : ℕ, u < h → h ≤ u+d → (p-2)*d ≤ (p-1)*(Nat.log p h+1) →
        (∑ j ∈ Finset.range d, padicValNat p (u+j+1)) < d := by
  rw [sparseDiskRootBound_eq_pred_iff_intervals]
  constructor
  · intro H u d hu hd _
    have hv := H u d hu hd
    rw [one_mul,← Nat.cast_sum] at hv
    exact_mod_cast hv
  · intro H u d hu hd
    rw [one_mul,← Nat.cast_sum]
    by_cases hlen : (p-2)*d ≤ (p-1)*(Nat.log p h+1)
    · exact_mod_cast H u d hu hd hlen
    · exact_mod_cast interval_valuation_sum_lt_length_of_log hu.le hh.ne' hp3 (lt_of_not_ge hlen)

end GRHArticle.SingularModuli
