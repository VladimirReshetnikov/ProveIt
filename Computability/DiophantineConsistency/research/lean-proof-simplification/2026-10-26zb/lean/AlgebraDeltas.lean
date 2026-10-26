import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace AlgebraDeltas
open Finset
open scoped BigOperators

theorem combined_dvd_iff {J F Q H C : ℤ} (hJF : J ∣ F - 1) :
    J * F ∣ Q * F + J * (H - C) ↔ J ∣ Q ∧ F ∣ H - C := by
  have hcop : IsCoprime F J := by simpa using IsCoprime.add_one_left_of_dvd hJF
  constructor
  · intro h
    exact ⟨hcop.symm.dvd_of_dvd_mul_right
      ((dvd_add_left (dvd_mul_right J _)).mp ((dvd_mul_right J F).trans h)),
      hcop.dvd_of_dvd_mul_left
      ((dvd_add_right (dvd_mul_left F Q)).mp ((dvd_mul_left F J).trans h))⟩
  · rintro ⟨hQ, hT⟩
    exact dvd_add (mul_dvd_mul_right hQ F) (mul_dvd_mul_left J hT)

theorem geometric_identity (B : ℤ) (d : ℕ) :
    (B - 1) * (∑ i ∈ range d, B ^ i) = B ^ d - 1 :=
  mul_geom_sum B d

theorem geometric_lt_two_top {B : ℤ} (hB : 2 ≤ B) (d : ℕ) :
    (∑ i ∈ range (d + 1), B ^ i) < 2 * B ^ d := by
  have hg := geometric_identity B d
  have hs : 0 ≤ ∑ i ∈ range d, B ^ i := sum_nonneg (fun _ _ => by positivity)
  have h := mul_le_mul_of_nonneg_right (show 1 ≤ B - 1 by omega) hs
  rw [sum_range_succ]
  nlinarith


/-- Direct interval consequence of the positive quadratic margin. -/
theorem coordinate_gt_of_margin_pos {C K Y cap g : ℤ}
    (hK : 0 < K) (hY : 2 ≤ Y) (hcap : 0 < cap) (hg : 0 ≤ g)
    (hm : 0 < (K ^ 2 - 4 * (C - K * Y) ^ 2) * cap - 8 * g * K ^ 2) :
    K < C := by
  have hgap : 0 < K ^ 2 - 4 * (C - K * Y) ^ 2 := by
    apply (mul_pos_iff_of_pos_right hcap).mp
    exact lt_of_lt_of_le hm (sub_le_self _ (by positivity))
  have hwindow := abs_lt_of_sq_lt_sq' (a := 2 * (C - K * Y))
    (b := K) (by nlinarith only [hgap]) hK.le
  have hKY := mul_le_mul_of_nonneg_left hY hK.le
  nlinarith only [hwindow.1, hKY, hK]

#print axioms coordinate_gt_of_margin_pos

#print axioms combined_dvd_iff
#print axioms geometric_identity
#print axioms geometric_lt_two_top
end AlgebraDeltas
