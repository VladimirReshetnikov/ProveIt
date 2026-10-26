import Mathlib.RingTheory.Coprime.Basic

import Mathlib.Algebra.Ring.GeomSum

import Mathlib.Algebra.Order.Ring.Abs

import Mathlib.Tactic.Linarith

import Mathlib.Tactic.Positivity

import Mathlib.Tactic.Ring

namespace AlgebraBaseline

open Finset

open scoped BigOperators

theorem isCoprime_of_congruence {J F : ℤ} (hJF : J ∣ F - 1) : IsCoprime F J := by
  simpa using IsCoprime.add_one_left_of_dvd hJF

theorem combined_dvd_iff {J F Q H C : ℤ} (hJF : J ∣ F - 1) :
    J * F ∣ Q * F + J * (H - C) ↔ J ∣ Q ∧ F ∣ H - C := by
  have hcop := isCoprime_of_congruence hJF
  constructor
  · intro h
    have hJ : J ∣ Q * F + J * (H - C) :=
      dvd_trans (show J ∣ J * F from ⟨F, rfl⟩) h
    have hF : F ∣ Q * F + J * (H - C) :=
      dvd_trans (show F ∣ J * F from ⟨J, by ring⟩) h
    have hQF : J ∣ Q * F := by
      simpa using dvd_sub hJ (show J ∣ J * (H - C) from ⟨H - C, rfl⟩)
    have hJHC : F ∣ J * (H - C) := by
      simpa using dvd_sub hF (show F ∣ Q * F from ⟨Q, by ring⟩)
    exact ⟨hcop.symm.dvd_of_dvd_mul_right hQF, hcop.dvd_of_dvd_mul_left hJHC⟩
  · rintro ⟨⟨q, hq⟩, ⟨z, hz⟩⟩
    refine ⟨q + z, ?_⟩
    rw [hq, hz]
    ring

#print axioms combined_dvd_iff

theorem geometric_identity (B : ℤ) (d : ℕ) :
    (B - 1) * (∑ i ∈ range d, B ^ i) = B ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    ring

#print axioms geometric_identity

theorem geometric_lt_two_top {B : ℤ} (hB : 2 ≤ B) (d : ℕ) :
    (∑ i ∈ range (d + 1), B ^ i) < 2 * B ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [sum_range_succ]
    have hp : 0 < B ^ d := by positivity
    have hnext : B ^ (d + 1) = B ^ d * B := pow_succ _ _
    nlinarith

#print axioms geometric_lt_two_top

theorem coordinate_gt_of_margin_pos {C K Y cap g : ℤ}
    (hK : 0 < K) (hY : 2 ≤ Y) (hcap : 0 < cap) (hg : 0 ≤ g)
    (hm : 0 < (K ^ 2 - 4 * (C - K * Y) ^ 2) * cap - 8 * g * K ^ 2) :
    K < C := by
  have hgap : 0 < K ^ 2 - 4 * (C - K * Y) ^ 2 := by
    by_contra h
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (le_of_lt hcap)
    have htail : 0 ≤ 8 * g * K ^ 2 := by positivity
    linarith
  by_contra h
  have hC : C ≤ K := by omega
  have hKY : 2 * K ≤ K * Y := by
    have := mul_le_mul_of_nonneg_left hY (le_of_lt hK)
    nlinarith
  have hCK : K ≤ -(C - K * Y) := by nlinarith
  have hsq : K ^ 2 ≤ (C - K * Y) ^ 2 := by
    have := mul_self_le_mul_self (le_of_lt hK) hCK
    nlinarith
  nlinarith [sq_nonneg K]

#print axioms coordinate_gt_of_margin_pos

end AlgebraBaseline
