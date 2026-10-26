import Diophantine.Common.Pell
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

/-!
A finite bound for a Pell divisibility witness. Only the m²+1 residue
pairs at indices 0,...,m² are used. This is a standard-natural arithmetic
theorem, not an object-language HA derivation.
-/
namespace DiophantineConsistency.BoundedPellDivisibility

open Pell Diophantine

variable {A : ℕ} (hA : 1 < A)

/-- Equal residue pairs subtract to a zero second coordinate. -/
theorem dvd_yn_sub_of_pair_eq {m s t : ℕ} (hst : s ≤ t)
    (hx : (xn hA s : ZMod m) = (xn hA t : ZMod m))
    (hy : (yn hA s : ZMod m) = (yn hA t : ZMod m)) :
    m ∣ yn hA (t - s) := by
  have hz := yz_sub hA hst
  simp only [xz, yz] at hz
  have hzero : ((yn hA (t - s) : ℤ) : ZMod m) = 0 := by
    rw [hz]
    push_cast
    rw [hx, hy]
    ring
  rw [Int.cast_natCast] at hzero
  exact (ZMod.natCast_eq_zero_iff _ _).1 hzero

/-- Finite pigeonhole on the literal prefix of length m²+1. -/
theorem residue_pair_collision {m : ℕ} (hm : 0 < m) :
    ∃ s t : ℕ, s < t ∧ t ≤ m ^ 2 ∧
      (xn hA s : ZMod m) = (xn hA t : ZMod m) ∧
      (yn hA s : ZMod m) = (yn hA t : ZMod m) := by
  letI : NeZero m := ⟨hm.ne'⟩
  let f : Fin (m ^ 2 + 1) → ZMod m × ZMod m :=
    fun j => ((xn hA j.val : ZMod m), (yn hA j.val : ZMod m))
  have hcard : Fintype.card (ZMod m × ZMod m) <
      Fintype.card (Fin (m ^ 2 + 1)) := by
    simp [pow_two]
  obtain ⟨s, t, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hneval : s.val ≠ t.val := fun h => hne (Fin.ext h)
  have hp := Prod.mk.inj heq
  change (xn hA s.val : ZMod m) = (xn hA t.val : ZMod m) ∧
    (yn hA s.val : ZMod m) = (yn hA t.val : ZMod m) at hp
  rcases lt_or_gt_of_ne hneval with hst | hts
  · exact ⟨s.val, t.val, hst, by omega, hp⟩
  · exact ⟨t.val, s.val, hts, by omega, hp.1.symm, hp.2.symm⟩

/-- Every positive modulus divides a positive Pell ordinate whose index
is at most its square. No unbounded existence theorem is used. -/
theorem exists_dvd_yn_le_square {m : ℕ} (hm : 0 < m) :
    ∃ k : ℕ, 0 < k ∧ k ≤ m ^ 2 ∧ m ∣ yn hA k := by
  obtain ⟨s, t, hst, ht, hx, hy⟩ := residue_pair_collision hA hm
  exact ⟨t - s, Nat.sub_pos_of_lt hst, (Nat.sub_le _ _).trans ht,
    dvd_yn_sub_of_pair_eq hA hst.le hx hy⟩

/-- The exact positive strong seed used before the secondary auxiliary
construction, now with a bound on its fresh index. -/
theorem strong_seed {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    ∃ k i : ℕ, 0 < k ∧ k ≤ (b * c ^ 2) ^ 2 ∧ 0 < i ∧
      yn hA k = b * i * c ^ 2 ∧
      (0 : ℤ) < xn hA k ∧
      (xn hA k : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) *
        ((b : ℤ) * i * (c : ℤ) ^ 2) ^ 2 = 1 := by
  obtain ⟨k, hk, hbound, i, hi⟩ :=
    exists_dvd_yn_le_square hA (show 0 < b * c ^ 2 by positivity)
  have hypos : 0 < yn hA k := by
    have h := strictMono_y hA hk
    simpa only [yn_zero] using h
  have hi0 : 0 < i := by
    by_contra hn
    have : i = 0 := by omega
    rw [this, mul_zero] at hi
    omega
  have hi' : yn hA k = b * i * c ^ 2 := by rw [hi]; ring
  have hA2 : 1 ≤ A * A := by nlinarith
  have hnorm := congrArg (fun n : ℕ => (n : ℤ)) (χ_sq hA k)
  simp only [χ, ψ] at hnorm
  push_cast [Nat.cast_sub hA2] at hnorm
  have hiZ := congrArg (fun n : ℕ => (n : ℤ)) hi'
  push_cast at hiZ
  refine ⟨k, i, hk, hbound, hi0, hi', ?_, ?_⟩
  · exact_mod_cast (show 0 < xn hA k from x_pos hA k)
  · rw [hiZ] at hnorm
    nlinarith only [hnorm]

/-- Specialization to the fixed outer rank in `ThirteenFreshSeed`.
Only positivity of that rank is required; rank modulo four is used later. -/
theorem strong_seed_at_rank {R b : ℕ} (hR : 0 < R) (hb : 0 < b) :
    ∃ k i : ℕ, 0 < k ∧ k ≤ (b * yn hA R ^ 2) ^ 2 ∧ 0 < i ∧
      yn hA k = b * i * yn hA R ^ 2 ∧
      (0 : ℤ) < xn hA k ∧
      (xn hA k : ℤ) ^ 2 - ((A : ℤ) ^ 2 - 1) *
        ((b : ℤ) * i * (yn hA R : ℤ) ^ 2) ^ 2 = 1 := by
  apply strong_seed hA hb
  have h := strictMono_y hA hR
  simpa only [yn_zero] using h

end DiophantineConsistency.BoundedPellDivisibility
