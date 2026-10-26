import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Consecutive modular coordinates realize every coprime-length sum

This is the interval-coordinate step in the ordinary controller argument.
It constructs an actual finite subset of ZMod T; it does not classify any
power orbit, perform CRT, or assert a safe mutation of arithmetic witnesses.
-/

namespace DiophantineConsistency.ControllerIntervalSums

open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

/-- A finite interval in the cyclic group, including intervals crossing zero. -/
def interval {T : ℕ} (start : ZMod T) (a : ℕ) : Finset (ZMod T) :=
  (Finset.range a).image (fun j : ℕ => start+(j : ZMod T))

/-- Distinct bounded natural coordinates stay distinct after translation. -/
theorem interval_injOn {T : ℕ} [NeZero T] (start : ZMod T) (a : ℕ) (ha : a ≤ T) :
    Set.InjOn (fun j : ℕ => start+(j : ZMod T)) (Finset.range a) := by
  intro j hj k hk he
  exact ((ZMod.natCast_eq_natCast_iff j k T).mp (add_left_cancel he)).eq_of_lt_of_lt
    ((Finset.mem_range.mp hj).trans_le ha) ((Finset.mem_range.mp hk).trans_le ha)

theorem interval_card {T : ℕ} [NeZero T] (start : ZMod T) (a : ℕ) (ha : a ≤ T) :
    (interval start a).card = a := by
  rw [interval,Finset.card_image_of_injOn (interval_injOn start a ha),Finset.card_range]

/-- The triangular term is evaluated in Nat before casting. In particular,
this formula never divides by2 in ZMod T and also applies to even T. -/
theorem interval_sum {T : ℕ} [NeZero T] (start : ZMod T) (a : ℕ) (ha : a ≤ T) :
    (∑ z ∈ interval start a, z) = (a : ZMod T)*start+((a*(a-1)/2 : ℕ) : ZMod T) := by
  rw [interval,Finset.sum_image (interval_injOn start a ha),Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [← Nat.cast_sum,Finset.sum_range_id]

/-- An explicit starting coordinate, using the inverse of the actual unit a. -/
def startFor {T : ℕ} (a : ℕ) (h : Nat.Coprime a T) (u : ZMod T) : ZMod T :=
  ((ZMod.unitOfCoprime a h)⁻¹ : (ZMod T)ˣ) *
    (u-((a*(a-1)/2 : ℕ) : ZMod T))

/-- The coefficient equation is solved explicitly, including the zero ring T=1. -/
theorem startFor_equation {T : ℕ} (a : ℕ) (h : Nat.Coprime a T) (u : ZMod T) :
    (a : ZMod T)*startFor a h u+((a*(a-1)/2 : ℕ) : ZMod T) = u := by
  change (ZMod.unitOfCoprime a h : ZMod T) *
    (((ZMod.unitOfCoprime a h)⁻¹ : (ZMod T)ˣ) *
      (u-((a*(a-1)/2 : ℕ) : ZMod T)))+((a*(a-1)/2 : ℕ) : ZMod T) = u
  rw [Units.mul_inv_cancel_left,sub_add_cancel]

/-- A concrete target-dependent subset, rather than an assumed subset witness. -/
def targetInterval {T : ℕ} (a : ℕ) (h : Nat.Coprime a T) (u : ZMod T) : Finset (ZMod T) :=
  interval (startFor a h u) a

theorem targetInterval_card {T : ℕ} [NeZero T] (a : ℕ) (h : Nat.Coprime a T)
    (ha : a ≤ T) (u : ZMod T) : (targetInterval a h u).card = a :=
  interval_card (startFor a h u) a ha

theorem targetInterval_sum {T : ℕ} [NeZero T] (a : ℕ) (h : Nat.Coprime a T)
    (ha : a ≤ T) (u : ZMod T) : (∑ z ∈ targetInterval a h u, z) = u := by
  rw [targetInterval,interval_sum _ a ha,startFor_equation]

/-- Every target is the sum of a distinct consecutive cyclic coordinates. -/
theorem exists_interval_sum {T : ℕ} [NeZero T] (a : ℕ) (h : Nat.Coprime a T)
    (ha : a ≤ T) (u : ZMod T) :
    ∃ start : ZMod T, (interval start a).card = a ∧ (∑ z ∈ interval start a, z) = u :=
  ⟨startFor a h u,targetInterval_card a h ha u,targetInterval_sum a h ha u⟩

/-- The finite subset interface used after a separate orbit-coordinate bijection. -/
theorem exists_subset_card_sum {T : ℕ} [NeZero T] (a : ℕ) (h : Nat.Coprime a T)
    (ha : a ≤ T) (u : ZMod T) :
    ∃ s : Finset (ZMod T), s.card = a ∧ (∑ z ∈ s, z) = u :=
  ⟨targetInterval a h u,targetInterval_card a h ha u,targetInterval_sum a h ha u⟩

end DiophantineConsistency.ControllerIntervalSums
