import GowersSzemeredi.Section05

/-!
# Diameter estimates for the polynomial degree induction

Diameters of pointwise sums add. A bounded nonnegative integral multiple of a
modular coefficient has diameter controlled by its centered absolute value.
These estimates account for the top-degree term after polynomial recurrence.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Add the integral modular diameters of two functions on the same finite set. -/
theorem diameterAtMost_add_image {N : Nat} {X : Type*} [DecidableEq X]
    (A : Finset X) (f g : X → ZMod N) {s t : Nat}
    (hf : diameterAtMost (A.image f) s) (hg : diameterAtMost (A.image g) t) :
    diameterAtMost (A.image fun x => f x + g x) (s + t) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ha (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hb (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  apply Finset.mem_image.mpr
  refine ⟨⟨(i : Nat) + j, by
    change (i : Nat) + j < s + t + 1
    have hi : (i : Nat) < s + 1 := i.isLt
    have hj : (j : Nat) < t + 1 := j.isLt
    omega⟩, Finset.mem_univ _, ?_⟩
  change a + b + ((i : Nat) + (j : Nat) : Nat) * (1 : ZMod N) = f x + g x
  have hi' : a + (i : Nat) = f x := by simpa [modInterval] using hi
  have hj' : b + (j : Nat) = g x := by simpa [modInterval] using hj
  rw [← hi', ← hj']
  push_cast
  ring

/-- Real upper bounds on integral diameters are additive as well. -/
theorem diameterAtMostReal_add_image {N : Nat} {X : Type*} [DecidableEq X]
    (A : Finset X) (f g : X → ZMod N) {s t : Real}
    (hf : diameterAtMostReal (A.image f) s) (hg : diameterAtMostReal (A.image g) t) :
    diameterAtMostReal (A.image fun x => f x + g x) (s + t) := by
  obtain ⟨d, hd, hds⟩ := hf
  obtain ⟨e, he, het⟩ := hg
  refine ⟨d + e, diameterAtMost_add_image A f g hd he, ?_⟩
  push_cast
  exact add_le_add hds het

/-- Multiples with coefficients in [0,L] lie in an interval of diameter
L times the centered absolute value, for either sign of the centered lift. -/
theorem diameterAtMost_bounded_multiples {N : Nat} [NeZero N]
    {X : Type*} [DecidableEq X] (A : Finset X) (a : ZMod N)
    (w : X → Nat) (L : Nat) (hw : ∀ x, x ∈ A → w x ≤ L) :
    diameterAtMost (A.image fun x => a * (w x : ZMod N)) (L * centeredAbs a) := by
  -- the centered lift is `a` or `-a`: count up from `0`, or down from `a * L`
  obtain ⟨b, idx, hidx⟩ : ∃ b : ZMod N, ∃ idx : X → Nat, ∀ x ∈ A,
      idx x ≤ L * centeredAbs a ∧ b + (idx x : ZMod N) * 1 = a * w x := by
    have hcast := ZMod.natCast_natAbs_valMinAbs a
    unfold centeredAbs
    split at hcast
    · exact ⟨0, fun x => w x * a.valMinAbs.natAbs, fun x hx =>
        ⟨Nat.mul_le_mul_right _ (hw x hx), by rw [Nat.cast_mul, hcast]; ring⟩⟩
    · exact ⟨a * L, fun x => (L - w x) * a.valMinAbs.natAbs, fun x hx =>
        ⟨Nat.mul_le_mul_right _ (Nat.sub_le _ _), by
          rw [Nat.cast_mul, Nat.cast_sub (hw x hx), hcast]; ring⟩⟩
  refine ⟨b, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨⟨idx x, Nat.lt_succ_of_le (hidx x hx).1⟩, Finset.mem_univ _,
    (hidx x hx).2⟩

/-- Bound the top-degree term on any subset of the first u indices. -/
theorem diameterAtMost_monomial {N k u : Nat} [NeZero N]
    (A : Finset Nat) (hA : A ⊆ Finset.range u) (a : ZMod N) :
    diameterAtMost (A.image fun x : Nat => a * (x : ZMod N) ^ k)
      (u ^ k * centeredAbs a) := by
  have h := diameterAtMost_bounded_multiples A a (fun x => x ^ k) (u ^ k)
    (fun x hx => Nat.pow_le_pow_left (Finset.mem_range.mp (hA hx)).le k)
  simpa only [Nat.cast_pow] using h

end LeanProofs.GowersSzemeredi
