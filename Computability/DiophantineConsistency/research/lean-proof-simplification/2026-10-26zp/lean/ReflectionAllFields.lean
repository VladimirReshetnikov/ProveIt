import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The reflection source formula does not need a low-field hypothesis

This standalone proof uses the actual width 2011, reflection pivot 1005,
and source support ceiling 1004. It does not import the production project.
The production helper `CurrentReflectedGeometry2011.reflected_source`
assumes h <= 1004; the proof below works for every natural h. Its coefficient
position bound can also be weakened from p <= 985 to p <= 1005.

The support condition here uses only the consequence of the production
`lowSupport` hypothesis needed by the proof. That adaptation must be checked
when integrating with the real module. No source_le, reflected_lt, or
low-field carry bound is generalized here.
-/

namespace ReflectionAllFields

open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

/-- The exact production support premise supplies the weaker interval premise. -/
theorem support_interval_of_sparse (S : Finset ℕ)
    (hS : ∀ e ∈ S, e ≤ 1004) (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, k.val % 2011 ∉ S → c k = 0) :
    ∀ k, 1004 < k.val % 2011 → c k = 0 := by
  intro k hk
  apply hc k
  intro he
  exact Nat.not_le_of_gt hk (hS _ he)

private theorem add_residue (b : ZMod (N * 2011)) (e : ℕ) :
    (b + (e : ZMod (N * 2011))).val % 2011 = (b.val + e) % 2011 := by
  have hh : (((b + (e : ZMod (N * 2011))).val : ℕ) : ZMod (N * 2011)) =
      ((b.val + e : ℕ) : ZMod (N * 2011)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

private theorem sub_residue (k : ZMod (N * 2011)) (e : ℕ) :
    ((k - (e : ZMod (N * 2011))).val + e) % 2011 = k.val % 2011 := by
  have hh : (((k - (e : ZMod (N * 2011))).val + e : ℕ) : ZMod (N * 2011)) =
      (k.val : ZMod (N * 2011)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, by ring⟩

/-- The full source formula, with no bound on the output offset h. -/
theorem reflected_source_all (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, 1004 < k.val % 2011 → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (h p : ℕ) (hp : p ≤ 1005) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      if 1005 ≤ h + p then
        c (b + ((h + p - 1005 : ℕ) : ZMod (N * 2011))) else 0 := by
  by_cases hv : 1005 ≤ h + p
  · rw [if_pos hv]
    congr 1
    rw [Nat.cast_sub hp, Nat.cast_sub hv, Nat.cast_add]
    ring
  · rw [if_neg hv]
    apply hsupport
    have hr := sub_residue (b + (h : ZMod (N * 2011))) (1005 - p)
    simp only [add_residue, Nat.add_mod, hb, zero_add, Nat.mod_mod] at hr
    omega

/-- Retain the old low-field interface as a wrapper, if compatibility is needed. -/
theorem reflected_source_low (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, 1004 < k.val % 2011 → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h p : ℕ} (_hh : h ≤ 1004) (hp : p ≤ 985) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      if 1005 ≤ h + p then
        c (b + ((h + p - 1005 : ℕ) : ZMod (N * 2011))) else 0 :=
  reflected_source_all c hsupport b hb h p (by omega)

/-- High-field specialization: the guard is automatically true. -/
theorem reflected_source_high (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, 1004 < k.val % 2011 → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h p : ℕ} (hh : 1005 ≤ h) (hp : p ≤ 1005) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      c (b + ((h - 1005 + p : ℕ) : ZMod (N * 2011))) := by
  rw [reflected_source_all c hsupport b hb h p hp, if_pos (by omega)]
  rw [show h + p - 1005 = h - 1005 + p from by omega]

/-- The same all-offset normal form lifts once through the finite reflected sum. -/
theorem reflected_sum_all {ι : Type*} [Fintype ι]
    (weight position : ι → ℕ) (hp : ∀ e, position e ≤ 1005)
    (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, 1004 < k.val % 2011 → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (h : ℕ) :
    (∑ e, weight e *
      c (b + (h : ZMod (N * 2011)) - ((1005 - position e : ℕ) : ZMod (N * 2011)))) =
      ∑ e, if 1005 ≤ h + position e then
        weight e * c (b + ((h + position e - 1005 : ℕ) : ZMod (N * 2011))) else 0 := by
  apply Finset.sum_congr rfl
  intro e _
  rw [reflected_source_all c hsupport b hb h (position e) (hp e)]
  split_ifs <;> simp only [mul_zero]

/-- Low-field compatibility at the sum level. -/
theorem reflected_sum_low {ι : Type*} [Fintype ι]
    (weight position : ι → ℕ) (hp : ∀ e, position e ≤ 985)
    (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, 1004 < k.val % 2011 → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h : ℕ} (_hh : h ≤ 1004) :
    (∑ e, weight e *
      c (b + (h : ZMod (N * 2011)) - ((1005 - position e : ℕ) : ZMod (N * 2011)))) =
      ∑ e, if 1005 ≤ h + position e then
        weight e * c (b + ((h + position e - 1005 : ℕ) : ZMod (N * 2011))) else 0 :=
  reflected_sum_all weight position (fun e => (hp e).trans (by decide)) c hsupport b hb h

/- Boundary and large-offset checks use the same theorem, not a second model. -/

example (c : ZMod (1 * 2011) → ℕ)
    (hc : ∀ k, 1004 < k.val % 2011 → c k = 0) :
    c ((19 : ZMod (1 * 2011)) - 20) = 0 := by
  simpa using reflected_source_all c hc 0 (by decide) 19 985 (by decide)

example (c : ZMod (1 * 2011) → ℕ)
    (hc : ∀ k, 1004 < k.val % 2011 → c k = 0) :
    c ((20 : ZMod (1 * 2011)) - 20) = c 0 := by
  simpa using reflected_source_all c hc 0 (by decide) 20 985 (by decide)

example (c : ZMod (1 * 2011) → ℕ)
    (hc : ∀ k, 1004 < k.val % 2011 → c k = 0) :
    c (((203109 : ℕ) : ZMod (1 * 2011)) - 1005) =
      c ((202104 : ℕ) : ZMod (1 * 2011)) := by
  simpa using reflected_source_all c hc 0 (by decide) 203109 0 (by decide)

example (c : ZMod (1 * 2011) → ℕ)
    (hc : ∀ k, 1004 < k.val % 2011 → c k = 0) :
    c ((0 : ZMod (1 * 2011)) - ((1005 - 1005 : ℕ) : ZMod (1 * 2011))) = c 0 :=
  reflected_source_all c hc 0 (by decide) 0 1005 (by decide)

/-- The input-position guard cannot be removed: truncated subtraction changes. -/
example :
    (if ((0 : ZMod 2011) - ((1005 - 1006 : ℕ) : ZMod 2011)) = 0 then 1 else 0 : ℕ) ≠
    (if ((0 : ZMod 2011) + ((0 + 1006 - 1005 : ℕ) : ZMod 2011)) = 0 then 1 else 0 : ℕ) := by
  decide

#print axioms reflected_source_all
#print axioms support_interval_of_sparse
#print axioms reflected_source_low
#print axioms reflected_source_high
#print axioms reflected_sum_all
#print axioms reflected_sum_low

end ReflectionAllFields
