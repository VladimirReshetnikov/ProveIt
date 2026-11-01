import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace DiophantineConsistency.ReflectedSource
variable {N : ℕ} [NeZero (N * 2011)]
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

/-- A wrapped negative offset lies beyond any support contained in 0..1004. -/
theorem source (c : ZMod (N * 2011) → ℕ) (S : Set ℕ)
    (hbound : ∀ f ∈ S, f ≤ 1004)
    (hsupport : ∀ k, k.val % 2011 ∉ S → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    {h p : ℕ} (hh : h ≤ 1004) (hp : p ≤ 985) :
    c (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))) =
      if 1005 ≤ h + p then c (b + ((h + p - 1005 : ℕ) : ZMod (N * 2011))) else 0 := by
  by_cases hv : 1005 ≤ h + p
  · rw [if_pos hv]
    congr 1
    rw [Nat.cast_sub (by omega : p ≤ 1005), Nat.cast_sub hv, Nat.cast_add]
    ring
  · rw [if_neg hv]
    apply hsupport
    intro hs
    have hl := hbound _ hs
    have hr := sub_residue (b + (h : ZMod (N * 2011))) (1005 - p)
    simp only [add_residue, Nat.add_mod, hb, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega : h < 2011)] at hr
    have hx := Nat.mod_lt
      (b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))).val
      (by decide : 0 < 2011)
    have hr' :
        (((b + (h : ZMod (N * 2011)) - ((1005 - p : ℕ) : ZMod (N * 2011))).val % 2011)
          + (1005 - p)) % 2011 = h := by
      simpa only [Nat.add_mod, Nat.mod_mod] using hr
    omega
end DiophantineConsistency.ReflectedSource
