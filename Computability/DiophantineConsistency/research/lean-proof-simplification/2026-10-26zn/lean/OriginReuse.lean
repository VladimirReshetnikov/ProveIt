import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IrreducibleDef

/-! Scoped exact-dependency check for origin reuse. The lowSupport definition,
    support bound, and three source lemmas below are extracted unchanged from
    pinned production source, within this isolated namespace. The new origin
    theorem is generic in the same supported word and aligned base. -/
namespace AdditionalOriginReuse
open scoped BigOperators
set_option Elab.async false
irreducible_def lowSupport : Finset ℕ := Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004}


theorem support_le {f : ℕ} (hf : f ∈ lowSupport) : f ≤ 1004 := by
  rw [lowSupport_def] at hf
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    Finset.mem_singleton] at hf
  omega

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

/-- A negative same-cell offset wraps into unsupported residues1006..2010.
Otherwise the source is exactly the nonnegative offset h+p−1005. -/
theorem reflected_source (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
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
    have hl := support_le hs
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


/-- New proof core: offset zero is already inside the established low-field theorem. -/
theorem origin_reflected_zero_new (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (p : ℕ) (hp : p ≤ 985) :
    c (b - ((1005 - p : ℕ) : ZMod (N * 2011))) = 0 := by
  simpa only [Nat.cast_zero, add_zero, if_neg (by omega : ¬ 1005 ≤ 0 + p)] using
    reflected_source c hsupport b hb (h := 0) (p := p) (by decide) hp

section Stencil
variable {E : Type*} [Fintype E]
variable (position weight : E → ℕ) (position_le : ∀ e, position e ≤ 985)

def reflected (c : ZMod (N * 2011) → ℕ) (k : ZMod (N * 2011)) : ℕ :=
  ∑ e : E, 2 * weight e * c (k - ((1005 - position e : ℕ) : ZMod (N * 2011)))

include position_le

/-- Generic reflected sum vanishes at zero offset, using the same proved source API. -/
theorem reflected_zero_at_origin (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    reflected position weight c b = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  rw [origin_reflected_zero_new c hsupport b hb _ (position_le e), mul_zero]

/-- The 3 bare taps are exactly those in the existing convolution identity. -/
theorem convolution_origin_zero_new (c : ZMod (N * 2011) → ℕ)
    (hsupport : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0)
    (h18 : c (b - 18) = 0) (h2020 : c (b - 2020) = 0)
    (h1004 : c (b - 1004) = 0) :
    c (b - 18) + c (b - 2020) + reflected position weight c b + c (b - 1004) = 0 := by
  rw [h18, h2020, h1004, reflected_zero_at_origin position weight position_le c hsupport b hb]

end Stencil
#print axioms origin_reflected_zero_new
#print axioms reflected_zero_at_origin
#print axioms convolution_origin_zero_new
end AdditionalOriginReuse
