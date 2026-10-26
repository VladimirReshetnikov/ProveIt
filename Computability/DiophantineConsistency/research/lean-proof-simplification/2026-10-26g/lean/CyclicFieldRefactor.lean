import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-!
Low-level cyclic-field lemmas suitable for extraction before CurrentClause2011.
The ambient modulus remains N * L. Only the field residue forgets whole cells.
-/
namespace DiophantineConsistency.RefactorCyclicField

variable {N L : ℕ} [NeZero (N * L)]

theorem addition_residue (b : ZMod (N * L)) (e : ℕ) :
    (b + (e : ZMod (N * L))).val % L = (b.val + e) % L := by
  have hh : (((b + (e : ZMod (N * L))).val : ℕ) : ZMod (N * L)) =
      ((b.val + e : ℕ) : ZMod (N * L)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, Nat.mul_comm _ _⟩

theorem subtraction_residue (k : ZMod (N * L)) (t : ℕ) :
    ((k - (t : ZMod (N * L))).val + t) % L = k.val % L := by
  have hh : (((k - (t : ZMod (N * L))).val + t : ℕ) : ZMod (N * L)) =
      (k.val : ZMod (N * L)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hh).of_dvd ⟨N, Nat.mul_comm _ _⟩

/-- No upper bound on the source offset or temporal shift is needed. -/
theorem source_residue (hL : 0 < L) (b : ZMod (N * L))
    (hb : b.val % L = 0) (e t : ℕ) :
    (b + (e : ZMod (N * L)) - (t : ZMod (N * L))).val % L =
      (L + e - t % L) % L := by
  have hsum :
      (b + (e : ZMod (N * L)) - (t : ZMod (N * L))).val + t ≡ e [MOD L] := by
    change _ % L = e % L
    rw [subtraction_residue, addition_residue, Nat.add_mod, hb,
      Nat.zero_add, Nat.mod_mod]
  have hrem : (L + e - t % L) + t ≡ e [MOD L] := by
    calc
      _ ≡ (L + e - t % L) + t % L [MOD L] := (Nat.mod_modEq t L).symm.add_left _
      _ = L + e := Nat.sub_add_cancel (by have := Nat.mod_lt t hL; omega)
      _ ≡ e [MOD L] := by simp [Nat.ModEq]
  exact Nat.ModEq.add_right_cancel' t (hsum.trans hrem.symm)

theorem zero_outside_support (hL : 0 < L) (S : Finset ℕ)
    (c : ZMod (N * L) → ℕ)
    (hc : ∀ k, k.val % L ∉ S → c k = 0)
    (b : ZMod (N * L)) (hb : b.val % L = 0) (e t : ℕ)
    (hnot : (L + e - t % L) % L ∉ S) :
    c (b + (e : ZMod (N * L)) - (t : ZMod (N * L))) = 0 := by
  apply hc
  rwa [source_residue hL b hb e t]

#print axioms source_residue
#print axioms zero_outside_support

end DiophantineConsistency.RefactorCyclicField
