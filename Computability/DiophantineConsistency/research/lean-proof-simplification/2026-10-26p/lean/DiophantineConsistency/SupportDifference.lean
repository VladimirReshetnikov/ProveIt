import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

/-! Translation-invariant support separation. The certificate concerns
    the residue group, not truncated natural subtraction. -/
namespace DiophantineConsistency.SupportDifference

def differences {G : Type*} [Sub G] (S : Set G) : Set G :=
  {d | ∃ a ∈ S, ∃ b ∈ S, d = b - a}

/-- A projection may merge physical positions. Only the projected support
and the actual projected displacement enter this certificate. -/
theorem translated_pair_zero {A B R : Type*} [AddCommGroup A] [AddCommGroup B] [Zero R]
    (π : A →+ B) (S : Set B) (f : A → R) (t : A)
    (hsupport : ∀ x, π (x - t) ∉ S → f x = 0)
    {x y δ : A} (hxy : y = x + δ) (hδ : π δ ∉ differences S) :
    f x = 0 ∨ f y = 0 := by
  classical
  by_cases hx : π (x - t) ∈ S
  · by_cases hy : π (y - t) ∈ S
    · exact False.elim (hδ ⟨π (x - t), hx, π (y - t), hy, by
        rw [← map_sub, hxy]
        congr 1
        abel⟩)
    · exact Or.inr (hsupport y hy)
  · exact Or.inl (hsupport x hx)

/-- Quotienting a cyclic word by its cell length is a ring homomorphism. -/
def residue {N L : ℕ} : ZMod (N * L) →+* ZMod L :=
  ZMod.castHom (Nat.dvd_mul_left L N) (ZMod L)

theorem residue_val {N L : ℕ} [NeZero (N * L)] (k : ZMod (N * L)) :
    (residue k).val = k.val % L := by
  simp only [residue, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

end DiophantineConsistency.SupportDifference
