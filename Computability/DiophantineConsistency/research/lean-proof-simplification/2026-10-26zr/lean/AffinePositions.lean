import Mathlib.Data.ZMod.Basic

/-! Standalone exact-domain pilot for the two proof replacements in
CurrentControllerPositions2011. The arithmetic data and ZMod domains are copied
literally; this file does not import the full production dependency chain. -/
namespace AdditionalLean.AffinePositions

def auxiliary : ℕ := 120199
instance : NeZero auxiliary := ⟨by decide⟩

def position (k : ℕ) (j : ZMod (auxiliary^k)) : ℕ :=
  2+(auxiliary-1)*j.val

def cell (k : ℕ) (j : ZMod (auxiliary^k)) : ZMod (auxiliary^(k+1)) :=
  (position k j : ℕ)

theorem position_ne_three (k : ℕ) (j : ZMod (auxiliary^k)) : position k j ≠ 3 := by
  change 2 + 120198 * j.val ≠ 3
  omega

theorem position_injective (k : ℕ) : Function.Injective (position k) := by
  intro i j hij
  apply ZMod.val_injective
  change 2 + 120198 * i.val = 2 + 120198 * j.val at hij
  omega

#print axioms position_ne_three
#print axioms position_injective
end AdditionalLean.AffinePositions
