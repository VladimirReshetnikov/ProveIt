import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq

/-!
The three definitions below are verbatim copies of the definitions in
NativeCyclicRotation.lean at ProveIt revision
9d9d1123b39927d30363f1dcd53c23f0575c30ee, in a separate namespace.
This file checks the proof kernel without importing stale project objects.
-/
namespace ProofSimplification.RotationPeriod

variable {n : ℕ}

def rotate (c : ZMod n → ℕ) (t k : ZMod n) : ℕ := c (k - t)

def shiftDigits (ρ s : ℕ) (c : ZMod n → ℕ) (k : ZMod n) : ℕ :=
  (s * c k) % ρ + (s * c (k - 1)) / ρ

def binaryRotation (v W : ℕ) (c : ZMod n → ℕ) : ZMod n → ℕ :=
  rotate (shiftDigits (2 ^ v) (2 ^ (W % v)) c) ((W / v : ℕ) : ZMod n)

/-- Binary rotation depends only on the exponent modulo the complete bit
window. No boundedness or Boolean hypothesis is needed; zero moduli and
zero digit width are included by the total definitions. -/
theorem binaryRotation_mod (v W : ℕ) (c : ZMod n → ℕ) :
    binaryRotation v (W % (v * n)) c = binaryRotation v W c := by
  simp only [binaryRotation, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self, ZMod.natCast_mod]

/-- Congruent natural exponents give literally equal digit functions. -/
theorem binaryRotation_modEq (v W W' : ℕ) (c : ZMod n → ℕ)
    (h : W ≡ W' [MOD v * n]) :
    binaryRotation v W c = binaryRotation v W' c := by
  rw [← binaryRotation_mod v W c, ← binaryRotation_mod v W' c, h]

/-- The direct low-overhead replacement needed by whole-cell rephasing. -/
theorem binaryRotation_whole_eq {v : ℕ} (hv : 0 < v)
    (c : ZMod n → ℕ) (s t : ℕ)
    (h : (s : ZMod n) = (t : ZMod n)) :
    binaryRotation v (v * s) c = binaryRotation v (v * t) c := by
  simp only [binaryRotation, Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ hv, h]

/-- Exact whole-cell specialization at the production radix width and
cell length, with the source's physical shift equality as the premise. -/
theorem rotation_eq_47_2011 {N : ℕ} (c : ZMod (N * 2011) → ℕ)
    (s t : ℕ)
    (h : ((2011 * s : ℕ) : ZMod (N * 2011)) =
      ((2011 * t : ℕ) : ZMod (N * 2011))) :
    binaryRotation 47 (47 * (2011 * s)) c =
      binaryRotation 47 (47 * (2011 * t)) c := by
  simp only [binaryRotation, Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ (by decide : 0 < 47), h]

example (v W : ℕ) (c : ZMod 0 → ℕ) :
    binaryRotation v (W % (v * 0)) c = binaryRotation v W c :=
  binaryRotation_mod v W c

example (W : ℕ) (c : ZMod n → ℕ) :
    binaryRotation 0 (W % (0 * n)) c = binaryRotation 0 W c :=
  binaryRotation_mod 0 W c

example (c : ZMod 1 → ℕ) :
    binaryRotation 47 188 c = binaryRotation 47 47 c := by
  apply binaryRotation_modEq
  decide

#print axioms binaryRotation_mod
#print axioms binaryRotation_modEq
#print axioms binaryRotation_whole_eq
#print axioms rotation_eq_47_2011

end ProofSimplification.RotationPeriod
