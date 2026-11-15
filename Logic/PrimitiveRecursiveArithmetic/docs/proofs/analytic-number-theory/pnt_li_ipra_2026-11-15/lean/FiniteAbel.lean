import Mathlib

/-!
# Finite Abel summation: a small algebraic proof candidate

STATUS: UNCOMPILED. The source below is intended to prove an actual finite
algebraic identity. It makes no claim to prove PNT or an iPRA derivation.
It uses neither an added axiom nor a proof placeholder.

The recursive sums are independent of the arithmetic specification file so
that this fragment can be compiled by itself in a Mathlib environment.
-/

namespace LiPNT.FiniteAbel

def prefix (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => prefix a n + a n

def correction (a b : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 =>
      correction a b n + prefix a (n + 1) * (b n - b (n + 1))

/-- Finite summation by parts, with all endpoint terms present. -/
theorem finiteAbel (a b : ℕ → ℚ) (n : ℕ) :
    prefix (fun j => a j * b j) n =
      prefix a n * b n + correction a b n := by
  induction n with
  | zero => simp [prefix, correction]
  | succ n ih =>
      simp only [prefix, correction]
      rw [ih]
      ring

/-- The one-step recurrence is an immediate arithmetic consequence. -/
theorem weightedStep (a b : ℕ → ℚ) (n : ℕ) :
    prefix (fun j => a j * b j) (n + 1) -
      prefix (fun j => a j * b j) n = a n * b n := by
  simp [prefix]

end LiPNT.FiniteAbel
