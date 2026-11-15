import Mathlib.Tactic

/-!
# A small algebraic kernel for the Pell development

STATUS: source supplied for the formalization outline.  This file was not
compiled in the delivery environment, which had no Lean executable.
It contains ordinary Lean theorems, not embedded iPRA derivations.  In
particular it does not assert the general existence theorem.
-/

namespace PellIPRA

abbrev Quad := Int × Int

def norm (D : Int) (z : Quad) : Int := z.1 * z.1 - D * z.2 * z.2

def mul (D : Int) (z w : Quad) : Quad :=
  (z.1 * w.1 + D * z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def conj (z : Quad) : Quad := (z.1, -z.2)

theorem norm_mul (D : Int) (z w : Quad) :
    norm D (mul D z w) = norm D z * norm D w := by
  simp only [norm, mul]
  ring

theorem mul_assoc (D : Int) (z w v : Quad) :
    mul D (mul D z w) v = mul D z (mul D w v) := by
  apply Prod.ext <;> simp only [mul] <;> ring

theorem mul_comm (D : Int) (z w : Quad) : mul D z w = mul D w z := by
  apply Prod.ext <;> simp only [mul] <;> ring

theorem mul_conj (D : Int) (z : Quad) :
    mul D z (conj z) = (norm D z, 0) := by
  apply Prod.ext <;> simp only [mul, conj, norm] <;> ring

def power (D : Int) (z : Quad) : Nat → Quad
  | 0 => (1, 0)
  | n + 1 => mul D (power D z n) z

theorem power_zero (D : Int) (z : Quad) : power D z 0 = (1, 0) := rfl

theorem power_succ (D : Int) (z : Quad) (n : Nat) :
    power D z (n + 1) = mul D (power D z n) z := rfl

theorem norm_power (D : Int) (z : Quad) (n : Nat) :
    norm D (power D z n) = norm D z ^ n := by
  induction n with
  | zero => simp [power, norm]
  | succ n ih => simp [power, norm_mul, ih, pow_succ]

theorem norm_one_power (D : Int) (z : Quad) (hz : norm D z = 1) (n : Nat) :
    norm D (power D z n) = 1 := by
  rw [norm_power, hz, one_pow]

theorem power_add (D : Int) (z : Quad) (m n : Nat) :
    power D z (m + n) = mul D (power D z m) (power D z n) := by
  induction n with
  | zero => simp [power, mul]
  | succ n ih => simpa [Nat.add_succ, power, ih] using
      mul_assoc D (power D z m) (power D z n) z

/-- The growth constants in the finite existence argument. -/
def cBound (D : Nat) : Nat := 2 * D + 1
def signatureBound (D : Nat) : Nat := 2 * cBound D ^ 3
def coordinateBound (D : Nat) : Nat :=
  (D + 2) ^ 2 * cBound D ^ (2 * (signatureBound D + 1))

/-- Smaller bounds from the finite continued-fraction construction. -/
def cfStateBound (D : Nat) : Nat := 2 * Nat.sqrt D * (Nat.sqrt D + 1)
def cfCoordinateBound (D : Nat) : Nat :=
  (2 * Nat.sqrt D + 1) ^ (2 * cfStateBound D)

/-- Additive natural-number form avoids truncated subtraction. -/
def Pell (D x y : Nat) : Prop := x * x = D * y * y + 1

/-- Finite bounded specification; this is a definition, not an asserted theorem. -/
def BoundedExistence (D : Nat) : Prop :=
  ∃ x ≤ cfCoordinateBound D, ∃ y ≤ cfCoordinateBound D,
    0 < y ∧ Pell D x y

/-- Correctness required of an explicit Skolem pair. -/
def SolverCorrect (solver : Nat → Nat × Nat) : Prop :=
  ∀ D, 2 ≤ D → Nat.sqrt D * Nat.sqrt D ≠ D →
    let z := solver D
    z.1 ≤ cfCoordinateBound D ∧ z.2 ≤ cfCoordinateBound D ∧
      0 < z.2 ∧ Pell D z.1 z.2

end PellIPRA

#print axioms PellIPRA.norm_mul
#print axioms PellIPRA.norm_power
#print axioms PellIPRA.power_add
