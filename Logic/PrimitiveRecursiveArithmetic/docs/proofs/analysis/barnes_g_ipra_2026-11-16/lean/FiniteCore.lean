import Std

/-!
# Finite Barnes-G core

This file is intentionally elementary.  It isolates the exact natural-number
content of the Barnes G-function.  It imports only `Std`; the intended next
step is to translate the same recursors and inductions to
`LeanProofs.ConciseIPRA.PR` and `Prf PRAAx`.

The artifact-building environment did not contain a Lean executable, so this
file was not compiled here.  It contains no `axiom`, `sorry`, or `admit`.
-/

namespace BarnesGIPRA.FiniteCore

/-- Structurally recursive factorial. -/
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

/-- Shifted positive-integer Barnes values: `gPos n = G(n+1)`. -/
def gPos : Nat → Nat
  | 0 => 1
  | n + 1 => fac n * gPos n

/-- `0! 1! ... n!`; the recurrence is chosen to mirror `gPos`. -/
def superfac : Nat → Nat
  | 0 => 1
  | n + 1 => superfac n * fac (n + 1)

/-- Hyperfactorial `H(n)=1^1 2^2 ... n^n`. -/
def hyperfac : Nat → Nat
  | 0 => 1
  | n + 1 => hyperfac n * (n + 1) ^ (n + 1)

/-- Odd double factorial `(2i-1)!!`. -/
def oddDF : Nat → Nat
  | 0 => 1
  | i + 1 => oddDF i * (2 * i + 1)

/-- The integer coefficient in the odd-half-integer formula.
`halfCoeff k` is the paper's `c_{k+2}`. -/
def halfCoeff : Nat → Nat
  | 0 => 1
  | k + 1 => halfCoeff k * oddDF (k + 1)

@[simp] theorem fac_zero : fac 0 = 1 := rfl
@[simp] theorem fac_succ (n : Nat) : fac (n + 1) = (n + 1) * fac n := rfl
@[simp] theorem gPos_zero : gPos 0 = 1 := rfl
@[simp] theorem gPos_succ (n : Nat) : gPos (n + 1) = fac n * gPos n := rfl
@[simp] theorem superfac_zero : superfac 0 = 1 := rfl
@[simp] theorem superfac_succ (n : Nat) :
    superfac (n + 1) = superfac n * fac (n + 1) := rfl
@[simp] theorem hyperfac_zero : hyperfac 0 = 1 := rfl
@[simp] theorem hyperfac_succ (n : Nat) :
    hyperfac (n + 1) = hyperfac n * (n + 1) ^ (n + 1) := rfl
@[simp] theorem oddDF_zero : oddDF 0 = 1 := rfl
@[simp] theorem oddDF_succ (i : Nat) :
    oddDF (i + 1) = oddDF i * (2 * i + 1) := rfl
@[simp] theorem halfCoeff_zero : halfCoeff 0 = 1 := rfl
@[simp] theorem halfCoeff_succ (k : Nat) :
    halfCoeff (k + 1) = halfCoeff k * oddDF (k + 1) := rfl

/-- `G(n+2)=0!1!...n!`; in shifted notation this is `gPos(n+1)`. -/
theorem gPos_eq_superfac (n : Nat) : gPos (n + 1) = superfac n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change fac (n + 1) * gPos (n + 1) = superfac n * fac (n + 1)
      simpa [ih, Nat.mul_comm]

/-- Finite Gamma-product identity with every division cleared.
The factor `fac (k+i)` is `Gamma(k+i+1)`. -/
def facBlock (k : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => facBlock k n * fac (k + n)

@[simp] theorem facBlock_zero (k : Nat) : facBlock k 0 = 1 := rfl
@[simp] theorem facBlock_succ (k n : Nat) :
    facBlock k (n + 1) = facBlock k n * fac (k + n) := rfl

/-- The division-free content of
`prod_{i=1}^n Gamma(k+i)=G(k+n+1)/G(k+1)` at natural `k`. -/
theorem gPos_telescope (k n : Nat) :
    gPos (k + n) = gPos k * facBlock k n := by
  induction n with
  | zero => simp [facBlock]
  | succ n ih =>
      change fac (k + n) * gPos (k + n) =
        gPos k * (facBlock k n * fac (k + n))
      rw [ih]
      ac_rfl

/-- Exact integer relation between Barnes values and the hyperfactorial. -/
theorem hyperfac_cross_identity (n : Nat) :
    gPos n * hyperfac n = fac n ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        gPos (n + 1) * hyperfac (n + 1)
            = (gPos n * hyperfac n) *
                (fac n * (n + 1) ^ (n + 1)) := by
                  rw [gPos_succ, hyperfac_succ]
                  ac_rfl
        _ = fac n ^ n * (fac n * (n + 1) ^ (n + 1)) := by rw [ih]
        _ = fac (n + 1) ^ (n + 1) := by
              simp only [fac_succ, Nat.mul_pow, Nat.pow_succ]
              ac_rfl

/-- The first twelve shifted values, useful as an executable normalization test. -/
def firstValues : List Nat := (List.range 12).map gPos

#eval firstValues
#eval (List.range 9).map halfCoeff

end BarnesGIPRA.FiniteCore
