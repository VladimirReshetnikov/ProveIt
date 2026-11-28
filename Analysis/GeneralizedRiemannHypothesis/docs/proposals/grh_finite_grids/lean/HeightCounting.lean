import Std

/-! Finite arithmetic consequences of the one-place height argument. -/
namespace HeightCounting

/-- A common reduction class for two different points would force an integral
obstruction norm to lie on both sides of a strict threshold. -/
theorem reduction_injective {X Label : Type} (label : X → Label)
    (norm : X → X → Nat) (threshold modulus : Nat)
    (strict : threshold < modulus)
    (upper : ∀ x y, x ≠ y → norm x y ≤ threshold)
    (positive : ∀ x y, x ≠ y → 0 < norm x y)
    (divides : ∀ x y, x ≠ y → label x = label y → modulus ∣ norm x y) :
    ∀ x y, label x = label y → x = y := by
  intro x y eqLabel
  apply Classical.byContradiction
  intro neq
  have lower := Nat.le_of_dvd (positive x y neq) (divides x y neq eqLabel)
  have high := upper x y neq
  omega

/-- Numerator of the dyadic upper sum after n shells. For n > 0 the common
denominator is 8^(n-1) when shell j has weight 8^(-j). -/
def scaledWeight (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => scaledWeight a n * 8 + a n

/-- If shell j contains at most C*4^(j+1) elements, all partial inverse-cube
sums are bounded by 8*C. This integral identity with natural coefficients
avoids real integrals or infinite series in the cube estimate. -/
theorem scaledWeight_bound (C : Nat) (a : Nat → Nat)
    (ha : ∀ j, a j ≤ C * 4^(j+1)) (n : Nat) :
    scaledWeight a n + C * 4^n ≤ C * 8^n := by
  induction n with
  | zero => simp [scaledWeight]
  | succ n ih =>
    have step := Nat.mul_le_mul_right 8 ih
    have shell := ha n
    simp only [scaledWeight, Nat.pow_succ, ← Nat.mul_assoc] at shell ⊢
    omega

#print axioms reduction_injective
#print axioms scaledWeight_bound
end HeightCounting
