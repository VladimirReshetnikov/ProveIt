import PolynomialFormulas.LazardQuintic

/-!
# Fourier reconstruction for depressed quintics

This file isolates the small, formula-independent algebraic endgame of
Lazard's solution.  Four cyclic identities for Fourier components imply that
every inverse Fourier value indexed by a fifth root of unity annihilates the
depressed quintic.

The substantial Lazard-specific calculation is therefore cleanly separated:
it only has to prove `FourierRelations` for the four displayed components
`P₁,...,P₄`.  No primitive-root property is needed in this file's pointwise
argument; `z ^ 5 = 1` is enough.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

section Field

variable {K : Type*} [Field K] [CharZero K]

/-! ## The four cyclic coefficient identities -/

/-- The cyclic quadratic expression in four nonzero Fourier components. -/
def fourierCyclic2 (a b c d : K) : K :=
  a * d + b * c

/-- The cyclic cubic expression in four nonzero Fourier components. -/
def fourierCyclic3 (a b c d : K) : K :=
  a ^ 2 * c + a * b ^ 2 + b * d ^ 2 + c ^ 2 * d

/-- The cyclic quartic expression in four nonzero Fourier components. -/
def fourierCyclic4 (a b c d : K) : K :=
  a ^ 2 * d ^ 2 - a * b * c * d + b ^ 2 * c ^ 2 -
    a ^ 3 * b - a * c ^ 3 - b ^ 3 * d - c * d ^ 3

/-- The cyclic quintic expression in four nonzero Fourier components. -/
def fourierCyclic5 (a b c d : K) : K :=
  a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 -
    5 * a ^ 3 * c * d + 5 * a ^ 2 * b ^ 2 * d +
    5 * a ^ 2 * b * c ^ 2 - 5 * a * b ^ 3 * c -
    5 * a * b * d ^ 3 + 5 * a * c ^ 2 * d ^ 2 +
    5 * b ^ 2 * c * d ^ 2 - 5 * b * c ^ 3 * d

/-- The four coefficient identities that characterize Fourier components of
the roots of `X⁵ + pX³ + qX² + rX + s` for the pointwise reconstruction
argument. -/
structure FourierRelations (c : DepressedQuintic K) (a b c' d : K) : Prop where
  cyclic2 : fourierCyclic2 a b c' d = -5 * c.p
  cyclic3 : fourierCyclic3 a b c' d = -25 * c.q
  cyclic4 : fourierCyclic4 a b c' d = 125 * c.r
  cyclic5 : fourierCyclic5 a b c' d = -3125 * c.s

/-! ## Inverse Fourier values and pointwise soundness -/

/-- Inverse Fourier reconstruction at an arbitrary scalar `z`. -/
def inverseFourierAt (z a b c d : K) : K :=
  (z * a + z ^ 2 * b + z ^ 3 * c + z ^ 4 * d) / 5

/-- The indexed inverse Fourier reconstruction used by Lazard's solver. -/
def inverseFourier (omega a b c d : K) (k : Fin 5) : K :=
  let n := (k : ℕ)
  (omega ^ n * a + omega ^ (2 * n) * b +
    omega ^ (3 * n) * c + omega ^ (4 * n) * d) / 5

omit [CharZero K] in
/-- The indexed form is evaluation at `z = omega ^ k`. -/
theorem inverseFourier_eq_at (omega a b c d : K) (k : Fin 5) :
    inverseFourier omega a b c d k =
      inverseFourierAt (omega ^ (k : ℕ)) a b c d := by
  simp [inverseFourier, inverseFourierAt, pow_mul, Nat.mul_comm]

/-- The inverse Fourier value at `z = 1` is a root whenever the four cyclic
relations hold.  After solving the relations for `p,q,r,s`, the assertion is
the single polynomial identity
`S⁵ - 5 C₂ S³ - 5 C₃ S² + 5 C₄ S - C₅ = 0`. -/
theorem FourierRelations.base_root {c : DepressedQuintic K} {a b c' d : K}
    (h : FourierRelations c a b c' d) :
    c.eval ((a + b + c' + d) / 5) = 0 := by
  have hp : c.p = -fourierCyclic2 a b c' d / 5 := by
    linear_combination (1 / 5) * h.cyclic2
  have hq : c.q = -fourierCyclic3 a b c' d / 25 := by
    linear_combination (1 / 25) * h.cyclic3
  have hr : c.r = fourierCyclic4 a b c' d / 125 := by
    linear_combination (-1 / 125) * h.cyclic4
  have hs : c.s = -fourierCyclic5 a b c' d / 3125 := by
    linear_combination (1 / 3125) * h.cyclic5
  unfold DepressedQuintic.eval
  rw [hp, hq, hr, hs]
  simp only [fourierCyclic2, fourierCyclic3, fourierCyclic4, fourierCyclic5]
  field_simp
  ring

omit [CharZero K] in
/-- Multiplying the four Fourier components by `z,z²,z³,z⁴` preserves all
four cyclic relations whenever `z⁵ = 1`. -/
theorem FourierRelations.twist {c : DepressedQuintic K} {a b c' d z : K}
    (h : FourierRelations c a b c' d) (hz : z ^ 5 = 1) :
    FourierRelations c (z * a) (z ^ 2 * b) (z ^ 3 * c') (z ^ 4 * d) := by
  have hz10 : z ^ 10 = 1 := by
    calc
      z ^ 10 = (z ^ 5) ^ 2 := by ring
      _ = 1 := by rw [hz]; ring
  have hz15 : z ^ 15 = 1 := by
    calc
      z ^ 15 = (z ^ 5) ^ 3 := by ring
      _ = 1 := by rw [hz]; ring
  have hz20 : z ^ 20 = 1 := by
    calc
      z ^ 20 = (z ^ 5) ^ 4 := by ring
      _ = 1 := by rw [hz]; ring
  constructor
  · rw [← h.cyclic2]
    simp only [fourierCyclic2]
    calc
      z * a * (z ^ 4 * d) + z ^ 2 * b * (z ^ 3 * c') =
          z ^ 5 * (a * d + b * c') := by ring
      _ = a * d + b * c' := by rw [hz]; ring
  · rw [← h.cyclic3]
    simp only [fourierCyclic3]
    calc
      (z * a) ^ 2 * (z ^ 3 * c') + (z * a) * (z ^ 2 * b) ^ 2 +
          (z ^ 2 * b) * (z ^ 4 * d) ^ 2 +
          (z ^ 3 * c') ^ 2 * (z ^ 4 * d) =
        z ^ 5 * (a ^ 2 * c' + a * b ^ 2) +
          z ^ 10 * (b * d ^ 2 + c' ^ 2 * d) := by ring
      _ = a ^ 2 * c' + a * b ^ 2 + b * d ^ 2 + c' ^ 2 * d := by
        rw [hz, hz10]
        ring
  · rw [← h.cyclic4]
    simp only [fourierCyclic4]
    calc
      (z * a) ^ 2 * (z ^ 4 * d) ^ 2 -
          (z * a) * (z ^ 2 * b) * (z ^ 3 * c') * (z ^ 4 * d) +
          (z ^ 2 * b) ^ 2 * (z ^ 3 * c') ^ 2 -
          (z * a) ^ 3 * (z ^ 2 * b) -
          (z * a) * (z ^ 3 * c') ^ 3 -
          (z ^ 2 * b) ^ 3 * (z ^ 4 * d) -
          (z ^ 3 * c') * (z ^ 4 * d) ^ 3 =
        z ^ 10 * (a ^ 2 * d ^ 2 - a * b * c' * d +
          b ^ 2 * c' ^ 2 - a * c' ^ 3 - b ^ 3 * d) +
          z ^ 5 * (-a ^ 3 * b) + z ^ 15 * (-c' * d ^ 3) := by ring
      _ = a ^ 2 * d ^ 2 - a * b * c' * d + b ^ 2 * c' ^ 2 -
          a ^ 3 * b - a * c' ^ 3 - b ^ 3 * d - c' * d ^ 3 := by
        rw [hz, hz10, hz15]
        ring
  · rw [← h.cyclic5]
    simp only [fourierCyclic5]
    rw [show
      (z * a) ^ 5 + (z ^ 2 * b) ^ 5 + (z ^ 3 * c') ^ 5 +
          (z ^ 4 * d) ^ 5 -
          5 * (z * a) ^ 3 * (z ^ 3 * c') * (z ^ 4 * d) +
          5 * (z * a) ^ 2 * (z ^ 2 * b) ^ 2 * (z ^ 4 * d) +
          5 * (z * a) ^ 2 * (z ^ 2 * b) * (z ^ 3 * c') ^ 2 -
          5 * (z * a) * (z ^ 2 * b) ^ 3 * (z ^ 3 * c') -
          5 * (z * a) * (z ^ 2 * b) * (z ^ 4 * d) ^ 3 +
          5 * (z * a) * (z ^ 3 * c') ^ 2 * (z ^ 4 * d) ^ 2 +
          5 * (z ^ 2 * b) ^ 2 * (z ^ 3 * c') * (z ^ 4 * d) ^ 2 -
          5 * (z ^ 2 * b) * (z ^ 3 * c') ^ 3 * (z ^ 4 * d) =
        z ^ 5 * a ^ 5 + z ^ 10 * b ^ 5 + z ^ 15 * c' ^ 5 +
          z ^ 20 * d ^ 5 - z ^ 10 * 5 * a ^ 3 * c' * d +
          z ^ 10 * 5 * a ^ 2 * b ^ 2 * d +
          z ^ 10 * 5 * a ^ 2 * b * c' ^ 2 -
          z ^ 10 * 5 * a * b ^ 3 * c' -
          z ^ 15 * 5 * a * b * d ^ 3 +
          z ^ 15 * 5 * a * c' ^ 2 * d ^ 2 +
          z ^ 15 * 5 * b ^ 2 * c' * d ^ 2 -
          z ^ 15 * 5 * b * c' ^ 3 * d by ring]
    rw [hz, hz10, hz15, hz20]
    ring

/-- Every inverse Fourier value at a fifth root of unity is a root of the
depressed quintic. -/
theorem FourierRelations.root {c : DepressedQuintic K} {a b c' d z : K}
    (h : FourierRelations c a b c' d) (hz : z ^ 5 = 1) :
    c.eval (inverseFourierAt z a b c' d) = 0 := by
  have ht := h.twist hz
  simpa [inverseFourierAt, mul_assoc] using ht.base_root

/-- Indexed inverse Fourier reconstruction is pointwise sound for a primitive
fifth root of unity. -/
theorem FourierRelations.inverseFourier_root {c : DepressedQuintic K}
    {a b c' d : K} (h : FourierRelations c a b c' d)
    (omega : FifthRootOfUnity K) (k : Fin 5) :
    c.eval (inverseFourier omega.value a b c' d k) = 0 := by
  rw [inverseFourier_eq_at]
  apply h.root
  calc
    (omega.value ^ (k : ℕ)) ^ 5 = omega.value ^ ((k : ℕ) * 5) := by
      rw [pow_mul]
    _ = omega.value ^ (5 * (k : ℕ)) := by rw [Nat.mul_comm]
    _ = (omega.value ^ 5) ^ (k : ℕ) := by rw [pow_mul]
    _ = 1 := by rw [omega.primitive.pow_eq_one, one_pow]

omit [CharZero K] in
/-- `solveDepressed` is precisely the generic inverse Fourier reconstruction
applied to Lazard's four computed components. -/
theorem solveDepressed_eq_inverseFourier [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K)
    (d : RadicalCertificate c i) (omega : FifthRootOfUnity K)
    (k : Fin 5) :
    solveDepressed c i d omega k =
      inverseFourier omega.value d.p1
        (fourierP2 c i d.chosen d.p1)
        (fourierP3 c i d.chosen d.p1)
        (fourierP4 c i d.chosen d.p1) k := by
  rfl

/-- The four Fourier relations are the complete formula-specific input needed
to prove pointwise soundness of `solveGeneral`.  This theorem packages the
generic inverse-Fourier argument together with the final Tschirnhaus
translation back to the original quintic. -/
theorem solveGeneral_root_of_fourierRelations [DecidableEq K]
    (c : GeneralQuintic K) (ha : c.a ≠ 0) (i : Invariants K)
    (d : RadicalCertificate (depress c) i) (omega : FifthRootOfUnity K)
    (h : FourierRelations (depress c) d.p1
      (fourierP2 (depress c) i d.chosen d.p1)
      (fourierP3 (depress c) i d.chosen d.p1)
      (fourierP4 (depress c) i d.chosen d.p1))
    (k : Fin 5) :
    c.eval (solveGeneral c i d omega k) = 0 := by
  rw [solveGeneral, depress_eval c ha]
  rw [solveDepressed_eq_inverseFourier]
  rw [h.inverseFourier_root omega k, mul_zero]

end Field

end LeanProofs.PolynomialFormulas.LazardQuintic
