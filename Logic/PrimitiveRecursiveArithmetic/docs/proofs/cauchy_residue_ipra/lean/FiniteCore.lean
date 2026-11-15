import Mathlib

/-!
# Finite algebra for the constructive Cauchy and residue development

Status: UNCOMPILED CANDIDATE. No Lean executable was available in the authoring
workspace. These are complete proposed proof scripts for elementary identities;
the file does not claim that the analytic theorems, or their deeply embedded
iPRA derivations, have been formalized.

The generic commutative ring can eventually be instantiated with rational
complex arithmetic. No theorem about `Complex` differentiation, integration,
limits, Cauchy's theorem, or residues is used here. The factor 2 is retained in
the trapezoidal form so that these identities do not require division.

Ordinary Lean proofs below are a preliminary validation layer. They still need
to be internalized as `PRAAx` derivations as specified in ROADMAP.md.
-/

namespace ConstructiveContours

section RingIdentities

variable {R : Type*} [CommRing R]

/-- Twice the trapezoidal contribution of one oriented edge. -/
def trapezoid2 (f : R → R) (a b : R) : R :=
  (b - a) * (f a + f b)

/-- The doubled trapezoidal boundary sum of a triangle. -/
def triangle2 (f : R → R) (a b c : R) : R :=
  trapezoid2 f a b + trapezoid2 f b c + trapezoid2 f c a

/-- Orientation reversal is an exact algebraic identity, at fixed sample data. -/
theorem trapezoid2_reverse (f : R → R) (a b : R) :
    trapezoid2 f b a = -trapezoid2 f a b := by
  unfold trapezoid2
  ring

/-- Degenerate edges contribute zero. -/
theorem trapezoid2_diagonal (f : R → R) (a : R) :
    trapezoid2 f a a = 0 := by
  simp [trapezoid2]

/-- A useful form of exactness for affine sample data. -/
theorem trapezoid2_affine_formula (α β a b : R) :
    trapezoid2 (fun z => α * z + β) a b =
      α * (b ^ 2 - a ^ 2) + (2 : R) * β * (b - a) := by
  unfold trapezoid2
  ring

/-- The doubled triangle sum annihilates every complex-affine function. -/
theorem triangle2_affine (α β a b c : R) :
    triangle2 (fun z => α * z + β) a b c = 0 := by
  unfold triangle2 trapezoid2
  ring

/-- Splitting an edge is exact for affine data, with no restriction on the
intermediate point. This lemma is not asserted for a general function. -/
theorem trapezoid2_affine_split (α β a m b : R) :
    trapezoid2 (fun z => α * z + β) a m +
        trapezoid2 (fun z => α * z + β) m b =
      trapezoid2 (fun z => α * z + β) a b := by
  unfold trapezoid2
  ring

/-- After one four-triangle subdivision, every internal edge cancels.

Here p, q, r are symbolic points; the cancellation does not use their being
midpoints. The right side is the six-edge *refined* outer boundary. It is not
the coarse three-edge quadrature for a general function. -/
theorem four_triangle_cancellation
    (f : R → R) (a b c p q r : R) :
    triangle2 f a p r + triangle2 f p b q +
        triangle2 f r q c + triangle2 f p q r =
      trapezoid2 f a p + trapezoid2 f p b +
        trapezoid2 f b q + trapezoid2 f q c +
        trapezoid2 f c r + trapezoid2 f r a := by
  unfold triangle2 trapezoid2
  ring

/-- A recursive finite geometric sum. This deliberately uses only primitive
recursion in n, rather than introducing an infinite series. -/
def geomSum (x : R) : ℕ → R
  | 0 => 0
  | n + 1 => geomSum x n + x ^ n

/-- The division-free finite geometric identity. -/
theorem geomSum_mul (x : R) (n : ℕ) :
    (1 - x) * geomSum x n = 1 - x ^ n := by
  induction n with
  | zero =>
      simp [geomSum]
  | succ n ih =>
      calc
        (1 - x) * geomSum x (n + 1) =
            (1 - x) * geomSum x n + (1 - x) * x ^ n := by
              rw [geomSum, mul_add]
        _ = (1 - x ^ n) + (1 - x) * x ^ n := by
              rw [ih]
        _ = 1 - x ^ (n + 1) := by
              rw [pow_succ]
              ring

/-- A finite identity with the remainder visible; used before dividing by an
apart denominator in the Laurent-kernel calculation. -/
theorem geomSum_remainder (x : R) (n : ℕ) :
    (1 - x) * geomSum x n + x ^ n = 1 := by
  rw [geomSum_mul]
  ring

/-- A division-free difference-of-powers polynomial, built by recursion. -/
def dividedPower (u v : R) : ℕ → R
  | 0 => 0
  | n + 1 => u * dividedPower u v n + v ^ n

/-- The elementary identity underlying rational-power primitive estimates. -/
theorem dividedPower_mul (u v : R) (n : ℕ) :
    (u - v) * dividedPower u v n = u ^ n - v ^ n := by
  induction n with
  | zero =>
      simp [dividedPower]
  | succ n ih =>
      calc
        (u - v) * dividedPower u v (n + 1) =
            u * ((u - v) * dividedPower u v n) + (u - v) * v ^ n := by
              rw [dividedPower]
              ring
        _ = u * (u ^ n - v ^ n) + (u - v) * v ^ n := by
              rw [ih]
        _ = u ^ (n + 1) - v ^ (n + 1) := by
              simp only [pow_succ]
              ring

end RingIdentities

end ConstructiveContours
