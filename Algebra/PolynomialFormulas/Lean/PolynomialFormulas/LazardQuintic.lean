import Mathlib.Tactic

/-!
# Lazard's formula for solvable quintics

This file is a proof-oriented transcription of the explicit formula in
Daniel Lazard, *Solving Quintics by Radicals*, pp. 219--222, with the two
corrections recorded in the accompanying Mathematica Stack Exchange thread:

* the sign of `ε` is changed when `E + F / ε = 0`, before `T` is chosen;
* the two misprinted terms in `P₂₂` are `8 p³ q` and `70 q³`.

The formula is deliberately split into named stages.  The four linear
invariant equations, radical choices, and every nonzero denominator are
visible in the API.  The rational entry point accepts a supplied rational
invariant witness; it does not implement factorization or rational-root
search.  The raw `InvariantRelations` and `RadicalCertificate` hypotheses do
not by themselves imply soundness.  `FormulaSound` and `FormulaFactors` below
retain those over-strong raw-certificate claims for audit; they are definitions
of propositions, not theorems or axioms.  Pointwise soundness from the
additional cyclic identities is proved in `LazardQuinticFourier`.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

section Field

variable {K : Type*} [Field K] [CharZero K]

/-! ## Normalize and depress -/

/-- Coefficients of `aX⁵ + bX⁴ + cX³ + dX² + eX + f`. -/
structure GeneralQuintic (K : Type*) where
  a : K
  b : K
  c : K
  d : K
  e : K
  f : K

namespace GeneralQuintic

/-- Evaluation of a general quintic. -/
def eval (c : GeneralQuintic K) (x : K) : K :=
  c.a * x ^ 5 + c.b * x ^ 4 + c.c * x ^ 3 +
    c.d * x ^ 2 + c.e * x + c.f

/-- The polynomial represented by the six coefficients. -/
noncomputable def polynomial (c : GeneralQuintic K) : K[X] :=
  C c.a * X ^ 5 + C c.b * X ^ 4 + C c.c * X ^ 3 +
    C c.d * X ^ 2 + C c.e * X + C c.f

omit [CharZero K] in
@[simp] theorem polynomial_eval (c : GeneralQuintic K) (x : K) :
    c.polynomial.eval x = c.eval x := by
  simp [polynomial, eval]

/-- Map all six coefficients into a field extension. -/
def map {L : Type*} [Field L] (c : GeneralQuintic K) (phi : K →+* L) :
    GeneralQuintic L :=
  ⟨phi c.a, phi c.b, phi c.c, phi c.d, phi c.e, phi c.f⟩

end GeneralQuintic

/-- Coefficients of the depressed monic quintic `X⁵ + pX³ + qX² + rX + s`. -/
structure DepressedQuintic (K : Type*) where
  p : K
  q : K
  r : K
  s : K

namespace DepressedQuintic

/-- Evaluation of a depressed monic quintic. -/
def eval (c : DepressedQuintic K) (x : K) : K :=
  x ^ 5 + c.p * x ^ 3 + c.q * x ^ 2 + c.r * x + c.s

/-- Polynomial represented by the four depressed coefficients. -/
noncomputable def polynomial (c : DepressedQuintic K) : K[X] :=
  X ^ 5 + C c.p * X ^ 3 + C c.q * X ^ 2 + C c.r * X + C c.s

omit [CharZero K] in
@[simp] theorem polynomial_eval (c : DepressedQuintic K) (x : K) :
    c.polynomial.eval x = c.eval x := by
  simp [polynomial, eval]

omit [CharZero K] in
@[simp] theorem polynomial_coeff_zero (c : DepressedQuintic K) :
    c.polynomial.coeff 0 = c.s := by
  simp [polynomial]

omit [CharZero K] in
@[simp] theorem polynomial_coeff_one (c : DepressedQuintic K) :
    c.polynomial.coeff 1 = c.r := by
  simp [polynomial]

omit [CharZero K] in
@[simp] theorem polynomial_coeff_two (c : DepressedQuintic K) :
    c.polynomial.coeff 2 = c.q := by
  simp [polynomial]

omit [CharZero K] in
@[simp] theorem polynomial_coeff_three (c : DepressedQuintic K) :
    c.polynomial.coeff 3 = c.p := by
  simp [polynomial]

omit [CharZero K] in
@[simp] theorem polynomial_coeff_four (c : DepressedQuintic K) :
    c.polynomial.coeff 4 = 0 := by
  simp [polynomial]

omit [CharZero K] in
@[simp] theorem polynomial_coeff_five (c : DepressedQuintic K) :
    c.polynomial.coeff 5 = 1 := by
  simp [polynomial]

omit [CharZero K] in
theorem polynomial_monic (c : DepressedQuintic K) : c.polynomial.Monic := by
  simp only [polynomial]
  monicity!

omit [CharZero K] in
@[simp] theorem polynomial_natDegree (c : DepressedQuintic K) :
    c.polynomial.natDegree = 5 := by
  simp only [polynomial]
  compute_degree!

/-- Map the four depressed coefficients into a field extension. -/
def map {L : Type*} [Field L] (c : DepressedQuintic K) (phi : K →+* L) :
    DepressedQuintic L :=
  ⟨phi c.p, phi c.q, phi c.r, phi c.s⟩

end DepressedQuintic

/-- Lazard's four coefficients after normalizing and translating
`X = Y - b/(5a)`. -/
def depress (c : GeneralQuintic K) : DepressedQuintic K where
  p := (5 * c.a * c.c - 2 * c.b ^ 2) / (5 * c.a ^ 2)
  q := (25 * c.a ^ 2 * c.d - 15 * c.a * c.b * c.c + 4 * c.b ^ 3) /
    (25 * c.a ^ 3)
  r := (125 * c.a ^ 3 * c.e - 50 * c.a ^ 2 * c.b * c.d +
    15 * c.a * c.b ^ 2 * c.c - 3 * c.b ^ 4) / (125 * c.a ^ 4)
  s := (3125 * c.a ^ 4 * c.f - 625 * c.a ^ 3 * c.b * c.e +
    125 * c.a ^ 2 * c.b ^ 2 * c.d - 25 * c.a * c.b ^ 3 * c.c +
    4 * c.b ^ 5) / (3125 * c.a ^ 5)

/-- Depression commutes with extension of scalars. -/
theorem depress_map {L : Type*} [Field L] [CharZero L]
    (c : GeneralQuintic K) (phi : K →+* L) :
    depress (c.map phi) = (depress c).map phi := by
  cases c
  simp [depress, GeneralQuintic.map, DepressedQuintic.map, map_ofNat]

/-- Exact normalization and Tschirnhaus translation used by the algorithm. -/
theorem depress_eval (c : GeneralQuintic K) (ha : c.a ≠ 0) (y : K) :
    c.eval (y - c.b / (5 * c.a)) = c.a * (depress c).eval y := by
  simp only [GeneralQuintic.eval, DepressedQuintic.eval, depress]
  field_simp [ha]
  ring

/-! ## The Lazard--Cayley sextic -/

/-- The discriminant of `X⁵ + pX³ + qX² + rX + s`, written explicitly as in
Lazard's section 7. -/
def discriminant (c : DepressedQuintic K) : K :=
  108 * c.p ^ 5 * c.s ^ 2 - 72 * c.p ^ 4 * c.q * c.r * c.s +
    16 * c.p ^ 4 * c.r ^ 3 + 16 * c.p ^ 3 * c.q ^ 3 * c.s -
    4 * c.p ^ 3 * c.q ^ 2 * c.r ^ 2 - 900 * c.p ^ 3 * c.r * c.s ^ 2 +
    825 * c.p ^ 2 * c.q ^ 2 * c.s ^ 2 +
    560 * c.p ^ 2 * c.q * c.r ^ 2 * c.s - 128 * c.p ^ 2 * c.r ^ 4 -
    630 * c.p * c.q ^ 3 * c.r * c.s + 144 * c.p * c.q ^ 2 * c.r ^ 3 -
    3750 * c.p * c.q * c.s ^ 3 + 2000 * c.p * c.r ^ 2 * c.s ^ 2 +
    108 * c.q ^ 5 * c.s - 27 * c.q ^ 4 * c.r ^ 2 +
    2250 * c.q ^ 2 * c.r * c.s ^ 2 - 1600 * c.q * c.r ^ 3 * c.s +
    256 * c.r ^ 5 + 3125 * c.s ^ 4

/-- The cubic expression whose square occurs in the fraction-free sextic.
The argument is `i₄`, not Cayley's invariant `Θ`. -/
def resolventCore (c : DepressedQuintic K) (z : K) : K :=
  2 * z ^ 3 + 8 * z ^ 2 * c.r +
    (-6 * c.p ^ 2 * c.r + 2 * c.p * c.q ^ 2 - 50 * c.q * c.s +
      24 * c.r ^ 2) * z -
    15 * c.p ^ 2 * c.q * c.s - 16 * c.p ^ 2 * c.r ^ 2 +
    13 * c.p * c.q ^ 2 * c.r + 125 * c.p * c.s ^ 2 -
    2 * c.q ^ 4 - 200 * c.q * c.r * c.s + 64 * c.r ^ 3

/-- Cayley's invariant in Lazard's earlier notation.  Section 7 translates
from this value to the variable `i₄`. -/
def cayleyTheta (c : DepressedQuintic K) (i4 : K) : K :=
  4 * i4 + c.p ^ 2 + 12 * c.r

/-- The monic degree-six resolvent evaluated at `z = i₄`. -/
def resolventEval (c : DepressedQuintic K) (z : K) : K :=
  (resolventCore c z / 2) ^ 2 -
    (z + 3 * c.r + c.p ^ 2 / 4) * discriminant c

/-- The actual sextic polynomial on which the rational-root step operates. -/
noncomputable def resolventPolynomial (c : DepressedQuintic K) : K[X] :=
  let z : K[X] := X
  let A : K[X] :=
    2 * z ^ 3 + Polynomial.C (8 * c.r) * z ^ 2 +
      Polynomial.C (-6 * c.p ^ 2 * c.r + 2 * c.p * c.q ^ 2 -
        50 * c.q * c.s + 24 * c.r ^ 2) * z +
      Polynomial.C (-15 * c.p ^ 2 * c.q * c.s - 16 * c.p ^ 2 * c.r ^ 2 +
        13 * c.p * c.q ^ 2 * c.r + 125 * c.p * c.s ^ 2 -
        2 * c.q ^ 4 - 200 * c.q * c.r * c.s + 64 * c.r ^ 3)
  (Polynomial.C (1 / 2) * A) ^ 2 -
    (z + Polynomial.C (3 * c.r + c.p ^ 2 / 4)) * Polynomial.C (discriminant c)

/-- The displayed Lazard polynomial is literally monic, not only associated
to a monic scalar resolvent after a coefficient-dependent rescaling. -/
theorem resolventPolynomial_monic (c : DepressedQuintic K) :
    (resolventPolynomial c).Monic := by
  simp only [resolventPolynomial]
  monicity!

@[simp] theorem resolventPolynomial_eval (c : DepressedQuintic K) (z : K) :
    (resolventPolynomial c).eval z = resolventEval c z := by
  simp [resolventPolynomial, resolventEval, resolventCore]
  ring

/-- The fraction-free equation used by the corrected Wolfram implementation
is exactly the vanishing of Lazard's monic sextic. -/
theorem resolventEval_eq_zero_iff (c : DepressedQuintic K) (z : K) :
    resolventEval c z = 0 ↔
      cayleyTheta c z * discriminant c = resolventCore c z ^ 2 := by
  have hscale :
      resolventCore c z ^ 2 - cayleyTheta c z * discriminant c =
        4 * resolventEval c z := by
    simp only [resolventEval, cayleyTheta]
    ring
  constructor
  · intro h
    have hz : resolventCore c z ^ 2 - cayleyTheta c z * discriminant c = 0 := by
      rw [hscale, h]
      ring
    exact (sub_eq_zero.mp hz).symm
  · intro h
    have hz : resolventCore c z ^ 2 - cayleyTheta c z * discriminant c = 0 :=
      sub_eq_zero.mpr h.symm
    rw [hscale] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-! ## The separating invariants `i₄,...,i₈` -/

/-- Values of Lazard's five metacyclic invariants.  For rational input these
are selected in `ℚ`; later radical calculations may map them to an extension. -/
structure Invariants (K : Type*) where
  i4 : K
  i5 : K
  i6 : K
  i7 : K
  i8 : K

namespace Invariants

/-- Map a rational invariant tuple into the radical field. -/
def map {L : Type*} [Field L] (i : Invariants K) (phi : K →+* L) :
    Invariants L :=
  ⟨phi i.i4, phi i.i5, phi i.i6, phi i.i7, phi i.i8⟩

end Invariants

/-- Right side of the first equation in Lazard's Figure 3. -/
def i4SquareRhs (c : DepressedQuintic K) (i : Invariants K) : K :=
  5 * i.i8 - 2 * c.p * i.i6 + 4 * c.q * i.i5 - 2 * c.p ^ 2 * i.i4 -
    6 * c.p ^ 2 * c.r + 2 * c.p * c.q ^ 2 + 10 * c.q * c.s + 4 * c.r ^ 2

/-- Right side of the second equation in Lazard's Figure 3. -/
def i4CubeRhs (c : DepressedQuintic K) (i : Invariants K) : K :=
  ((3 * c.p ^ 2 - 20 * c.r) * i.i8 + (-c.p * c.q - 50 * c.s) * i.i7 +
    (-3 * c.p ^ 3 + 28 * c.p * c.r - 12 * c.q ^ 2) * i.i6 +
    (3 * c.p ^ 2 * c.q - 45 * c.p * c.s - 6 * c.q * c.r) * i.i5 +
    (-3 * c.p ^ 4 + 36 * c.p ^ 2 * c.r - 15 * c.p * c.q ^ 2 +
      60 * c.q * c.s - 32 * c.r ^ 2) * i.i4 -
    6 * c.p ^ 4 * c.r + 3 * c.p ^ 3 * c.q ^ 2 +
    41 * c.p ^ 2 * c.q * c.s + 52 * c.p ^ 2 * c.r ^ 2 -
    54 * c.p * c.q ^ 2 * c.r - 250 * c.p * c.s ^ 2 +
    14 * c.q ^ 4 + 140 * c.q * c.r * c.s - 80 * c.r ^ 3) / 2

/-- Right side of the third equation in Lazard's Figure 3. -/
def i4FourthRhs (c : DepressedQuintic K) (i : Invariants K) : K :=
  (19 * c.p ^ 2 * c.r - 9 * c.p * c.q ^ 2 + 225 * c.q * c.s -
      60 * c.r ^ 2) * i.i8 +
    (15 * c.p ^ 2 * c.s - 8 * c.p * c.q * c.r + 3 * c.q ^ 3 +
      100 * c.r * c.s) * i.i7 +
    (-4 * c.p ^ 3 * c.r + 4 * c.p ^ 2 * c.q ^ 2 -
      105 * c.p * c.q * c.s - 16 * c.p * c.r ^ 2 +
      29 * c.q ^ 2 * c.r + 125 * c.s ^ 2) * i.i6 +
    (-9 * c.p ^ 3 * c.s + 17 * c.p ^ 2 * c.q * c.r -
      8 * c.p * c.q ^ 3 + 140 * c.p * c.r * c.s +
      155 * c.q ^ 2 * c.s - 68 * c.q * c.r ^ 2) * i.i5 +
    (-4 * c.p ^ 4 * c.r + 4 * c.p ^ 3 * c.q ^ 2 -
      79 * c.p ^ 2 * c.q * c.s - 16 * c.p ^ 2 * c.r ^ 2 +
      15 * c.p * c.q ^ 2 * c.r - 25 * c.p * c.s ^ 2 +
      4 * c.q ^ 4 + 80 * c.q * c.r * c.s) * i.i4 +
    6 * c.p ^ 4 * c.q * c.s - 22 * c.p ^ 4 * c.r ^ 2 +
    16 * c.p ^ 3 * c.q ^ 2 * c.r - 4 * c.p ^ 2 * c.q ^ 4 -
    404 * c.p ^ 2 * c.q * c.r * c.s + 68 * c.p ^ 2 * c.r ^ 3 +
    132 * c.p * c.q ^ 3 * c.s + 42 * c.p * c.q ^ 2 * c.r ^ 2 +
    550 * c.p * c.r * c.s ^ 2 - 30 * c.q ^ 4 * c.r -
    50 * c.q ^ 2 * c.s ^ 2 + 20 * c.q * c.r ^ 2 * c.s + 16 * c.r ^ 4

/-- Right side of the fourth equation in Lazard's Figure 3. -/
def i4FifthRhs (c : DepressedQuintic K) (i : Invariants K) : K :=
  ((15 * c.p ^ 4 * c.r - 5 * c.p ^ 3 * c.q ^ 2 +
      290 * c.p ^ 2 * c.q * c.s - 152 * c.p ^ 2 * c.r ^ 2 -
      27 * c.p * c.q ^ 2 * c.r - 1375 * c.p * c.s ^ 2 +
      22 * c.q ^ 4 - 700 * c.q * c.r * c.s + 240 * c.r ^ 3) * i.i8 +
    (18 * c.p ^ 4 * c.s - 11 * c.p ^ 3 * c.q * c.r +
      3 * c.p ^ 2 * c.q ^ 3 - 530 * c.p ^ 2 * c.r * c.s +
      110 * c.p * c.q ^ 2 * c.s + 124 * c.p * c.q * c.r ^ 2 -
      41 * c.q ^ 3 * c.r - 2375 * c.q * c.s ^ 2 +
      200 * c.r ^ 2 * c.s) * i.i7 +
    (-15 * c.p ^ 5 * c.r + 5 * c.p ^ 4 * c.q ^ 2 -
      212 * c.p ^ 3 * c.q * c.s + 168 * c.p ^ 3 * c.r ^ 2 -
      83 * c.p ^ 2 * c.q ^ 2 * c.r + 325 * c.p ^ 2 * c.s ^ 2 +
      10 * c.p * c.q ^ 4 + 1560 * c.p * c.q * c.r * c.s -
      176 * c.p * c.r ^ 3 - 620 * c.q ^ 3 * c.s -
      12 * c.q ^ 2 * c.r ^ 2 - 1500 * c.r * c.s ^ 2) * i.i6 +
    (15 * c.p ^ 4 * c.q * c.r - 5 * c.p ^ 3 * c.q ^ 3 -
      147 * c.p ^ 3 * c.r * c.s + 351 * c.p ^ 2 * c.q ^ 2 * c.s -
      90 * c.p ^ 2 * c.q * c.r ^ 2 - 43 * c.p * c.q ^ 3 * c.r -
      3175 * c.p * c.q * c.s ^ 2 - 420 * c.p * c.r ^ 2 * c.s +
      20 * c.q ^ 5 + 215 * c.q ^ 2 * c.r * c.s +
      152 * c.q * c.r ^ 3 + 625 * c.s ^ 3) * i.i5 +
    (-15 * c.p ^ 6 * c.r + 5 * c.p ^ 5 * c.q ^ 2 -
      200 * c.p ^ 4 * c.q * c.s + 200 * c.p ^ 4 * c.r ^ 2 -
      110 * c.p ^ 3 * c.q ^ 2 * c.r + 355 * c.p ^ 3 * c.s ^ 2 +
      15 * c.p ^ 2 * c.q ^ 4 + 1728 * c.p ^ 2 * c.q * c.r * c.s -
      432 * c.p ^ 2 * c.r ^ 3 - 752 * c.p * c.q ^ 3 * c.s +
      220 * c.p * c.q ^ 2 * c.r ^ 2 - 200 * c.p * c.r * c.s ^ 2 -
      43 * c.q ^ 4 * c.r + 1825 * c.q ^ 2 * c.s ^ 2 -
      2640 * c.q * c.r ^ 2 * c.s + 512 * c.r ^ 4) * i.i4 -
    30 * c.p ^ 6 * c.r ^ 2 + 25 * c.p ^ 5 * c.q ^ 2 * c.r +
    198 * c.p ^ 5 * c.s ^ 2 - 5 * c.p ^ 4 * c.q ^ 4 -
    491 * c.p ^ 4 * c.q * c.r * c.s + 364 * c.p ^ 4 * c.r ^ 3 +
    181 * c.p ^ 3 * c.q ^ 3 * c.s - 286 * c.p ^ 3 * c.q ^ 2 * c.r ^ 2 -
    810 * c.p ^ 3 * c.r * c.s ^ 2 + 95 * c.p ^ 2 * c.q ^ 4 * c.r +
    3005 * c.p ^ 2 * c.q ^ 2 * c.s ^ 2 +
    4120 * c.p ^ 2 * c.q * c.r ^ 2 * c.s - 1088 * c.p ^ 2 * c.r ^ 4 -
    12 * c.p * c.q ^ 6 - 4095 * c.p * c.q ^ 3 * c.r * c.s +
    612 * c.p * c.q ^ 2 * c.r ^ 3 - 15875 * c.p * c.q * c.s ^ 3 +
    900 * c.p * c.r ^ 2 * c.s ^ 2 + 858 * c.q ^ 5 * c.s -
    34 * c.q ^ 4 * c.r ^ 2 + 10700 * c.q ^ 2 * c.r * c.s ^ 2 -
    6240 * c.q * c.r ^ 3 * c.s + 960 * c.r ^ 5 + 6250 * c.s ^ 4) / 2

/-- The exact five equations solved in the rational invariant stage.  The
last four are linear in `i₅,...,i₈` once `i₄` is fixed. -/
structure InvariantRelations (c : DepressedQuintic K) (i : Invariants K) : Prop where
  resolvent : resolventEval c i.i4 = 0
  square : i.i4 ^ 2 = i4SquareRhs c i
  cube : i.i4 ^ 3 = i4CubeRhs c i
  fourth : i.i4 ^ 4 = i4FourthRhs c i
  fifth : i.i4 ^ 5 = i4FifthRhs c i

/-- The rational invariant equations remain true after extension of scalars. -/
theorem InvariantRelations.map {L : Type*} [Field L] [CharZero L]
    {c : DepressedQuintic K} {i : Invariants K}
    (h : InvariantRelations c i) (phi : K →+* L) :
    InvariantRelations (c.map phi) (i.map phi) := by
  constructor
  · simpa [resolventEval, resolventCore, discriminant, DepressedQuintic.map,
      Invariants.map, map_ofNat] using congrArg phi h.resolvent
  · simpa [i4SquareRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      congrArg phi h.square
  · simpa [i4CubeRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      congrArg phi h.cube
  · simpa [i4FourthRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      congrArg phi h.fourth
  · simpa [i4FifthRhs, DepressedQuintic.map, Invariants.map, map_ofNat] using
      congrArg phi h.fifth

/-! ## Explicit metacyclic invariants -/

/-- Lazard's invariant `D`; the first square radical satisfies `ε² = 5D`. -/
def invariantD (c : DepressedQuintic K) (i : Invariants K) : K :=
  40 * c.p * i.i8 - 120 * c.q * i.i7 +
    (-24 * c.p ^ 2 + 100 * c.r) * i.i6 +
    (88 * c.p * c.q - 300 * c.s) * i.i5 +
    (-24 * c.p ^ 3 + 100 * c.p * c.r + 24 * c.q ^ 2) * i.i4 -
    80 * c.p ^ 3 * c.r + 40 * c.p ^ 2 * c.q ^ 2 -
    480 * c.p * c.q * c.s + 160 * c.p * c.r ^ 2 +
    332 * c.q ^ 2 * c.r + 125 * c.s ^ 2

/-- Lazard's invariant `E`. -/
def invariantE (c : DepressedQuintic K) (i : Invariants K) : K :=
  (3 * c.p ^ 2 + 20 * c.r) * i.i6 + (-c.p * c.q - 50 * c.s) * i.i5 +
    (3 * c.p ^ 3 + 12 * c.p * c.r + 3 * c.q ^ 2) * i.i4 +
    4 * c.p ^ 3 * c.r - 3 * c.p ^ 2 * c.q ^ 2 +
    40 * c.p * c.q * c.s + 16 * c.p * c.r ^ 2 -
    21 * c.q ^ 2 * c.r + 125 * c.s ^ 2

/-- Lazard's invariant `F`. -/
def invariantF (c : DepressedQuintic K) (i : Invariants K) : K :=
  (-65 * c.p ^ 2 * c.q + 875 * c.p * c.s - 550 * c.q * c.r) * i.i8 +
    (-58 * c.p ^ 2 * c.r + 41 * c.p * c.q ^ 2 - 275 * c.q * c.s +
      440 * c.r ^ 2) * i.i7 +
    (85 * c.p ^ 3 * c.q - 520 * c.p ^ 2 * c.s -
      298 * c.p * c.q * c.r + 366 * c.q ^ 3 + 2100 * c.r * c.s) * i.i6 +
    (4 * c.p ^ 3 * c.r - 73 * c.p ^ 2 * c.q ^ 2 +
      2095 * c.p * c.q * c.s - 56 * c.p * c.r ^ 2 -
      748 * c.q ^ 2 * c.r - 4875 * c.s ^ 2) * i.i5 +
    (85 * c.p ^ 4 * c.q - 418 * c.p ^ 3 * c.s -
      440 * c.p ^ 2 * c.q * c.r + 419 * c.p * c.q ^ 3 +
      1590 * c.p * c.r * c.s - 1040 * c.q ^ 2 * c.s +
      524 * c.q * c.r ^ 2) * i.i4 -
    12 * c.p ^ 5 * c.s + 158 * c.p ^ 4 * c.q * c.r -
    85 * c.p ^ 3 * c.q ^ 3 - 1462 * c.p ^ 3 * c.r * c.s -
    159 * c.p ^ 2 * c.q ^ 2 * c.s + 142 * c.p ^ 2 * c.q * c.r ^ 2 +
    896 * c.p * c.q ^ 3 * c.r + 175 * c.p * c.q * c.s ^ 2 +
    2900 * c.p * c.r ^ 2 * c.s - 402 * c.q ^ 5 -
    1925 * c.q ^ 2 * c.r * c.s - 448 * c.q * c.r ^ 3 - 1875 * c.s ^ 3

/-- Lazard's invariant `G`; after the second square root,
`U = 5G/(Tε)`. -/
def invariantG (c : DepressedQuintic K) (i : Invariants K) : K :=
  (-35 * c.p ^ 2 * c.q - 250 * c.p * c.s - 200 * c.q * c.r) * i.i8 +
    (-22 * c.p ^ 2 * c.r + 19 * c.p * c.q ^ 2 + 650 * c.q * c.s -
      40 * c.r ^ 2) * i.i7 +
    (15 * c.p ^ 3 * c.q + 195 * c.p ^ 2 * c.s +
      68 * c.p * c.q * c.r - 6 * c.q ^ 3 - 1100 * c.r * c.s) * i.i6 +
    (-4 * c.p ^ 3 * c.r - 27 * c.p ^ 2 * c.q ^ 2 -
      270 * c.p * c.q * c.s + 96 * c.p * c.r ^ 2 -
      182 * c.q ^ 2 * c.r + 3000 * c.s ^ 2) * i.i5 +
    (15 * c.p ^ 4 * c.q + 213 * c.p ^ 3 * c.s +
      50 * c.p ^ 2 * c.q * c.r + c.p * c.q ^ 3 -
      940 * c.p * c.r * c.s + 515 * c.q ^ 2 * c.s -
      184 * c.q * c.r ^ 2) * i.i4 +
    12 * c.p ^ 5 * c.s + 42 * c.p ^ 4 * c.q * c.r -
    15 * c.p ^ 3 * c.q ^ 3 + 492 * c.p ^ 3 * c.r * c.s -
    156 * c.p ^ 2 * c.q ^ 2 * c.s + 358 * c.p ^ 2 * c.q * c.r ^ 2 -
    246 * c.p * c.q ^ 3 * c.r + 2825 * c.p * c.q * c.s ^ 2 -
    1400 * c.p * c.r ^ 2 * c.s + 42 * c.q ^ 5 +
    550 * c.q ^ 2 * c.r * c.s - 232 * c.q * c.r ^ 3 - 1250 * c.s ^ 3

/-- The first projection used in the fifth-root radicand. -/
def invariantH (c : DepressedQuintic K) (i : Invariants K) : K :=
  25 * (2 * i.i5 - c.p * c.q - 5 * c.s)

/-- The second projection used in the fifth-root radicand. -/
def invariantI (c : DepressedQuintic K) (i : Invariants K) : K :=
  25 * (40 * c.p * i.i8 - 70 * c.q * i.i7 +
    (-24 * c.p ^ 2 + 100 * c.r) * i.i6 +
    (68 * c.p * c.q - 300 * c.s) * i.i5 +
    (-24 * c.p ^ 3 + 100 * c.p * c.r - 46 * c.q ^ 2) * i.i4 -
    80 * c.p ^ 3 * c.r + 20 * c.p ^ 2 * c.q ^ 2 -
    255 * c.p * c.q * c.s + 160 * c.p * c.r ^ 2 -
    28 * c.q ^ 2 * c.r + 125 * c.s ^ 2)

/-- The third projection used in the fifth-root radicand. -/
def invariantJ (c : DepressedQuintic K) (i : Invariants K) : K :=
  -25 * c.p * i.i8 - 25 * c.q * i.i7 +
    (-9 * c.p ^ 2 - 60 * c.r) * i.i6 +
    (-7 * c.p * c.q + 525 * c.s) * i.i5 +
    (-c.p ^ 3 - 96 * c.p * c.r + 11 * c.q ^ 2) * i.i4 +
    50 * c.p ^ 3 * c.r - 7 * c.p ^ 2 * c.q ^ 2 -
    145 * c.p * c.q * c.s - 308 * c.p * c.r ^ 2 +
    128 * c.q ^ 2 * c.r - 1000 * c.s ^ 2

/-- The fourth projection used in the fifth-root radicand. -/
def invariantK (c : DepressedQuintic K) (i : Invariants K) : K :=
  -125 * c.p * i.i8 + 75 * c.q * i.i7 +
    (67 * c.p ^ 2 - 420 * c.r) * i.i6 +
    (-109 * c.p * c.q + 1175 * c.s) * i.i5 +
    (63 * c.p ^ 3 - 412 * c.p * c.r + 27 * c.q ^ 2) * i.i4 +
    210 * c.p ^ 3 * c.r - 79 * c.p ^ 2 * c.q ^ 2 -
    415 * c.p * c.q * c.s - 676 * c.p * c.r ^ 2 +
    496 * c.q ^ 2 * c.r - 750 * c.s ^ 2

/-! ## Corrected square-root and sign stages -/

/-- Zapodovnikov's correction: if the first choice would make `T = 0`, use
the other determination of `ε` before taking the second square root. -/
def correctEpsilon [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) (epsilon0 : K) : K :=
  if invariantE c i + invariantF c i / epsilon0 = 0 then -epsilon0 else epsilon0

omit [CharZero K] in
/-- The sign correction does not change the square of `ε`. -/
theorem correctEpsilon_sq [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) (epsilon0 : K) :
    correctEpsilon c i epsilon0 ^ 2 = epsilon0 ^ 2 := by
  by_cases h : invariantE c i + invariantF c i / epsilon0 = 0
  · simp [correctEpsilon, h]
  · simp [correctEpsilon, h]

/-- The two radicands exchanged by changing the sign of `ε`. -/
def squareBranchAvailable (c : DepressedQuintic K) (i : Invariants K)
    (epsilon0 : K) : Prop :=
  invariantE c i + invariantF c i / epsilon0 ≠ 0 ∨
    invariantE c i - invariantF c i / epsilon0 ≠ 0

omit [CharZero K] in
/-- Under Lazard's nondegeneracy assertion, the corrected radicand for `T`
is nonzero. -/
theorem correctedTRadicand_ne_zero [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) {epsilon0 : K}
    (hbranches : squareBranchAvailable c i epsilon0) :
    invariantE c i + invariantF c i / correctEpsilon c i epsilon0 ≠ 0 := by
  by_cases h : invariantE c i + invariantF c i / epsilon0 = 0
  · rw [correctEpsilon, if_pos h]
    rcases hbranches with hfalse | hminus
    · exact (hfalse h).elim
    · simpa only [div_neg, sub_eq_add_neg] using hminus
  · rw [correctEpsilon, if_neg h]
    exact h

/-- A supplied first square root and the nondegeneracy facts needed by the
corrected radical stage.  This keeps division by `ε` honest. -/
structure EpsilonChoice (c : DepressedQuintic K) (i : Invariants K) where
  value : K
  square : value ^ 2 = 5 * invariantD c i
  nonzero : value ≠ 0
  branches : squareBranchAvailable c i value

/-- A supplied second square root, chosen only after correcting `ε`. -/
structure TChoice [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) (epsilon0 : K) where
  value : K
  square : value ^ 2 =
    (5 / 2) * (invariantE c i + invariantF c i / correctEpsilon c i epsilon0)
  nonzero : value ≠ 0

/-- The value `U` determined by Lazard's second quadratic stage. -/
def radicalU (c : DepressedQuintic K) (i : Invariants K)
    (epsilon t : K) : K :=
  5 * invariantG c i / (t * epsilon)

/-- One coherent determination of the three quadratic-stage values. -/
structure QuadraticTriple (K : Type*) where
  epsilon : K
  t : K
  u : K

/-- The three equations that make a quadratic triple coherent.  The first
three specify the two square-root stages; the product equation records that
`U = 5G/(Tε)` without hiding its denominator conditions. -/
structure QuadraticRelations (c : DepressedQuintic K) (i : Invariants K)
    (v : QuadraticTriple K) : Prop where
  epsilon_square : v.epsilon ^ 2 = 5 * invariantD c i
  t_square : v.t ^ 2 = (5 / 2) * (invariantE c i + invariantF c i / v.epsilon)
  u_square : v.u ^ 2 = (5 / 2) * (invariantE c i - invariantF c i / v.epsilon)
  product : v.t * v.u * v.epsilon = 5 * invariantG c i

/-- The four coherent sign choices described by Lazard. -/
inductive SignBranch
  | base
  | negateTU
  | rotate
  | rotateNegate
  deriving DecidableEq, Repr

/-- Apply one of Lazard's four coherent sign transformations. -/
def branchTriple (initial : QuadraticTriple K) : SignBranch → QuadraticTriple K
  | .base => initial
  | .negateTU => ⟨initial.epsilon, -initial.t, -initial.u⟩
  | .rotate => ⟨-initial.epsilon, initial.u, -initial.t⟩
  | .rotateNegate => ⟨-initial.epsilon, -initial.u, initial.t⟩

omit [CharZero K] in
/-- Every one of the four sign transformations preserves the quadratic-stage
equations.  In particular, changing the sign of `ε` exchanges the two square
radicands and simultaneously rotates `T` and `U`. -/
theorem QuadraticRelations.of_branchTriple {c : DepressedQuintic K}
    {i : Invariants K} {v : QuadraticTriple K}
    (h : QuadraticRelations c i v) (branch : SignBranch) :
    QuadraticRelations c i (branchTriple v branch) := by
  cases branch
  · exact h
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [branchTriple] using h.epsilon_square
    · simpa [branchTriple] using h.t_square
    · simpa [branchTriple] using h.u_square
    · simpa [branchTriple, mul_comm, mul_left_comm, mul_assoc] using h.product
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [branchTriple] using h.epsilon_square
    · change v.u ^ 2 =
        (5 / 2) * (invariantE c i + invariantF c i / -v.epsilon)
      rw [div_neg]
      simpa [sub_eq_add_neg] using h.u_square
    · change (-v.t) ^ 2 =
        (5 / 2) * (invariantE c i - invariantF c i / -v.epsilon)
      rw [div_neg]
      simpa [sub_eq_add_neg] using h.t_square
    · simpa [branchTriple, mul_comm, mul_left_comm, mul_assoc] using h.product
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [branchTriple] using h.epsilon_square
    · change (-v.u) ^ 2 =
        (5 / 2) * (invariantE c i + invariantF c i / -v.epsilon)
      rw [div_neg]
      simpa [sub_eq_add_neg] using h.u_square
    · change v.t ^ 2 =
        (5 / 2) * (invariantE c i - invariantF c i / -v.epsilon)
      rw [div_neg]
      simpa [sub_eq_add_neg] using h.t_square
    · simpa [branchTriple, mul_comm, mul_left_comm, mul_assoc] using h.product

/-- The fifth-root radicand `Q₁` for one coherent sign triple. -/
def q1 (c : DepressedQuintic K) (i : Invariants K)
    (v : QuadraticTriple K) : K :=
  (5 / 4) * (invariantH c i + invariantI c i / v.epsilon +
    (v.t * invariantJ c i + v.u * invariantK c i) / invariantE c i)

/-- Explicit order used by the Wolfram `Select`: the first branch with a
nonzero `Q₁` is selected. -/
def selectSignBranch [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K)
    (initial : QuadraticTriple K) : Option SignBranch :=
  if q1 c i (branchTriple initial .base) ≠ 0 then some .base
  else if q1 c i (branchTriple initial .negateTU) ≠ 0 then some .negateTU
  else if q1 c i (branchTriple initial .rotate) ≠ 0 then some .rotate
  else if q1 c i (branchTriple initial .rotateNegate) ≠ 0 then some .rotateNegate
  else none

omit [CharZero K] in
/-- Any branch returned by `selectSignBranch` has a nonzero fifth-root
radicand. -/
theorem selectSignBranch_sound [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) (initial : QuadraticTriple K)
    {branch : SignBranch} (h : selectSignBranch c i initial = some branch) :
    q1 c i (branchTriple initial branch) ≠ 0 := by
  unfold selectSignBranch at h
  split at h <;> rename_i hbase
  · simp only [Option.some.injEq] at h
    subst branch
    exact hbase
  · split at h <;> rename_i hneg
    · simp only [Option.some.injEq] at h
      subst branch
      exact hneg
    · split at h <;> rename_i hrot
      · simp only [Option.some.injEq] at h
        subst branch
        exact hrot
      · split at h <;> rename_i hrotneg
        · simp only [Option.some.injEq] at h
          subst branch
          exact hrotneg
        · simp at h

/-! ## Corrected `P₂₂` and the remaining Fourier components -/

def p41 (c : DepressedQuintic K) : K := -5 * c.p

def p42 (c : DepressedQuintic K) (i : Invariants K) : K :=
  5 * (10 * i.i7 - 4 * c.p * i.i5 - 14 * c.q * i.i4 -
    4 * c.p ^ 2 * c.q + 45 * c.p * c.s - 72 * c.q * c.r)

def p31 (c : DepressedQuintic K) : K := -25 * c.q

def p32 (c : DepressedQuintic K) (i : Invariants K) : K :=
  25 * (-10 * i.i8 + 2 * c.p * i.i6 - 22 * c.q * i.i5 +
    2 * c.p ^ 2 * i.i4 + 20 * c.p ^ 2 * c.r + 2 * c.p * c.q ^ 2 -
    35 * c.q * c.s - 40 * c.r ^ 2)

def p33 (c : DepressedQuintic K) (i : Invariants K) : K :=
  5 * (35 * i.i8 - 4 * c.p * i.i6 + 23 * c.q * i.i5 +
    (-6 * c.p ^ 2 + 12 * c.r) * i.i4 - 58 * c.p ^ 2 * c.r +
    14 * c.p * c.q ^ 2 - 105 * c.q * c.s + 76 * c.r ^ 2)

def p34 (c : DepressedQuintic K) (i : Invariants K) : K :=
  5 * (5 * i.i8 - 22 * c.p * i.i6 + 14 * c.q * i.i5 +
    (-18 * c.p ^ 2 + 16 * c.r) * i.i4 - 34 * c.p ^ 2 * c.r +
    22 * c.p * c.q ^ 2 - 140 * c.q * c.s + 68 * c.r ^ 2)

def p21 (c : DepressedQuintic K) (i : Invariants K) : K :=
  5 * (3 * i.i4 + 2 * c.p ^ 2 - 16 * c.r)

/-- Reshetnikov's correction of Lazard p. 222.  The printed `8p³` and
`70q³q` are respectively `8p³q` and `70q³`. -/
def p22 (c : DepressedQuintic K) (i : Invariants K) : K :=
  25 * (-10 * c.q * i.i6 + (8 * c.p ^ 2 - 50 * c.r) * i.i5 +
    (-2 * c.p * c.q - 25 * c.s) * i.i4 +
    8 * c.p ^ 3 * c.q + 70 * c.q ^ 3 - 20 * c.p ^ 2 * c.s -
    26 * c.p * c.q * c.r + 50 * c.r * c.s)

def p23 (c : DepressedQuintic K) (i : Invariants K) : K :=
  25 * (-4 * c.p * i.i7 - c.q * i.i6 + 4 * c.r * i.i5 +
    (-3 * c.p * c.q + 15 * c.s) * i.i4 + 26 * c.p ^ 2 * c.s -
    26 * c.p * c.q * c.r + 7 * c.q ^ 3 - 40 * c.r * c.s)

def p24 (c : DepressedQuintic K) (i : Invariants K) : K :=
  25 * (3 * c.p * i.i7 - 18 * c.q * i.i6 + 22 * c.r * i.i5 +
    (-14 * c.p * c.q + 20 * c.s) * i.i4 + 18 * c.p ^ 2 * c.s -
    33 * c.p * c.q * c.r + 21 * c.q ^ 3 + 30 * c.r * c.s)

/-- Lazard's fourth Fourier component `P₄`. -/
def fourierP4 (c : DepressedQuintic K) (i : Invariants K)
    (v : QuadraticTriple K) (p1 : K) : K :=
  p41 c / (2 * p1) + p42 c i / (2 * v.epsilon * p1)

/-- Lazard's third Fourier component `P₃`. -/
def fourierP3 (c : DepressedQuintic K) (i : Invariants K)
    (v : QuadraticTriple K) (p1 : K) : K :=
  p31 c / (4 * p1 ^ 2) + p32 c i / (4 * v.epsilon * p1 ^ 2) +
    (p33 c i * v.t + p34 c i * v.u) /
      (10 * invariantE c i * p1 ^ 2)

/-- Lazard's second Fourier component `P₂`, using the corrected `P₂₂`. -/
def fourierP2 (c : DepressedQuintic K) (i : Invariants K)
    (v : QuadraticTriple K) (p1 : K) : K :=
  p21 c i / (4 * p1 ^ 3) + p22 c i / (4 * v.epsilon * p1 ^ 3) +
    (p23 c i * v.t + p24 c i * v.u) /
      (10 * invariantE c i * p1 ^ 3)

/-! ## Certified choices and the five outputs -/

/-- All algebraic choices needed after the rational invariant stage.  Each
radical occurs once and its defining equation is stored once, matching
Lazard's requirement that repeated occurrences use the same determination. -/
structure RadicalCertificate [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) where
  epsilon0 : K
  epsilon0_square : epsilon0 ^ 2 = 5 * invariantD c i
  epsilon0_nonzero : epsilon0 ≠ 0
  epsilon_branches : squareBranchAvailable c i epsilon0
  t : K
  t_square : t ^ 2 =
    (5 / 2) * (invariantE c i + invariantF c i / correctEpsilon c i epsilon0)
  u_square :
    (radicalU c i (correctEpsilon c i epsilon0) t) ^ 2 =
      (5 / 2) *
        (invariantE c i - invariantF c i / correctEpsilon c i epsilon0)
  invariantE_nonzero : invariantE c i ≠ 0
  branch : SignBranch
  branch_nonzero :
    q1 c i (branchTriple
      ⟨correctEpsilon c i epsilon0, t,
        radicalU c i (correctEpsilon c i epsilon0) t⟩ branch) ≠ 0
  p1 : K
  p1_power : p1 ^ 5 =
    q1 c i (branchTriple
      ⟨correctEpsilon c i epsilon0, t,
        radicalU c i (correctEpsilon c i epsilon0) t⟩ branch)

namespace RadicalCertificate

/-- The corrected initial `(ε,T,U)` triple. -/
def initial [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : QuadraticTriple K :=
  ⟨correctEpsilon c i d.epsilon0, d.t,
    radicalU c i (correctEpsilon c i d.epsilon0) d.t⟩

/-- The coherent triple selected for the fifth-root radicand. -/
def chosen [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : QuadraticTriple K :=
  branchTriple d.initial d.branch

omit [CharZero K] in
/-- Correcting a sign preserves the fact that `ε` is nonzero. -/
theorem epsilon_nonzero [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : d.initial.epsilon ≠ 0 := by
  unfold initial correctEpsilon
  split
  · simpa using d.epsilon0_nonzero
  · exact d.epsilon0_nonzero

/-- The corrected radicand and the stored square equation force `T ≠ 0`. -/
theorem t_nonzero [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : d.t ≠ 0 := by
  have hrad := correctedTRadicand_ne_zero c i d.epsilon_branches
  have hrhs :
      (5 / 2 : K) *
        (invariantE c i + invariantF c i / correctEpsilon c i d.epsilon0) ≠ 0 :=
    mul_ne_zero (by norm_num) hrad
  intro ht
  apply hrhs
  calc
    (5 / 2 : K) *
        (invariantE c i + invariantF c i / correctEpsilon c i d.epsilon0) =
        d.t ^ 2 := d.t_square.symm
    _ = 0 := by rw [ht]; norm_num

/-- The stored square equations and the definition of `U` form a coherent
initial quadratic triple. -/
theorem initial_relations [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : QuadraticRelations c i d.initial := by
  refine ⟨?_, d.t_square, d.u_square, ?_⟩
  · calc
      d.initial.epsilon ^ 2 = d.epsilon0 ^ 2 :=
        correctEpsilon_sq c i d.epsilon0
      _ = 5 * invariantD c i := d.epsilon0_square
  · have he : correctEpsilon c i d.epsilon0 ≠ 0 := by
      simpa [initial] using d.epsilon_nonzero
    simp only [initial, radicalU]
    field_simp [d.t_nonzero, he]

/-- The branch used for `Q₁` still satisfies all quadratic-stage equations. -/
theorem chosen_relations [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : QuadraticRelations c i d.chosen :=
  d.initial_relations.of_branchTriple d.branch

omit [CharZero K] in
/-- A fifth root of the selected nonzero `Q₁` is nonzero. -/
theorem p1_nonzero [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) : d.p1 ≠ 0 := by
  intro hp
  apply d.branch_nonzero
  calc
    q1 c i d.chosen = d.p1 ^ 5 := d.p1_power.symm
    _ = 0 := by rw [hp]; norm_num

end RadicalCertificate

/-- A primitive fifth root of unity, shared by all five Fourier outputs. -/
structure FifthRootOfUnity (K : Type*) [CommMonoid K] where
  value : K
  primitive : IsPrimitiveRoot value 5

/-- Lazard's inverse discrete Fourier transform for a depressed quintic. -/
def solveDepressed [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K)
    (d : RadicalCertificate c i) (omega : FifthRootOfUnity K)
    (k : Fin 5) : K :=
  let v := d.chosen
  let n := (k : ℕ)
  (omega.value ^ n * d.p1 +
    omega.value ^ (2 * n) * fourierP2 c i v d.p1 +
    omega.value ^ (3 * n) * fourierP3 c i v d.p1 +
    omega.value ^ (4 * n) * fourierP4 c i v d.p1) / 5

/-- The five candidate values for the original general quintic. -/
def solveGeneral [DecidableEq K]
    (c : GeneralQuintic K) (i : Invariants K)
    (d : RadicalCertificate (depress c) i) (omega : FifthRootOfUnity K) :
    Fin 5 → K :=
  fun k => solveDepressed (depress c) i d omega k - c.b / (5 * c.a)

/-- The rational front end of Lazard's algorithm: `i₄,...,i₈` are genuinely
rational and satisfy the sextic/linear-system equations before being mapped
to the radical field. -/
structure RationalInvariantCertificate (c : GeneralQuintic ℚ) where
  values : Invariants ℚ
  relations : InvariantRelations (depress c) values

/-- The supplied rational invariant certificate remains valid in every
characteristic-zero extension field used for the radical calculations. -/
theorem RationalInvariantCertificate.mappedRelations
    {L : Type*} [Field L] [CharZero L] [Algebra ℚ L]
    {c : GeneralQuintic ℚ} (w : RationalInvariantCertificate c) :
    InvariantRelations
      (depress (c.map (algebraMap ℚ L)))
      (w.values.map (algebraMap ℚ L)) := by
  rw [depress_map]
  exact w.relations.map (algebraMap ℚ L)

/-- Evaluate the radical formula in an extension field while retaining a
certificate that the resolvent and invariant-system choices were rational. -/
def solveRational {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    [Algebra ℚ L] (c : GeneralQuintic ℚ)
    (w : RationalInvariantCertificate c)
    (d : RadicalCertificate
      (depress (c.map (algebraMap ℚ L)))
      (w.values.map (algebraMap ℚ L)))
    (omega : FifthRootOfUnity L) : Fin 5 → L :=
  solveGeneral (c.map (algebraMap ℚ L))
    (w.values.map (algebraMap ℚ L)) d omega

omit [CharZero K] in
@[simp] theorem solveDepressed_zero [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K)
    (d : RadicalCertificate c i) (omega : FifthRootOfUnity K) :
    solveDepressed c i d omega 0 =
      (d.p1 + fourierP2 c i d.chosen d.p1 +
        fourierP3 c i d.chosen d.p1 + fourierP4 c i d.chosen d.p1) / 5 := by
  simp [solveDepressed]

/-- The over-strong raw-certificate pointwise claim, retained as a proposition
for audit.  It is not a theorem and does not follow from the stated
hypotheses: `InvariantRelations` and `RadicalCertificate` do not ensure that
the computed components are Fourier components of roots.  The proved theorem
`solveGeneral_root_of_fourierRelations` additionally assumes the four cyclic
`FourierRelations`. -/
def FormulaSound [DecidableEq K] : Prop :=
  ∀ (c : GeneralQuintic K) (_ha : c.a ≠ 0) (i : Invariants K),
    InvariantRelations (depress c) i →
    ∀ (d : RadicalCertificate (depress c) i) (omega : FifthRootOfUnity K)
      (k : Fin 5),
      c.eval (solveGeneral c i d omega k) = 0

/-- The analogous over-strong raw-certificate factorization claim.  It is
retained for audit, not asserted as a theorem; its hypotheses omit the same
Fourier evidence as `FormulaSound`. -/
def FormulaFactors [DecidableEq K] : Prop :=
  ∀ (c : GeneralQuintic K) (_ha : c.a ≠ 0) (i : Invariants K),
    InvariantRelations (depress c) i →
    ∀ (d : RadicalCertificate (depress c) i) (omega : FifthRootOfUnity K),
      c.polynomial =
        C c.a * ∏ k : Fin 5, (X - C (solveGeneral c i d omega k))

/-- Rational specialization of the over-strong raw-certificate pointwise
claim.  Mapping the supplied relations out of `ℚ` does not add the missing
Fourier evidence, so this too is only a retained proposition, not a theorem. -/
def RationalFormulaSound : Prop :=
  ∀ {L : Type*} [Field L] [CharZero L] [DecidableEq L] [Algebra ℚ L]
    (c : GeneralQuintic ℚ) (_ha : c.a ≠ 0)
    (w : RationalInvariantCertificate c)
    (d : RadicalCertificate
      (depress (c.map (algebraMap ℚ L)))
      (w.values.map (algebraMap ℚ L)))
    (omega : FifthRootOfUnity L) (k : Fin 5),
    (c.map (algebraMap ℚ L)).eval (solveRational c w d omega k) = 0

/-- Rational specialization of the over-strong raw-certificate factorization
claim, retained for audit and not asserted as a theorem. -/
def RationalFormulaFactors : Prop :=
  ∀ {L : Type*} [Field L] [CharZero L] [DecidableEq L] [Algebra ℚ L]
    (c : GeneralQuintic ℚ) (_ha : c.a ≠ 0)
    (w : RationalInvariantCertificate c)
    (d : RadicalCertificate
      (depress (c.map (algebraMap ℚ L)))
      (w.values.map (algebraMap ℚ L)))
    (omega : FifthRootOfUnity L),
    (c.map (algebraMap ℚ L)).polynomial =
      C (algebraMap ℚ L c.a) *
        ∏ k : Fin 5, (X - C (solveRational c w d omega k))

end Field

end LeanProofs.PolynomialFormulas.LazardQuintic
