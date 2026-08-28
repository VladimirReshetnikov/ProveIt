import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Reverting a quadratic: the Catalan numbers as the inverse coefficients

Over an arbitrary commutative ring `R`, and for an arbitrary `c : R`, the power
series `X + c·X²` has a compositional inverse whose coefficients are the
Catalan numbers carrying an alternating geometric factor,

`S = ∑_{m ≥ 1} (-c)^(m-1) · C_(m-1) · X^m`.

The usual derivation solves the quadratic and expands a square root.  That
route needs the square root to exist, hence a field, a topology and a choice of
branch, none of which the statement is about.  The mechanism used here is the
*functional equation* `S + c·S² = X` read on coefficients: it says exactly that
`m ↦ coeff (m + 1) S` obeys the Catalan convolution recurrence `catalan_succ'`,
twisted by `(-c)^m`.  So the theorem lives over a bare commutative ring — no
division, no characteristic hypothesis, no square root — and `c` is an
arbitrary ring element rather than the single value a specialisation would fix.

The module is therefore organised around the equation, not around the inverse.

* `signedCatalanSeries c` is the Catalan generating function with `-c·X`
  substituted for its variable, and `signedCatalanSeries_functionalEquation` is
  `T + c·X·T² = 1`, which is one Catalan recurrence in disguise.
* `inverse c := X * signedCatalanSeries c` is the reverted quadratic; the proof
  of `inverse_functionalEquation`, namely `S + c·S² = X`, is the previous
  identity multiplied by `X`.
* `eq_of_functionalEquation` shows that the equation together with a vanishing
  constant term *determines* the series.  This is what makes the equation the
  right hypothesis to reason from: callers hold the equation, not a closed
  form.  From it, `coeff_of_functionalEquation` reads the coefficients off any
  solution, and `seq_succ_of_convolution` does the same for a caller holding
  only the scalar convolution recurrence, who never forms a power series.

Uniqueness applies verbatim to Mathlib's abstract compositional inverse
`PowerSeries.substInv (X + C c * X ^ 2)`, whose defining property
`PowerSeries.subst_substInv_right` becomes this very equation once the
substitution is pushed through the sum and the product.  That identification is
left to whichever caller wants it, so that this file need not import the
substitution machinery.

## Relation to Mathlib

Mathlib has the Catalan numbers with their recurrence, and (in
`Mathlib.RingTheory.PowerSeries.Catalan`) their generating function over `ℕ`,
but no closed form for it and nothing about reverting a quadratic.  Only
`catalan_succ'` is used below.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace QuadraticInverse

variable {R : Type*} [CommRing R]

/-! ### The Catalan generating function at `-c·X` -/

/-- The Catalan generating function with `-c·X` substituted for its variable,
`T = ∑_m (-c)^m · C_m · X^m`.  Shifting it by one factor of `X` reverts
`X + c·X²`. -/
def signedCatalanSeries (c : R) : PowerSeries R :=
  PowerSeries.mk fun m => (-c) ^ m * (catalan m : R)

@[simp]
theorem coeff_signedCatalanSeries (c : R) (n : ℕ) :
    coeff n (signedCatalanSeries c) = (-c) ^ n * (catalan n : R) := by
  simp [signedCatalanSeries]

/-- **The Catalan recurrence with a geometric twist.**  Scaling the two factors
of a Catalan convolution by `(-c)^i` and `(-c)^j` contributes the common factor
`(-c)^(i+j)`, so the twisted convolution is the untwisted one rescaled. -/
theorem sum_antidiagonal_signedCatalan (c : R) (n : ℕ) :
    ∑ p ∈ antidiagonal n,
        ((-c) ^ p.1 * (catalan p.1 : R)) * ((-c) ^ p.2 * (catalan p.2 : R)) =
      (-c) ^ n * (catalan (n + 1) : R) := by
  have hcast : ((catalan (n + 1) : ℕ) : R) =
      ∑ p ∈ antidiagonal n, (catalan p.1 : R) * (catalan p.2 : R) := by
    rw [catalan_succ', Nat.cast_sum]
    exact Finset.sum_congr rfl fun p _ => Nat.cast_mul _ _
  rw [hcast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

/-- The square of the twisted Catalan series carries the *next* Catalan number
in its `n`-th coefficient: this is `catalan_succ'` transported to power
series. -/
theorem coeff_signedCatalanSeries_sq (c : R) (n : ℕ) :
    coeff n (signedCatalanSeries c ^ 2) = (-c) ^ n * (catalan (n + 1) : R) := by
  rw [pow_two, coeff_mul]
  simp only [coeff_signedCatalanSeries]
  exact sum_antidiagonal_signedCatalan c n

/-- **The functional equation of the twisted Catalan series**, `T = 1 - c·X·T²`:
the shape `C = 1 + u·C²` of the Catalan generating function, at `u = -c·X`. -/
theorem signedCatalanSeries_functionalEquation (c : R) :
    signedCatalanSeries c + C c * X * signedCatalanSeries c ^ 2 = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [map_add, mul_assoc, coeff_C_mul, coeff_signedCatalanSeries]
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, mul_zero, add_zero]
    simp
  | succ m =>
    have hone : coeff (m + 1) (1 : PowerSeries R) = 0 := by simp
    rw [coeff_succ_X_mul, coeff_signedCatalanSeries_sq, hone, pow_succ]
    ring

/-! ### The reverted quadratic -/

/-- The compositional inverse of `X + c·X²`: the series with vanishing constant
term whose `(m+1)`-st coefficient is `(-c)^m · C_m`. -/
noncomputable def inverse (c : R) : PowerSeries R := X * signedCatalanSeries c

@[simp]
theorem constantCoeff_inverse (c : R) : constantCoeff (inverse c) = 0 := by
  simp [inverse]

@[simp]
theorem coeff_succ_inverse (c : R) (m : ℕ) :
    coeff (m + 1) (inverse c) = (-c) ^ m * (catalan m : R) := by
  simp [inverse]

/-- **The reverted quadratic solves the quadratic.**  Multiplying
`T + c·X·T² = 1` by `X` turns it into `S + c·S² = X` for `S = X·T`; that is the
entire proof. -/
theorem inverse_functionalEquation (c : R) :
    inverse c + C c * inverse c ^ 2 = X := by
  have key : inverse c + C c * inverse c ^ 2 =
      X * (signedCatalanSeries c + C c * X * signedCatalanSeries c ^ 2) := by
    simp only [inverse]
    ring
  rw [key, signedCatalanSeries_functionalEquation, mul_one]

/-! ### The first coefficients

Read straight off `coeff_succ_inverse`; the same two lines produce any further
order.  Both the alternating sign and the Catalan numbers `1, 1, 2, 5` are
visible here. -/

/-- `[X¹] S = 1`. -/
theorem coeff_one_inverse (c : R) : coeff 1 (inverse c) = 1 := by
  have h : coeff 1 (inverse c) = (-c) ^ 0 * (catalan 0 : R) := coeff_succ_inverse c 0
  rw [h, catalan_zero]
  simp

/-- `[X²] S = -c`. -/
theorem coeff_two_inverse (c : R) : coeff 2 (inverse c) = -c := by
  have h : coeff 2 (inverse c) = (-c) ^ 1 * (catalan 1 : R) := coeff_succ_inverse c 1
  rw [h, catalan_one]
  simp

/-- `[X³] S = 2c²`. -/
theorem coeff_three_inverse (c : R) : coeff 3 (inverse c) = 2 * c ^ 2 := by
  have h : coeff 3 (inverse c) = (-c) ^ 2 * (catalan 2 : R) := coeff_succ_inverse c 2
  rw [h, catalan_two]
  push_cast
  ring

/-- `[X⁴] S = -5c³`. -/
theorem coeff_four_inverse (c : R) : coeff 4 (inverse c) = -(5 * c ^ 3) := by
  have h : coeff 4 (inverse c) = (-c) ^ 3 * (catalan 3 : R) := coeff_succ_inverse c 3
  rw [h, catalan_three]
  push_cast
  ring

/-! ### The equation determines the series -/

/-- The quadratic functional equation read on the `n`-th coefficient: the square
contributes the self-convolution over the antidiagonal.  Every use of the
equation below goes through this one identity. -/
theorem coeff_add_C_mul_sq (c : R) (S : PowerSeries R) (n : ℕ) :
    coeff n (S + C c * S ^ 2) =
      coeff n S + c * ∑ p ∈ antidiagonal n, coeff p.1 S * coeff p.2 S := by
  rw [map_add, coeff_C_mul, pow_two, coeff_mul]

/-- **Uniqueness.**  At most one power series with vanishing constant term
satisfies `S + c·S² = X`.  In the `n`-th coefficient of the equation every
convolution term either carries a factor `coeff 0`, hence vanishes, or has both
of its indices below `n`; so the equation *is* an explicit recursion, and no
invertibility hypothesis is needed to run it. -/
theorem eq_of_functionalEquation {c : R} {S T : PowerSeries R}
    (hS₀ : constantCoeff S = 0) (hT₀ : constantCoeff T = 0)
    (hS : S + C c * S ^ 2 = X) (hT : T + C c * T ^ 2 = X) : S = T := by
  have hS0 : coeff 0 S = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact hS₀
  have hT0 : coeff 0 T = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact hT₀
  refine PowerSeries.ext fun n => ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hSn : coeff n S + c * ∑ p ∈ antidiagonal n, coeff p.1 S * coeff p.2 S =
        coeff n X := by rw [← coeff_add_C_mul_sq, hS]
    have hTn : coeff n T + c * ∑ p ∈ antidiagonal n, coeff p.1 T * coeff p.2 T =
        coeff n X := by rw [← coeff_add_C_mul_sq, hT]
    have hsum : ∑ p ∈ antidiagonal n, coeff p.1 S * coeff p.2 S =
        ∑ p ∈ antidiagonal n, coeff p.1 T * coeff p.2 T := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      by_cases h1 : p.1 = 0
      · rw [h1, hS0, hT0, zero_mul, zero_mul]
      by_cases h2 : p.2 = 0
      · rw [h2, hS0, hT0, mul_zero, mul_zero]
      rw [ih p.1 (by omega), ih p.2 (by omega)]
    rw [hsum] at hSn
    exact add_right_cancel (hSn.trans hTn.symm)

/-- Every solution of the quadratic functional equation with vanishing constant
term *is* the reverted quadratic. -/
theorem eq_inverse {c : R} {S : PowerSeries R} (h₀ : constantCoeff S = 0)
    (h : S + C c * S ^ 2 = X) : S = inverse c :=
  eq_of_functionalEquation h₀ (constantCoeff_inverse c) h (inverse_functionalEquation c)

/-- **The Catalan coefficients of the reverted quadratic.**  Any `S` with
vanishing constant term satisfying `S + c·S² = X` has
`[X^(m+1)] S = (-c)^m · C_m`. -/
theorem coeff_succ_of_functionalEquation {c : R} {S : PowerSeries R}
    (h₀ : constantCoeff S = 0) (h : S + C c * S ^ 2 = X) (m : ℕ) :
    coeff (m + 1) S = (-c) ^ m * (catalan m : R) := by
  rw [eq_inverse h₀ h, coeff_succ_inverse]

/-- The same statement with the sign split off from the geometric factor. -/
theorem coeff_succ_of_functionalEquation' {c : R} {S : PowerSeries R}
    (h₀ : constantCoeff S = 0) (h : S + C c * S ^ 2 = X) (m : ℕ) :
    coeff (m + 1) S = (-1) ^ m * c ^ m * (catalan m : R) := by
  rw [coeff_succ_of_functionalEquation h₀ h, neg_pow]

/-- **The coefficient formula in its classical indexing**: the `m`-th
coefficient of the compositional inverse of `X + c·X²` is
`(-1)^(m-1) · c^(m-1) · C_(m-1)`, for every `m ≥ 1`. -/
theorem coeff_of_functionalEquation {c : R} {S : PowerSeries R}
    (h₀ : constantCoeff S = 0) (h : S + C c * S ^ 2 = X) {m : ℕ} (hm : 1 ≤ m) :
    coeff m S = (-1) ^ (m - 1) * c ^ (m - 1) * (catalan (m - 1) : R) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk]
  exact coeff_succ_of_functionalEquation' h₀ h k

/-! ### Scalar form

A caller who has only a sequence and a convolution recurrence, and never forms
a power series, reaches the same conclusion. -/

/-- **The scalar form of the theorem.**  A sequence `s` vanishing at `0` whose
self-convolution obeys `s n + c · ∑_{i+j=n} s i · s j = [n = 1]` satisfies
`s (m+1) = (-c)^m · C_m`. -/
theorem seq_succ_of_convolution {c : R} {s : ℕ → R} (h₀ : s 0 = 0)
    (h : ∀ n, s n + c * ∑ p ∈ antidiagonal n, s p.1 * s p.2 =
      if n = 1 then 1 else 0) (m : ℕ) :
    s (m + 1) = (-c) ^ m * (catalan m : R) := by
  have hmk : (PowerSeries.mk s : PowerSeries R) + C c * PowerSeries.mk s ^ 2 = X := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_add_C_mul_sq]
    simp only [coeff_mk]
    rw [h n, coeff_X]
  have h0 : constantCoeff (PowerSeries.mk s : PowerSeries R) = 0 := by
    rw [constantCoeff_mk]; exact h₀
  have hcoeff := coeff_succ_of_functionalEquation h0 hmk m
  rwa [coeff_mk] at hcoeff

end QuadraticInverse
