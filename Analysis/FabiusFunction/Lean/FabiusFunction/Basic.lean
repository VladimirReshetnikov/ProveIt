import FabiusFunction.Arithmetic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Analytic definitions for the Fabius function

This file deliberately separates two functions that are both denoted by `F` in
the literature:

* `BoundedFabius` is the type of cumulative-distribution candidates taking
  values in `[0, 1]`.  `IsFabius` records, among other properties, that the
  function is zero to the left of the unit interval and one to its right.
* `extendedFabius` is the signed smooth extension to all of `ℝ` used in Juan
  Arias de Reyna, *Arithmetic of the Fabius function*, arXiv:1702.06487v3,
  equation (1).  It need not take values in `[0, 1]` outside that interval.

Keeping these objects distinct prevents the global codomain mismatch in the
paper while retaining a convenient subtype-valued API for the bounded
function.  `IsFabius` records the standard characterization used on the unit
interval.  Existence and uniqueness, and the analytic identities relating the
integrals below to the exact rational sequences in `FabiusFunction.Arithmetic`,
are intentionally left to subsequent files.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff
open Set

namespace Fabius

/-- The closed unit interval, used as the codomain of the bounded Fabius function. -/
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- A bounded Fabius candidate, defined on all reals and valued in `[0, 1]`. -/
abbrev BoundedFabius := ℝ → UnitInterval

/-- Forget the interval-valued codomain of a bounded Fabius candidate. -/
abbrev fabiusReal (F : BoundedFabius) : ℝ → ℝ :=
  fun x => F x

@[simp]
theorem fabiusReal_apply (F : BoundedFabius) (x : ℝ) :
    fabiusReal F x = (F x : ℝ) :=
  rfl

/-- Every bounded Fabius candidate is nonnegative after coercion to `ℝ`. -/
theorem fabiusReal_nonneg (F : BoundedFabius) (x : ℝ) :
    0 ≤ fabiusReal F x :=
  (F x).property.1

/-- Every bounded Fabius candidate is at most one after coercion to `ℝ`. -/
theorem fabiusReal_le_one (F : BoundedFabius) (x : ℝ) :
    fabiusReal F x ≤ 1 :=
  (F x).property.2

/--
The standard bounded/CDF characterization of the Fabius function.

The derivative equation is asserted only on `[0, 1/2]`; the global signed
extension has a different role and is defined separately below.
-/
structure IsFabius (F : BoundedFabius) : Prop where
  zero_of_nonpos : ∀ x, x ≤ 0 → fabiusReal F x = 0
  one_of_one_le : ∀ x, 1 ≤ x → fabiusReal F x = 1
  contDiff : ContDiff ℝ ∞ (fabiusReal F)
  symmetry : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    fabiusReal F (1 - x) = 1 - fabiusReal F x
  hasDerivAt : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 * x)) x

/-- The reflection identity in `IsFabius` automatically extends from the
unit interval to all real arguments using the two constant tails. -/
theorem IsFabius.symmetry_all {F : BoundedFabius} (hF : IsFabius F) (x : ℝ) :
    fabiusReal F (1 - x) = 1 - fabiusReal F x := by
  by_cases hx0 : x ≤ 0
  · rw [hF.one_of_one_le (1 - x) (by linarith), hF.zero_of_nonpos x hx0]
    norm_num
  · by_cases hx1 : 1 ≤ x
    · rw [hF.zero_of_nonpos (1 - x) (by linarith), hF.one_of_one_le x hx1]
      norm_num
    · exact hF.symmetry x ⟨le_of_not_ge hx0, le_of_not_ge hx1⟩

/-- A bounded Fabius function bundled with its defining properties. -/
abbrev FabiusFunction := {F : BoundedFabius // IsFabius F}

/--
Rvachev's `up` function obtained by folding the bounded Fabius function about
zero.  Under `IsFabius F`, its support is contained in `[-1, 1]`.
-/
noncomputable def rvachevUp (F : BoundedFabius) (x : ℝ) : ℝ :=
  if x ≤ 0 then fabiusReal F (x + 1) else fabiusReal F (1 - x)

/-!
## Elementary values and bounds for Rvachev's function

These facts require no calculus: they follow from the two branches of the
definition of `rvachevUp` together with the unit-interval codomain of
`BoundedFabius`.  Collecting them next to the definition avoids the four
separate re-derivations that previously appeared downstream.
-/

/-- Unfolding of `rvachevUp` on the left branch. -/
theorem rvachevUp_of_nonpos (F : BoundedFabius) {x : ℝ} (hx : x ≤ 0) :
    rvachevUp F x = fabiusReal F (x + 1) := by
  rw [rvachevUp, if_pos hx]

/-- Unfolding of `rvachevUp` on the right branch. -/
theorem rvachevUp_of_pos (F : BoundedFabius) {x : ℝ} (hx : 0 < x) :
    rvachevUp F x = fabiusReal F (1 - x) := by
  rw [rvachevUp, if_neg (by linarith : ¬ x ≤ 0)]

/-- Rvachev's up function is nonnegative. -/
theorem rvachevUp_nonneg (F : BoundedFabius) (x : ℝ) : 0 ≤ rvachevUp F x := by
  rw [rvachevUp]
  split_ifs <;> exact fabiusReal_nonneg F _

/-- Rvachev's up function is at most one. -/
theorem rvachevUp_le_one (F : BoundedFabius) (x : ℝ) : rvachevUp F x ≤ 1 := by
  rw [rvachevUp]
  split_ifs <;> exact fabiusReal_le_one F _

/-- Rvachev's up function coincides with its own absolute value. -/
theorem abs_rvachevUp (F : BoundedFabius) (x : ℝ) :
    |rvachevUp F x| = rvachevUp F x :=
  abs_of_nonneg (rvachevUp_nonneg F x)

/-- Rvachev's up function is bounded by one in absolute value. -/
theorem abs_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    |rvachevUp F x| ≤ 1 := by
  rw [abs_rvachevUp]
  exact rvachevUp_le_one F x

/-- Rvachev's up function is bounded by one in norm. -/
theorem norm_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    ‖rvachevUp F x‖ ≤ 1 :=
  abs_rvachevUp_le_one F x

/-- Rvachev's up function takes its normalized value at the origin. -/
theorem rvachevUp_zero (F : BoundedFabius) (hF : IsFabius F) :
    rvachevUp F 0 = 1 := by
  rw [rvachevUp, if_pos le_rfl]
  simpa using hF.one_of_one_le 1 le_rfl

/-- The complex cast of Rvachev's up function is bounded by one in norm. -/
theorem norm_ofReal_rvachevUp_le_one (F : BoundedFabius) (x : ℝ) :
    ‖(rvachevUp F x : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using abs_rvachevUp_le_one F x

/--
The signed global extension from equation (1) of Arias de Reyna's paper:
`F(x) = ∑ n, (-1)^w(n) up(x - 2n - 1)`.

For a function satisfying `IsFabius`, the summand is pointwise supported at
only finitely many indices.  The summability and agreement with the bounded
function on `[0, 1]` are exposed as later theorems rather than built into the
definition.
-/
noncomputable def extendedFabius (F : BoundedFabius) (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ binaryWeight n *
    rvachevUp F (x - 2 * (n : ℝ) - 1)

/-- The removable entire function `sin z / z`, normalized to `1` at zero. -/
noncomputable def complexSinc (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin z / z

/-- The Fourier transform of Rvachev's function, with the paper's convention. -/
noncomputable def rvachevFourier (F : BoundedFabius) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (rvachevUp F t : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I * t * z)

/-- The infinite sinc product in equation (5). -/
noncomputable def rvachevFourierProduct (z : ℂ) : ℂ :=
  ∏' n : ℕ, complexSinc (Real.pi * z / (2 : ℂ) ^ n)

/-- The moment power series on the right side of equation (7). -/
noncomputable def rvachevMomentSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * (moment n : ℂ) /
    (Nat.factorial (2 * n) : ℂ) * (2 * Real.pi * z) ^ (2 * n)

/-- The exponential generating series `∑ d_n z^n / n!` in equation (17). -/
noncomputable def halfMomentGeneratingSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (halfMoment n : ℂ) / (n.factorial : ℂ) * z ^ n

/-- The removable extension of `(exp x - 1) / x`, with value `1` at zero. -/
noncomputable def expm1Div (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.exp x - 1) / x

@[simp]
theorem expm1Div_zero : expm1Div 0 = 1 := by
  simp [expm1Div]

theorem expm1Div_of_ne {x : ℝ} (hx : x ≠ 0) :
    expm1Div x = (Real.exp x - 1) / x := by
  simp [expm1Div, hx]

/-- The complex removable extension of `(exp z - 1) / z`. -/
noncomputable def complexExpm1Div (z : ℂ) : ℂ :=
  if z = 0 then 1 else (Complex.exp z - 1) / z

@[simp]
theorem complexExpm1Div_zero : complexExpm1Div 0 = 1 := by
  simp [complexExpm1Div]

theorem complexExpm1Div_of_ne {z : ℂ} (hz : z ≠ 0) :
    complexExpm1Div z = (Complex.exp z - 1) / z := by
  simp [complexExpm1Div, hz]

/-- The even moment `∫_ℝ t^(2n) up(t) dt`, denoted `c_n` in the paper. -/
noncomputable def momentIntegral (F : BoundedFabius) (n : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ (2 * n) * rvachevUp F t

/--
The half moment denoted `d_n` in the paper.  Its zeroth term is normalized to
`1`; at a successor index it is `(n+1) ∫_0^1 t^n up(t) dt`.
-/
noncomputable def halfMomentIntegral (F : BoundedFabius) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      ((n + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..1, t ^ n * rvachevUp F t

@[simp]
theorem halfMomentIntegral_zero (F : BoundedFabius) :
    halfMomentIntegral F 0 = 1 :=
  rfl

@[simp]
theorem halfMomentIntegral_succ (F : BoundedFabius) (n : ℕ) :
    halfMomentIntegral F (n + 1) =
      ((n + 1 : ℕ) : ℝ) * ∫ t in (0 : ℝ)..1, t ^ n * rvachevUp F t :=
  rfl

/--
The exponential generating function
`1 + x ∫_0^1 up(t) exp(x t) dt` used to define the half moments.
-/
noncomputable def generatingFunction (F : BoundedFabius) (x : ℝ) : ℝ :=
  1 + x * ∫ t in (0 : ℝ)..1, rvachevUp F t * Real.exp (x * t)

/--
The entire complex generating function used in Proposition 2.  Its
restriction to the real axis is `generatingFunction` after the usual cast.
-/
noncomputable def complexGeneratingFunction (F : BoundedFabius) (z : ℂ) : ℂ :=
  1 + z * ∫ t in (0 : ℝ)..1,
    (rvachevUp F t : ℂ) * Complex.exp (z * t)

end Fabius
