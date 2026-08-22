import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact formal Lambert cocycles

This file isolates the coefficientwise algebra behind

`H_{A,M}(X) = \sum_{n >= 1} (M^n - 1) / (A^n - 1) X^n`.

All series below are formal power series. Thus the identities require no
convergence, meromorphic continuation, or common-exponent relation between
the parameters.
-/

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

open PowerSeries

variable {F : Type*} [Field F]

/-- The `n`th Lambert quotient. At `n = 0`, Lean's totalized division gives
`0 / 0 = 0`, which is the desired zero constant coefficient. -/
def lambertCoeff (A M : F) (n : ℕ) : F :=
  (M ^ n - 1) / (A ^ n - 1)

/-- The formal Lambert series with coefficients
`(M^n - 1) / (A^n - 1)`. -/
def formalLambertSeries (A M : F) : PowerSeries F :=
  PowerSeries.mk (lambertCoeff A M)

/-- Formal substitution `X ↦ cX`, followed by subtraction of the original
series. This is the coefficientwise dilation operator `Δ_c`. -/
def seriesDilationDifference (c : F) (H : PowerSeries F) : PowerSeries F :=
  PowerSeries.rescale c H - H

/-- The formal geometric series `1 + X + X^2 + ...`. -/
def formalGeometricSeries : PowerSeries F :=
  PowerSeries.mk fun _ ↦ 1

/-- The rational formal series whose `n`th coefficient is `M^n - 1`.
Analytically it is `MX/(1-MX) - X/(1-X)`. -/
def lambertRationalCocycle (M : F) : PowerSeries F :=
  PowerSeries.rescale M formalGeometricSeries - formalGeometricSeries

@[simp]
theorem lambertCoeff_zero (A M : F) : lambertCoeff A M 0 = 0 := by
  simp [lambertCoeff]

@[simp]
theorem coeff_formalLambertSeries (A M : F) (n : ℕ) :
    PowerSeries.coeff n (formalLambertSeries A M) = lambertCoeff A M n := by
  simp [formalLambertSeries]

@[simp]
theorem coeff_seriesDilationDifference (c : F) (H : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (seriesDilationDifference c H) =
      (c ^ n - 1) * PowerSeries.coeff n H := by
  simp [seriesDilationDifference]
  ring

@[simp]
theorem coeff_formalGeometricSeries (n : ℕ) :
    PowerSeries.coeff n (formalGeometricSeries : PowerSeries F) = 1 := by
  simp [formalGeometricSeries]

@[simp]
theorem coeff_lambertRationalCocycle (M : F) (n : ℕ) :
    PowerSeries.coeff n (lambertRationalCocycle M) = M ^ n - 1 := by
  simp [lambertRationalCocycle]

/-- Clearing the native denominator gives the rational cocycle coefficient. -/
theorem lambertCoeff_native_dilation (A M : F) (n : ℕ)
    (hA : A ^ n ≠ 1) :
    (A ^ n - 1) * lambertCoeff A M n = M ^ n - 1 := by
  rw [lambertCoeff]
  exact mul_div_cancel₀ _ (sub_ne_zero.mpr hA)

/-- The coefficient identity behind the mixed double-difference equation.
It is symmetric for arbitrary `A,M,B,N`; no common exponent is used. -/
theorem mixedDoubleDilation_lambertCoeff_universal
    (A M B N : F) (n : ℕ) (hA : A ^ n ≠ 1) (hB : B ^ n ≠ 1) :
    (N ^ n - 1) * (A ^ n - 1) * lambertCoeff A M n =
      (M ^ n - 1) * (B ^ n - 1) * lambertCoeff B N n := by
  calc
    (N ^ n - 1) * (A ^ n - 1) * lambertCoeff A M n =
        (N ^ n - 1) * (M ^ n - 1) := by
          rw [mul_assoc, lambertCoeff_native_dilation A M n hA]
    _ = (M ^ n - 1) * (N ^ n - 1) := by ring
    _ = (M ^ n - 1) * (B ^ n - 1) * lambertCoeff B N n := by
          rw [mul_assoc, lambertCoeff_native_dilation B N n hB]

/-- `formalGeometricSeries` is the inverse of `1-X`. -/
theorem formalGeometricSeries_mul_one_sub_X :
    (formalGeometricSeries : PowerSeries F) * (1 - PowerSeries.X) = 1 := by
  ext (_ | n) <;> simp [formalGeometricSeries, mul_sub]

/-- After rescaling, the geometric series is the inverse of `1-cX`. -/
theorem rescale_formalGeometricSeries_mul_one_sub_C_mul_X (c : F) :
    PowerSeries.rescale c (formalGeometricSeries : PowerSeries F) *
        (1 - PowerSeries.C c * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale c)
    (formalGeometricSeries_mul_one_sub_X (F := F))
  simpa [map_sub] using h

/-- The rational presentation
`R_M(X) = MX/(1-MX) - X/(1-X)` of the cocycle series. -/
theorem lambertRationalCocycle_eq (M : F) :
    lambertRationalCocycle M =
      PowerSeries.C M *
          (PowerSeries.X * PowerSeries.rescale M formalGeometricSeries) -
        PowerSeries.X * formalGeometricSeries := by
  ext n
  rw [coeff_lambertRationalCocycle]
  cases n with
  | zero => simp [formalGeometricSeries]
  | succ n =>
    simp [formalGeometricSeries, pow_succ]
    ring

/-- Exact formal-series identity `Δ_A H_{A,M} = R_M`.

The only denominator hypothesis says that positive powers of `A` occurring in
the Lambert coefficients are not one. -/
theorem seriesDilationDifference_formalLambertSeries
    (A M : F) (hA : ∀ n : ℕ, 0 < n → A ^ n ≠ 1) :
    seriesDilationDifference A (formalLambertSeries A M) =
      lambertRationalCocycle M := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [coeff_seriesDilationDifference, coeff_formalLambertSeries,
      coeff_lambertRationalCocycle,
      lambertCoeff_native_dilation A M n (hA n (Nat.pos_of_ne_zero hn))]

/-- Applying a second dilation to a rational cocycle multiplies its `n`th
coefficient by the second factor `N^n - 1`. -/
theorem coeff_secondDilation_lambertRationalCocycle (M N : F) (n : ℕ) :
    PowerSeries.coeff n
        (seriesDilationDifference N (lambertRationalCocycle M)) =
      (N ^ n - 1) * (M ^ n - 1) := by
  simp

/-- The mixed rational cocycle is symmetric in `M,N`. -/
theorem secondDilation_lambertRationalCocycle_commute (M N : F) :
    seriesDilationDifference N (lambertRationalCocycle M) =
      seriesDilationDifference M (lambertRationalCocycle N) := by
  ext n
  simp [mul_comm]

/-- Closed four-term form of the mixed rational cocycle. Its analytic
notation is

`MN X/(1-MN X) - M X/(1-M X) - N X/(1-N X) + X/(1-X)`.
-/
theorem secondDilation_lambertRationalCocycle_eq (M N : F) :
    seriesDilationDifference N (lambertRationalCocycle M) =
      PowerSeries.rescale (M * N) formalGeometricSeries -
        PowerSeries.rescale M formalGeometricSeries -
        PowerSeries.rescale N formalGeometricSeries +
        formalGeometricSeries := by
  simp only [seriesDilationDifference, lambertRationalCocycle, map_sub,
    PowerSeries.rescale_rescale]
  ring

/-- **Universal mixed double-difference identity.** For arbitrary
`A,M,B,N`, the two sides are equal whenever the native Lambert denominators
are nonzero. No relation between `A,M,B,N` is used. In particular, the
identity does not encode a common real exponent. -/
theorem mixedDoubleDilation_formalLambertSeries_universal
    (A M B N : F)
    (hA : ∀ n : ℕ, 0 < n → A ^ n ≠ 1)
    (hB : ∀ n : ℕ, 0 < n → B ^ n ≠ 1) :
    seriesDilationDifference N
        (seriesDilationDifference A (formalLambertSeries A M)) =
      seriesDilationDifference M
        (seriesDilationDifference B (formalLambertSeries B N)) := by
  rw [seriesDilationDifference_formalLambertSeries A M hA,
    seriesDilationDifference_formalLambertSeries B N hB]
  exact secondDilation_lambertRationalCocycle_commute M N

/-- The base-`2`, base-`3` specialization over `ℚ`. It holds for every pair
`M,N : ℚ`; in particular there is no hypothesis that they are powers with a
common exponent. -/
theorem mixedDoubleDilation_two_three_universal (M N : ℚ) :
    seriesDilationDifference N
        (seriesDilationDifference 2 (formalLambertSeries 2 M)) =
      seriesDilationDifference M
        (seriesDilationDifference 3 (formalLambertSeries 3 N)) := by
  apply mixedDoubleDilation_formalLambertSeries_universal
  · intro n hn
    exact ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (Nat.ne_of_gt hn))
  · intro n hn
    exact ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 3) (Nat.ne_of_gt hn))

end

end LeanProofs.TwoBaseIntegerExponent
