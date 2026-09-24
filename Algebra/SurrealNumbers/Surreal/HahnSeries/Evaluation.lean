import Mathlib.RingTheory.HahnSeries.HEval
import Mathlib.Algebra.Field.GeomSum

/-!
# Admissible univariate Hahn evaluation

The univariate summability and ring-compatibility clauses of `a:cor:complexsub`
and the formal geometric identity `a:eq:geom` in the analysis report.

The definitions and summability proofs come from Mathlib. Its total `heval`
uses evaluation at zero outside the positive-order domain. Our interface
requires the positive-order proof explicitly, and the term formula below
verifies that the resulting family really is the intended substitution.
`orderTop` assigns infinity to zero, so evaluation at zero is included.

The value group is an explicit set-sized parameter. No normal-form bridge,
topological convergence, multivariable evaluation, or compatibility with
composition or differentiation is asserted here.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

section Ring

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- Evaluation on the domain justified by `a:cor:complexsub`. Being an
algebra homomorphism includes compatibility with addition and multiplication. -/
noncomputable def evaluate (x : R⟦Γ⟧) (_hx : 0 < x.orderTop) :
    PowerSeries R →ₐ[R] R⟦Γ⟧ := PowerSeries.heval x

/-- The variable maps to the actual admissible argument. -/
@[simp] theorem evaluate_X (x : R⟦Γ⟧) (hx : 0 < x.orderTop) :
    evaluate x hx PowerSeries.X = x := PowerSeries.heval_X x hx

/-- Arbitrary coefficient sequences, without a growth restriction, give
strongly summable substituted terms (`a:cor:complexsub`, univariate clause). -/
theorem summable_coeff_mul_powers (x : R⟦Γ⟧) (hx : 0 < x.orderTop) (c : ℕ → R) :
    ∃ s : SummableFamily Γ R ℕ, ∀ n, s n = single 0 (c n) * x ^ n := by
  refine ⟨SummableFamily.powerSeriesFamily x (PowerSeries.mk c), ?_⟩
  intro n
  rw [SummableFamily.powerSeriesFamily_of_orderTop_pos hx, PowerSeries.coeff_mk,
    single_zero_mul_eq_smul]

/-- The coefficients of admissible evaluation are finite Hahn coefficient
sums of the intended substituted terms. -/
theorem coeff_evaluate (x : R⟦Γ⟧) (hx : 0 < x.orderTop) (f : PowerSeries R) (g : Γ) :
    (evaluate x hx f).coeff g = ∑ᶠ n, (single 0 (f.coeff n) * x ^ n).coeff g := by
  simp only [evaluate, PowerSeries.coeff_heval, SummableFamily.coeff_def,
    SummableFamily.powerSeriesFamily_of_orderTop_pos hx, single_zero_mul_eq_smul]

/-- Substitution preserves the ordinary constant coefficient. -/
@[simp] theorem coeff_zero_evaluate (x : R⟦Γ⟧) (hx : 0 < x.orderTop) (f : PowerSeries R) :
    (evaluate x hx f).coeff 0 = f.constantCoeff := PowerSeries.coeff_heval_zero x f

/-- The actual family of powers is summable, including the case `x = 0`. -/
theorem summable_powers (x : R⟦Γ⟧) (hx : 0 < x.orderTop) :
    ∃ s : SummableFamily Γ R ℕ, ∀ n, s n = x ^ n :=
  ⟨SummableFamily.powers x, SummableFamily.powers_of_orderTop_pos hx⟩

/-- The geometric identity before division, valid even over a coefficient
ring. This is an algebraic Hahn sum, as required by `a:eq:geom`. -/
theorem geometric_mul (x : R⟦Γ⟧) (hx : 0 < x.orderTop) :
    (1 - x) * (SummableFamily.powers x).hsum = 1 :=
  SummableFamily.one_sub_self_mul_hsum_powers hx

end Ring

section Field

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- The Hahn geometric series formula `a:eq:geom`. -/
theorem geometric_hsum (x : K⟦Γ⟧) (hx : 0 < x.orderTop) :
    (SummableFamily.powers x).hsum = (1 - x)⁻¹ := by
  have h := geometric_mul x hx
  have hne := left_ne_zero_of_mul_eq_one h
  apply mul_left_cancel₀ hne
  rw [h, mul_inv_cancel₀ hne]

/-- The exact finite-partial-sum remainder in `a:ex:geometric`. Its
valuation and failure to converge in the surreal fine topology are separate
claims and require the corresponding value group and topology. -/
theorem geometric_remainder (x : K⟦Γ⟧) (hx : 0 < x.orderTop) (N : ℕ) :
    (SummableFamily.powers x).hsum - ∑ n ∈ Finset.range (N + 1), x ^ n =
      x ^ (N + 1) / (1 - x) := by
  have hne := left_ne_zero_of_mul_eq_one (geometric_mul x hx)
  rw [geometric_hsum x hx]
  apply (eq_div_iff hne).mpr
  rw [sub_mul, inv_mul_cancel₀ hne]
  have h := geom_sum_mul_neg x (N + 1)
  rw [h]
  ring

end Field
end Surreal.HahnSeries
