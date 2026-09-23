import Surreal.Algebra.CosineFoldPolynomial
import Surreal.Surcomplex.CosineFoldDerivative
import Surreal.Surcomplex.InfinitesimalPhase

/-!
# Angular multiplicities of the actual cosine fold

The exact local angular series is strongly summable and evaluates to the
cosine difference. Its order is one at a separated root and two at the
collision. Euler's identity identifies the manuscript's exponential
polynomial coordinate; the corresponding native polynomial multiplicities
are exactly those orders. This closes the multiplicity clauses of
`trigonometry:thm:fold`, using the convention of `trigonometry:thm:polyroots`.
-/

universe u
namespace Surreal.Surcomplex.CosineFold

open Foundations
noncomputable section

/-- The actual local series of `cos(θ+H)-cos θ` in the angular increment. -/
def localSeries (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) : PowerSeries Surcomplex.{u} :=
  PowerSeries.C (infCos θ hθ) *
      PowerSeries.map ofComplex (Analytic.complexCosSeries - 1) -
    PowerSeries.C (infSin θ hθ) * PowerSeries.map ofComplex Analytic.complexSinSeries

private theorem localSeries_term (θ h : Surcomplex.{u}) (hθ : IsInfinitesimal θ) (n : ℕ) :
    (localSeries θ hθ).coeff n * h ^ n =
      infCos θ hθ * (ofComplex ((Analytic.complexCosSeries - 1).coeff n) * h ^ n) +
        -(infSin θ hθ * (ofComplex (Analytic.complexSinSeries.coeff n) * h ^ n)) := by
  simp only [localSeries, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  ring

/-- The literal local Taylor terms form an actual strong sum at every infinitesimal increment. -/
theorem stronglySummable_localSeries (θ h : Surcomplex.{u})
    (hθ : IsInfinitesimal θ) (hh : IsInfinitesimal h) :
    StronglySummable (fun n => (localSeries θ hθ).coeff n * h ^ n) := by
  simp only [localSeries_term]
  exact ((stronglySummable_powerSeries h hh (Analytic.complexCosSeries - 1)).const_mul _).add
    ((stronglySummable_powerSeries h hh Analytic.complexSinSeries).const_mul _).neg

/-- The local series represents the actual cosine difference, with no convergence assumption. -/
theorem strongSum_localSeries (θ h : Surcomplex.{u})
    (hθ : IsInfinitesimal θ) (hh : IsInfinitesimal h) :
    strongSum (fun n => (localSeries θ hθ).coeff n * h ^ n)
      (stronglySummable_localSeries θ h hθ hh) =
      infCos (θ + h) (infinitesimal_add hθ hh) - infCos θ hθ := by
  have hc := stronglySummable_powerSeries h hh (Analytic.complexCosSeries - 1)
  have hs := stronglySummable_powerSeries h hh Analytic.complexSinSeries
  have he := strongSum_add (hc.const_mul (infCos θ hθ))
    (hs.const_mul (infSin θ hθ)).neg
  rw [strongSum_neg (hs.const_mul (infSin θ hθ)),
    strongSum_const_mul hc (infCos θ hθ), strongSum_const_mul hs (infSin θ hθ),
    ← powerSeriesEvaluation_eq_strongSum, ← powerSeriesEvaluation_eq_strongSum] at he
  have hfamily := funext (localSeries_term θ h hθ)
  calc
    _ = _ := by simpa only [hfamily] using he
    _ = infCos (θ + h) (infinitesimal_add hθ hh) - infCos θ hθ := by
      rw [map_sub, map_one, infCos_add θ h hθ hh]
      change infCos θ hθ * (infCos h hh - 1) + -(infSin θ hθ * infSin h hh) = _
      ring

@[simp] theorem coeff_localSeries_zero (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    (localSeries θ hθ).coeff 0 = 0 := by
  simp only [localSeries, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

@[simp] theorem coeff_localSeries_one (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    (localSeries θ hθ).coeff 1 = -infSin θ hθ := by
  simp [localSeries, PowerSeries.coeff_C_mul]

/-- A separated actual root has a simple zero of its verified local angular series. -/
theorem localSeries_order_one (τ θ : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hτ0 : τ ≠ 0) (hθ : IsInfinitesimal θ) (he : infCos θ hθ = 1 - τ) :
    (localSeries θ hθ).order = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · rw [coeff_localSeries_one]
    exact derivative_ne_zero_at_root τ θ hτ hτ0 hθ he
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    exact coeff_localSeries_zero θ hθ

/-- At collision the verified actual angular series has a double zero. -/
theorem localSeries_order_at_collision :
    (localSeries (0 : Surcomplex.{u}) infinitesimal_zero).order = 2 := by
  simpa only [localSeries, infCos_zero, infSin_zero, map_one, map_zero, one_mul,
    zero_mul, sub_zero] using actual_collision_series_order.{u}

/-- Clearing the Laurent denominator gives the manuscript's quadratic polynomial. -/
theorem polynomial_eval_phase (τ θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    (CosineFoldPolynomial.polynomial τ).eval (infinitesimalPhase θ hθ) =
      2 * infinitesimalPhase θ hθ * (infCos θ hθ - (1 - τ)) := by
  rw [CosineFoldPolynomial.eval_polynomial, infCos_eq_phase]
  have hu := infinitesimalPhase_ne_zero θ hθ
  field_simp [hu]
  ring

/-- Roots correspond exactly to roots of the quadratic at the nonzero exponential coordinate. -/
theorem polynomial_root_iff (τ θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    (CosineFoldPolynomial.polynomial τ).eval (infinitesimalPhase θ hθ) = 0 ↔
      infCos θ hθ = 1 - τ := by
  rw [polynomial_eval_phase, mul_eq_zero]
  have hn : 2 * infinitesimalPhase θ hθ ≠ 0 :=
    mul_ne_zero (by norm_num) (infinitesimalPhase_ne_zero θ hθ)
  simp only [hn, false_or, sub_eq_zero]

/-- At a fold root the polynomial derivative is `2i sin θ`. -/
theorem polynomial_derivative_at_root (τ θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ)
    (he : infCos θ hθ = 1 - τ) :
    (CosineFoldPolynomial.polynomial τ).derivative.eval (infinitesimalPhase θ hθ) =
      2 * I * infSin θ hθ := by
  rw [CosineFoldPolynomial.eval_derivative, infinitesimalPhase_eq, he]
  ring

/-- Every separated root has polynomial multiplicity one in the source's angular coordinate. -/
theorem polynomial_multiplicity_one (τ θ : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hτ0 : τ ≠ 0) (hθ : IsInfinitesimal θ) (he : infCos θ hθ = 1 - τ) :
    (CosineFoldPolynomial.polynomial τ).rootMultiplicity (infinitesimalPhase θ hθ) = 1 := by
  apply CosineFoldPolynomial.multiplicity_one _ _ ((polynomial_root_iff τ θ hθ).mpr he)
  rw [polynomial_derivative_at_root τ θ hθ he]
  apply mul_ne_zero
  · apply mul_ne_zero (by norm_num)
    intro hi
    have hsq : (I : Surcomplex.{u}) ^ 2 = -1 := I_sq
    rw [hi] at hsq
    norm_num at hsq
  · exact neg_ne_zero.mp (derivative_ne_zero_at_root τ θ hτ hτ0 hθ he)

/-- At zero the angular polynomial has multiplicity two at the actual exponential coordinate. -/
theorem polynomial_multiplicity_at_collision :
    (CosineFoldPolynomial.polynomial (0 : Surcomplex.{u})).rootMultiplicity
      (infinitesimalPhase 0 infinitesimal_zero) = 2 := by
  rw [infinitesimalPhase_zero]
  exact CosineFoldPolynomial.multiplicity_at_collision

/-- The local angular order agrees with the native polynomial multiplicity, and gives 2 or 1. -/
theorem angular_multiplicity (τ θ : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hθ : IsInfinitesimal θ) (he : infCos θ hθ = 1 - τ) :
    (localSeries θ hθ).order =
        ((CosineFoldPolynomial.polynomial τ).rootMultiplicity (infinitesimalPhase θ hθ) : ℕ∞) ∧
      (CosineFoldPolynomial.polynomial τ).rootMultiplicity (infinitesimalPhase θ hθ) =
        if τ = 0 then 2 else 1 := by
  by_cases hτ0 : τ = 0
  · subst τ
    have hzero : θ = 0 := (zero_solution_iff θ hθ).mp (by simpa only [sub_zero] using he)
    subst θ
    simp only [localSeries_order_at_collision, polynomial_multiplicity_at_collision,
      if_true, Nat.cast_ofNat, and_self]
  · rw [localSeries_order_one τ θ hτ hτ0 hθ he,
      polynomial_multiplicity_one τ θ hτ hτ0 hθ he, if_neg hτ0]
    simp
/-- The exact Laurent-algebraization polynomial has the same local angular multiplicity. -/
theorem angular_multiplicity_laurent (τ θ : Surcomplex.{u}) (hτ : IsInfinitesimal τ)
    (hθ : IsInfinitesimal θ) (he : infCos θ hθ = 1 - τ) :
    (localSeries θ hθ).order =
        ((CosineFoldPolynomial.laurentPolynomial τ).rootMultiplicity
          (infinitesimalPhase θ hθ) : ℕ∞) ∧
      (CosineFoldPolynomial.laurentPolynomial τ).rootMultiplicity (infinitesimalPhase θ hθ) =
        if τ = 0 then 2 else 1 := by
  rw [CosineFoldPolynomial.multiplicity_laurentPolynomial τ _ (by norm_num)]
  exact angular_multiplicity τ θ hτ hθ he

/-- At every root the local angular strong sum is the original fold equation at the shifted angle. -/
theorem strongSum_localSeries_at_root (τ θ h : Surcomplex.{u})
    (hθ : IsInfinitesimal θ) (hh : IsInfinitesimal h) (he : infCos θ hθ = 1 - τ) :
    strongSum (fun n => (localSeries θ hθ).coeff n * h ^ n)
      (stronglySummable_localSeries θ h hθ hh) =
      infCos (θ + h) (infinitesimal_add hθ hh) - (1 - τ) := by
  rw [strongSum_localSeries θ h hθ hh, he]

end
end Surreal.Surcomplex.CosineFold
