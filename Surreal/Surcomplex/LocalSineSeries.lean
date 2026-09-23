import Surreal.Surcomplex.InfinitesimalPhase

/-!
# Verified centered sine series at actual infinitesimal angles

The actual strong series of `sin(θ+H)-sin θ` has zero constant term and
unit linear coefficient `cos θ`. These facts supply the formal angular
coordinate change used for multiplicity in `trigonometry:sec:coupled`.
-/

universe u

namespace Surreal.Surcomplex

noncomputable section

/-- Sine addition holds throughout the actual complex infinitesimal monad. -/
theorem infSin_add (z w : Surcomplex.{u}) (hz : IsInfinitesimal z) (hw : IsInfinitesimal w) :
    infSin (z + w) (infinitesimal_add hz hw) =
      infSin z hz * infCos w hw + infCos z hz * infSin w hw := by
  have h := infinitesimalPhase_add z w hz hw
  rw [infinitesimalPhase_eq, infinitesimalPhase_eq, infinitesimalPhase_eq,
    infCos_add z w hz hw] at h
  have hi : (I : Surcomplex.{u}) ≠ 0 := by
    intro he
    have hh : (I : Surcomplex.{u}) ^ 2 = -1 := I_sq
    rw [he] at hh
    norm_num at hh
  apply mul_left_cancel₀ hi
  linear_combination h + infSin z hz * infSin w hw * I_sq

/-- The local increment series with actual surcomplex coefficients. -/
def localSinSeries (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    PowerSeries Surcomplex.{u} :=
  PowerSeries.C (infCos θ hθ) * PowerSeries.map ofComplex Analytic.complexSinSeries +
    PowerSeries.C (infSin θ hθ) * PowerSeries.map ofComplex (Analytic.complexCosSeries - 1)

private theorem localSinSeries_term (θ h : Surcomplex.{u}) (hθ : IsInfinitesimal θ) (n : ℕ) :
    (localSinSeries θ hθ).coeff n * h ^ n =
      infCos θ hθ * (ofComplex (Analytic.complexSinSeries.coeff n) * h ^ n) +
        infSin θ hθ * (ofComplex ((Analytic.complexCosSeries - 1).coeff n) * h ^ n) := by
  simp only [localSinSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  ring

/-- The literal local sine terms are strongly summable at every infinitesimal increment. -/
theorem stronglySummable_localSinSeries (θ h : Surcomplex.{u})
    (hθ : IsInfinitesimal θ) (hh : IsInfinitesimal h) :
    StronglySummable (fun n => (localSinSeries θ hθ).coeff n * h ^ n) := by
  simp only [localSinSeries_term]
  exact ((stronglySummable_powerSeries h hh Analytic.complexSinSeries).const_mul _).add
    ((stronglySummable_powerSeries h hh (Analytic.complexCosSeries - 1)).const_mul _)

/-- This formal series represents the actual centered sine function, not just its derivative. -/
theorem strongSum_localSinSeries (θ h : Surcomplex.{u})
    (hθ : IsInfinitesimal θ) (hh : IsInfinitesimal h) :
    strongSum (fun n => (localSinSeries θ hθ).coeff n * h ^ n)
      (stronglySummable_localSinSeries θ h hθ hh) =
      infSin (θ + h) (infinitesimal_add hθ hh) - infSin θ hθ := by
  have hs := stronglySummable_powerSeries h hh Analytic.complexSinSeries
  have hc := stronglySummable_powerSeries h hh (Analytic.complexCosSeries - 1)
  have he := strongSum_add (hs.const_mul (infCos θ hθ)) (hc.const_mul (infSin θ hθ))
  rw [strongSum_const_mul hs (infCos θ hθ), strongSum_const_mul hc (infSin θ hθ),
    ← powerSeriesEvaluation_eq_strongSum, ← powerSeriesEvaluation_eq_strongSum] at he
  have hfamily := funext (localSinSeries_term θ h hθ)
  calc
    _ = _ := by simpa only [hfamily] using he
    _ = _ := by
      rw [map_sub, map_one, infSin_add θ h hθ hh]
      change infCos θ hθ * infSin h hh + infSin θ hθ * (infCos h hh - 1) = _
      ring

@[simp] theorem constantCoeff_localSinSeries (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    (localSinSeries θ hθ).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [localSinSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

@[simp] theorem coeff_localSinSeries_one (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    (localSinSeries θ hθ).coeff 1 = infCos θ hθ := by
  simp [localSinSeries, PowerSeries.coeff_C_mul]

/-- The formal linear term is a unit at every actual infinitesimal center. -/
theorem isUnit_linear_localSinSeries (θ : Surcomplex.{u}) (hθ : IsInfinitesimal θ) :
    IsUnit ((localSinSeries θ hθ).coeff 1) := by
  rw [coeff_localSinSeries_one, isUnit_iff_ne_zero]
  exact infCos_ne_zero θ hθ

end
end Surreal.Surcomplex
