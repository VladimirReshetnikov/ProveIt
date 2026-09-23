import Surreal.Surcomplex.CoupledAngularRoots
import Surreal.Surcomplex.PowerSeriesDerivative

/-!
# The actual angular Jacobian and its collision locus

For `trigonometry:sec:coupled`, each entry of the displayed Jacobian is
verified as an actual fine partial derivative. Its determinant is the
source's `2 cos(α) cos(β) X Y`; on a solution it vanishes exactly when
`s²-4u²=0`. The nonzero cosine factors require only infinitesimal angles.
-/

universe u

namespace Surreal.Surcomplex.CoupledAngular

noncomputable section

/-- The actual sine germ has cosine as its fine derivative everywhere in the monad. -/
theorem fineHasDerivAt_sin (α : Surcomplex.{u}) (hα : IsInfinitesimal α) :
    FineHasDerivAt (powerSeriesFunction Analytic.complexSinSeries) (infCos α hα) α := by
  have h := fineHasDerivAt_powerSeriesFunction Analytic.complexSinSeries α hα
  rw [Analytic.derivative_complexSinSeries] at h
  exact h

/-- A total extension of the two equations from the open infinitesimal monad. -/
def system (s t : Surcomplex.{u}) (p : Surcomplex.{u} × Surcomplex.{u}) :
    Surcomplex.{u} × Surcomplex.{u} :=
  let x := powerSeriesFunction Analytic.complexSinSeries p.1
  let y := powerSeriesFunction Analytic.complexSinSeries p.2
  (x ^ 2 + y ^ 2 - s, x * y - t)

/-- Rows correspond to the two equations and columns to the two angle variables. -/
def jacobian (α β : Surcomplex.{u}) (hα : IsInfinitesimal α) (hβ : IsInfinitesimal β) :
    Matrix (Fin 2) (Fin 2) Surcomplex.{u} :=
  !![2 * infSin α hα * infCos α hα, 2 * infSin β hβ * infCos β hβ;
     infCos α hα * infSin β hβ, infSin α hα * infCos β hβ]

/-- The first row consists of genuine fine partial derivatives of the first equation. -/
theorem fine_partials_first (s t α β : Surcomplex.{u})
    (hα : IsInfinitesimal α) (hβ : IsInfinitesimal β) :
    FineHasDerivAt (fun a => (system s t (a, β)).1) (jacobian α β hα hβ 0 0) α ∧
    FineHasDerivAt (fun b => (system s t (α, b)).1) (jacobian α β hα hβ 0 1) β := by
  constructor
  · simpa [system, jacobian, powerSeriesFunction_of_isInfinitesimal _ α hα, infSin] using
      (((fineHasDerivAt_sin α hα).pow 2).add
        (FineHasDerivAt.const ((powerSeriesFunction Analytic.complexSinSeries β) ^ 2) α)).sub
          (FineHasDerivAt.const s α)
  · simpa [system, jacobian, powerSeriesFunction_of_isInfinitesimal _ β hβ, infSin] using
      ((FineHasDerivAt.const ((powerSeriesFunction Analytic.complexSinSeries α) ^ 2) β).add
        ((fineHasDerivAt_sin β hβ).pow 2)).sub (FineHasDerivAt.const s β)

/-- The second row consists of genuine fine partial derivatives of the second equation. -/
theorem fine_partials_second (s t α β : Surcomplex.{u})
    (hα : IsInfinitesimal α) (hβ : IsInfinitesimal β) :
    FineHasDerivAt (fun a => (system s t (a, β)).2) (jacobian α β hα hβ 1 0) α ∧
    FineHasDerivAt (fun b => (system s t (α, b)).2) (jacobian α β hα hβ 1 1) β := by
  constructor
  · simpa [system, jacobian, powerSeriesFunction_of_isInfinitesimal _ β hβ, infSin] using
      ((fineHasDerivAt_sin α hα).mul
        (FineHasDerivAt.const (powerSeriesFunction Analytic.complexSinSeries β) α)).sub
          (FineHasDerivAt.const t α)
  · simpa [system, jacobian, powerSeriesFunction_of_isInfinitesimal _ α hα, infSin] using
      ((FineHasDerivAt.const (powerSeriesFunction Analytic.complexSinSeries α) β).mul
        (fineHasDerivAt_sin β hβ)).sub (FineHasDerivAt.const t β)

/-- The determinant is the claimed unit factor times the two diagonal coordinates. -/
theorem det_jacobian (α β : Surcomplex.{u}) (hα : IsInfinitesimal α)
    (hβ : IsInfinitesimal β) :
    (jacobian α β hα hβ).det = 2 * infCos α hα * infCos β hβ *
      (infSin α hα + infSin β hβ) * (infSin α hα - infSin β hβ) := by
  simp only [jacobian, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The cosine factors are units everywhere in the infinitesimal monad. -/
theorem cosine_factor_isUnit (α β : Surcomplex.{u}) (hα : IsInfinitesimal α)
    (hβ : IsInfinitesimal β) : IsUnit (2 * infCos α hα * infCos β hβ) := by
  exact isUnit_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) (infCos_ne_zero α hα)) (infCos_ne_zero β hβ))

/-- At every angular root, singularity is exactly the discriminant equation in parameter space. -/
theorem det_jacobian_eq_zero_iff (s t α β : Surcomplex.{u})
    (hα : IsInfinitesimal α) (hβ : IsInfinitesimal β)
    (he : Equations s t (infSin α hα) (infSin β hβ)) :
    (jacobian α β hα hβ).det = 0 ↔ s ^ 2 - 4 * t ^ 2 = 0 := by
  have h := (equations_iff _ _ _ _).mp he
  have hd : (infSin α hα + infSin β hβ) ^ 2 *
      (infSin α hα - infSin β hβ) ^ 2 = s ^ 2 - 4 * t ^ 2 := by
    rw [h.1, h.2]; ring
  rw [det_jacobian, mul_assoc (2 * infCos α hα * infCos β hβ)]
  rw [mul_eq_zero, or_iff_right (cosine_factor_isUnit α β hα hβ).ne_zero]
  rw [← hd, ← mul_pow, sq_eq_zero_iff]

end
end Surreal.Surcomplex.CoupledAngular
