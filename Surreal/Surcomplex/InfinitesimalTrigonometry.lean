import Surreal.Algebra.ComplexArcsinSeries
import Surreal.Surcomplex.InfinitesimalSquare
import Surreal.Surcomplex.PowerSeriesHom
import Surreal.Surcomplex.StrongConjugation
import Surreal.Surcomplex.AnalyticTaylor

/-!
# Trigonometric inverse germs on actual complex infinitesimals

The zero-centered sine, cosine and inverse-sine series are evaluated as
actual strong sums. Their formal substitution identities make sine a
bijection of the infinitesimal monad. These are the analytic prerequisites
for the cosine fold in `trigonometry:thm:fold` and `trigonometry:eq:foldroots`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- The zero-centered complex sine germ on the infinitesimal monad. -/
def infSin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) : Surcomplex.{u} :=
  powerSeriesEvaluation z hz Analytic.complexSinSeries

/-- The zero-centered complex cosine germ on the infinitesimal monad. -/
def infCos (z : Surcomplex.{u}) (hz : IsInfinitesimal z) : Surcomplex.{u} :=
  powerSeriesEvaluation z hz Analytic.complexCosSeries

/-- The zero-centered formal inverse-sine germ on the infinitesimal monad. -/
def infArcsin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) : Surcomplex.{u} :=
  powerSeriesEvaluation z hz Analytic.complexArcsinSeries

/-- This sine is the established Taylor lift of ordinary complex sine. -/
theorem infSin_eq_analyticTaylorEvaluation (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infSin z hz = analyticTaylorEvaluation Complex.sin 0 Complex.analyticAt_sin z hz := rfl

/-- This cosine is the established Taylor lift of ordinary complex cosine. -/
theorem infCos_eq_analyticTaylorEvaluation (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infCos z hz = analyticTaylorEvaluation Complex.cos 0 Complex.analyticAt_cos z hz := rfl

theorem infinitesimal_infSin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    IsInfinitesimal (infSin z hz) :=
  (isInfinitesimal_powerSeriesEvaluation_iff z hz _).mpr
    Analytic.constantCoeff_complexSinSeries

theorem infinitesimal_infArcsin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    IsInfinitesimal (infArcsin z hz) :=
  (isInfinitesimal_powerSeriesEvaluation_iff z hz _).mpr
    Analytic.constantCoeff_complexArcsinSeries

@[simp] theorem standardPart_infCos (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    standardPart (infCos z hz) = 1 := by
  simp [infCos]

theorem infCos_ne_zero (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infCos z hz ≠ 0 := by
  intro h
  have hs := standardPart_infCos z hz
  have hr := congrArg Complex.re hs
  simp [h, standardPart] at hr

@[simp] theorem infSin_zero :
    infSin (0 : Surcomplex.{u})
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩ = 0 := by
  simp [infSin]

@[simp] theorem infCos_zero :
    infCos (0 : Surcomplex.{u})
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩ = 1 := by
  simp [infCos]

@[simp] theorem infArcsin_zero :
    infArcsin (0 : Surcomplex.{u})
      ⟨SignSequence.infinitesimal_zero, SignSequence.infinitesimal_zero⟩ = 0 := by
  simp [infArcsin]

/-- Sine cancels the zero-centered inverse germ on every complex infinitesimal. -/
@[simp] theorem infSin_infArcsin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infSin (infArcsin z hz) (infinitesimal_infArcsin z hz) = z := by
  have h := powerSeriesEvaluation_subst z hz Analytic.complexSinSeries
    Analytic.complexArcsinSeries Analytic.constantCoeff_complexArcsinSeries
  rw [Analytic.complexSinSeries_subst_arcsin, powerSeriesEvaluation_X] at h
  exact h.symm

/-- The inverse germ cancels sine on the complete infinitesimal monad. -/
@[simp] theorem infArcsin_infSin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infArcsin (infSin z hz) (infinitesimal_infSin z hz) = z := by
  have h := powerSeriesEvaluation_subst z hz Analytic.complexArcsinSeries
    Analytic.complexSinSeries Analytic.constantCoeff_complexSinSeries
  rw [Analytic.complexArcsinSeries_subst_sin, powerSeriesEvaluation_X] at h
  exact h.symm

theorem infSin_injective {z w : Surcomplex.{u}} (hz : IsInfinitesimal z)
    (hw : IsInfinitesimal w) (h : infSin z hz = infSin w hw) : z = w := by
  calc
    z = infArcsin (infSin z hz) (infinitesimal_infSin z hz) := (infArcsin_infSin z hz).symm
    _ = infArcsin (infSin w hw) (infinitesimal_infSin w hw) := by congr 1
    _ = w := infArcsin_infSin w hw

theorem infArcsin_injective {z w : Surcomplex.{u}} (hz : IsInfinitesimal z)
    (hw : IsInfinitesimal w) (h : infArcsin z hz = infArcsin w hw) : z = w := by
  calc
    z = infSin (infArcsin z hz) (infinitesimal_infArcsin z hz) := (infSin_infArcsin z hz).symm
    _ = infSin (infArcsin w hw) (infinitesimal_infArcsin w hw) := by congr 1
    _ = w := infSin_infArcsin w hw

/-- The sine germ is an equivalence of the actual infinitesimal monad. -/
def infinitesimalSinEquiv : {z : Surcomplex.{u} // IsInfinitesimal z} ≃
    {z : Surcomplex.{u} // IsInfinitesimal z} where
  toFun z := ⟨infSin z z.2, infinitesimal_infSin z z.2⟩
  invFun z := ⟨infArcsin z z.2, infinitesimal_infArcsin z z.2⟩
  left_inv z := Subtype.ext (infArcsin_infSin z z.2)
  right_inv z := Subtype.ext (infSin_infArcsin z z.2)

/-- Formal evaluation of a linearly rescaled argument. -/
theorem powerSeriesEvaluation_subst_const_mul_X (z : Surcomplex.{u})
    (hz : IsInfinitesimal z) (r : ℂ) (f : PowerSeries ℂ)
    (hrz : IsInfinitesimal (ofComplex r * z)) :
    powerSeriesEvaluation z hz (f.subst (PowerSeries.C r * PowerSeries.X)) =
      powerSeriesEvaluation (ofComplex r * z) hrz f := by
  have h := powerSeriesEvaluation_subst z hz f (PowerSeries.C r * PowerSeries.X) (by simp)
  have he : powerSeriesEvaluation z hz (PowerSeries.C r * PowerSeries.X) = ofComplex r * z := by
    rw [map_mul, powerSeriesEvaluation_C, powerSeriesEvaluation_X]
  exact h.trans (by congr 2)

/-- The double-angle cosine identity is exact on the actual infinitesimal monad. -/
theorem infCos_two_mul (z : Surcomplex.{u}) (hz : IsInfinitesimal z)
    (h2z : IsInfinitesimal (2 * z)) :
    infCos (2 * z) h2z = 1 - 2 * infSin z hz ^ 2 := by
  have h := congrArg (powerSeriesEvaluation z hz) Analytic.complexCosSeries_subst_two_mul_X
  rw [powerSeriesEvaluation_subst_const_mul_X z hz 2 _ (by simpa only [map_ofNat] using h2z)] at h
  simpa only [map_sub, map_one, map_mul, map_ofNat, map_pow, infCos, infSin] using h

/-- The double-angle sine identity is exact on the actual infinitesimal monad. -/
theorem infSin_two_mul (z : Surcomplex.{u}) (hz : IsInfinitesimal z)
    (h2z : IsInfinitesimal (2 * z)) :
    infSin (2 * z) h2z = 2 * infSin z hz * infCos z hz := by
  have h := congrArg (powerSeriesEvaluation z hz) Analytic.complexSinSeries_subst_two_mul_X
  rw [powerSeriesEvaluation_subst_const_mul_X z hz 2 _ (by simpa only [map_ofNat] using h2z)] at h
  simpa only [map_mul, map_ofNat, infCos, infSin] using h

theorem infSin_sq_add_cos_sq (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infSin z hz ^ 2 + infCos z hz ^ 2 = 1 := by
  have h := congrArg (powerSeriesEvaluation z hz) Analytic.complexSinSeries_sq_add_cos_sq
  simpa only [map_add, map_pow, map_one, infSin, infCos] using h

/-- The inverse-sine germ is odd on its full infinitesimal domain. -/
theorem infArcsin_neg (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infArcsin (-z) (infinitesimal_neg hz) = -infArcsin z hz := by
  have h := powerSeriesEvaluation_subst z hz Analytic.complexArcsinSeries
    (-PowerSeries.X) (by simp)
  rw [Analytic.complexArcsinSeries_subst_neg_X] at h
  simpa only [map_neg, powerSeriesEvaluation_X, infArcsin] using h.symm

/-- The sine germ is odd. -/
theorem infSin_neg (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infSin (-z) (infinitesimal_neg hz) = -infSin z hz := by
  have h := powerSeriesEvaluation_subst z hz Analytic.complexSinSeries
    (-PowerSeries.X) (by simp)
  rw [Analytic.complexSinSeries_subst_neg_X] at h
  simpa only [map_neg, powerSeriesEvaluation_X, infSin] using h.symm

/-- The cosine germ is even. -/
theorem infCos_neg (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infCos (-z) (infinitesimal_neg hz) = infCos z hz := by
  have h := powerSeriesEvaluation_subst z hz Analytic.complexCosSeries
    (-PowerSeries.X) (by simp)
  rw [Analytic.complexCosSeries_subst_neg_X] at h
  simpa only [map_neg, powerSeriesEvaluation_X, infCos] using h.symm

/-- Real coefficients make the inverse germ commute with conjugation. -/
theorem infArcsin_conj (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    infArcsin (conj z) (infinitesimal_conj hz) = conj (infArcsin z hz) := by
  have h := powerSeriesEvaluation_conj z hz Analytic.complexArcsinSeries
  rw [Analytic.map_conj_complexArcsinSeries] at h
  exact h

/-- The inverse germ preserves the real axis. -/
theorem infArcsin_im_eq_zero (z : Surcomplex.{u}) (hz : IsInfinitesimal z)
    (hr : z.im = 0) : (infArcsin z hz).im = 0 := by
  apply (conj_eq_self_iff_im_eq_zero _).mp
  rw [← infArcsin_conj]
  congr 1
  exact (conj_eq_self_iff_im_eq_zero z).mpr hr

/-- Oddness and real coefficients preserve the purely imaginary axis. -/
theorem infArcsin_re_eq_zero (z : Surcomplex.{u}) (hz : IsInfinitesimal z)
    (hi : z.re = 0) : (infArcsin z hz).re = 0 := by
  apply (conj_eq_neg_iff_re_eq_zero _).mp
  calc
    conj (infArcsin z hz) = infArcsin (conj z) (infinitesimal_conj hz) :=
      (infArcsin_conj z hz).symm
    _ = infArcsin (-z) (infinitesimal_neg hz) := by
      congr 1
      exact (conj_eq_neg_iff_re_eq_zero z).mpr hi
    _ = -infArcsin z hz := infArcsin_neg z hz

/-- The nonzero linear term preserves the exact valuation, including at zero. -/
theorem valuation_infArcsin (z : Surcomplex.{u}) (hz : IsInfinitesimal z) :
    valuation (infArcsin z hz) = valuation z := by
  simpa only [infArcsin, Analytic.order_complexArcsinSeries, ENat.toNat_one, one_nsmul] using
    valuation_powerSeriesEvaluation z hz _ Analytic.complexArcsinSeries_ne_zero

end
end Surreal.Surcomplex
