import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelCompactPositiveRadius
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalUpperAddition
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals

/-!
# Exact signed coordinates of two projected-radius corrections

No sign or canonicality is assumed for either original observation.
Their real projections retain the original signed values. Each radius
adds exactly its two requested dyadics; adding two diagonal corrections
therefore costs exactly four dyadics at the unchanged original query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRadiusCorrectionSum

open_ipra
open GaussianEulerUnitKernelCompactPositiveRadius (positiveRadius)
open GaussianGammaRealValues (projection projection_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_represents)
open GaussianRationalHorner (qadd positive_product scalar_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper)
open ComplexLogarithmRemainder (re)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (p q v : PTm n) : PTm n := positiveRadius v (unit p) (unit q)
ipra_subst radius

theorem projection_scalar_representation (v : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (projection v)) (re (rawGaussian v)) (rawDen v) :=
  scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _)
    (projection_represents v (rawGaussian v) (rawDen v) (raw_represents v)).andE₁

theorem correction_upper (v P Q : PTm n) (hP : Γ ⊢[PRAAx] le one P) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    upper (fstT (positiveRadius v P Q)) (fstT v) (P+Q) (P*Q) := by
  have hPQ := positive_product _ _ hP hQ
  have extra : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (radiusPoint (P+Q) (P*Q))) (ZT.ofNat (P+Q)) (P*Q) :=
    scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianDominantPairAlgebra.radiusNumerator,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _)
      (radius_represents (P+Q) (P*Q) hPQ).andE₁
  have actual := RationalRepresentations.represents_add _ _ _ _ _ _ (projection_scalar_representation (Γ := Γ) v) extra
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _
    (positive_product _ _ (raw_den_positive v) hPQ) (raw_den_positive v)
    (scalar_congr (RationalGaussianRealPart.real_add _ _).eqSymm (.eqRefl _) (.eqRefl _) actual) (raw_represents v).andE₁
  apply zle_of_toZ zero
  simp only [ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem diagonal_correction_upper (v u : PTm n) : Γ ⊢[PRAAx]
    upper (fstT (radius u u v)) (fstT v) two (unit u) :=
  RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive u) (unit_positive u))
    (correction_upper v (unit u) (unit u) (unit_positive u) (unit_positive u))
    (le_of_eq_add (d := zero) (by ipra_ring))

theorem sum_correction_upper (v w u : PTm n) : Γ ⊢[PRAAx]
    upper (fstT (qadd (radius u u v) (radius u u w))) (fstT (qadd v w)) (num 4) (unit u) := by
  have added := RationalUpperAddition.add_upper (Γ := Γ) _ _ _ _ two (unit u) two (unit u)
    (diagonal_correction_upper v u) (diagonal_correction_upper w u)
  have cleared : Γ ⊢[PRAAx] upper (fstT (qadd (radius u u v) (radius u u w))) (fstT (qadd v w))
      (unit u*num 4) (unit u*unit u) :=
    RationalValueBounds.upper_congr (RationalGaussianRealPart.real_add _ _).eqSymm (RationalGaussianRealPart.real_add _ _).eqSymm
      (by ipra_ring) (.eqRefl _) added
  exact RationalValueBounds.upper_cancel _ _ (num 4) (unit u) (unit u) (unit_positive u) cleared

theorem actual_raw_two_radius_correction_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (upper (fstT (qadd (radius (var 2) (var 2) (var 0)) (radius (var 2) (var 2) (var 1))))
      (fstT (qadd (var 0) (var 1))) (num 4) (unit (var 2))) :=
  closeUniv 3 (sum_correction_upper _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalRadiusCorrectionSum
