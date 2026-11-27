import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalRelativeTwoTerm
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianRationalInvertibleNorm

/-!
# Actual rational rescaling for the finite translation travel bound

The original natural fraction A/B produces the real Gaussian point, its
actual inverse and the actual ratio z/(A/B). Exact runtime power and
difference identities bind the rescaled coefficient recurrence. The disk
bounds are derived from original rational comparisons, including zero z.
Recovering an original point as a literal code retains its canonical guard;
no norm positivity, inverse law or desired rescaling equation is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalTravelScaling

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical positive_product represents_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_succ power_canonical bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra (relative)
open LeanProofs.IPRA.Analysis.GaussianDominantPairAlgebra (radiusPoint radiusNumerator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (A B : PTm n) : PTm n := radiusPoint A B
def inverse (A B : PTm n) : PTm n := radiusPoint B A
def ratio (A B z : PTm n) : PTm n := qmul (inverse A B) z
def scaled (A B e c : PTm n) : PTm n := qmul (power (radius A B) e) c

ipra_subst radius
ipra_subst inverse
ipra_subst ratio
ipra_subst scaled

theorem diagonal_point (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] radiusPoint A A ≐ qone := by
  apply GaussianRationalHorner.canonical_unique _ _ _ A
    (GaussianRationalHorner.ofGaussian_canonical _ _ hA)
    GaussianRationalSyntheticDivision.qone_canonical hA
    (hrv := GaussianRationalReciprocal.qone_represents_scaled A)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := GaussianDominantPairAlgebra.radius_represents A A hA)
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [radiusNumerator,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat,Q.mk_zero,map_zero]
    ring

theorem inverse_radius (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (inverse A B) (radius A B) ≐ qone :=
  (GaussianDominantPairAlgebra.radius_multiply B A A B hA hB).eqTrans
    ((GaussianDominantPairAlgebra.radius_congr (mul_comm B A) (.eqRefl _)).eqTrans
      (diagonal_point (A*B) (positive_product A B hA hB)))

theorem inverse_next_power (A B e : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (inverse A B) (power (radius A B) (succ e)) ≐ power (radius A B) e :=
  (qmul_congr (.eqRefl _) (power_succ (radius A B) e)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
        ((qmul_congr (inverse_radius A B hA hB) (.eqRefl _)).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
            (GaussianReciprocalHorner.qmul_one_right _ (power_canonical _ _))))))

theorem ratio_scaled_succ (A B z e c : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (ratio A B z) (scaled A B (succ e) c) ≐ qmul (power (radius A B) e) (qmul z c) :=
  (GaussianRationalPowerAlgebra.qmul_shuffle _ _ _ _).eqTrans
    (qmul_congr (inverse_next_power A B e hA hB) (.eqRefl _))

theorem scaled_difference (A B z e a b : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    scaled A B e (qsub a (qmul z b)) ≐ qsub (scaled A B e a) (qmul (ratio A B z) (scaled A B (succ e) b)) :=
  (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm.eqTrans
    (qsub_congr (.eqRefl _) (ratio_scaled_succ A B z e b hA hB).eqSymm)

theorem inverse_unit (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    bounded (inverse A B) one one := by
  have hA := le_trans hB hBA
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hA (le_refl one)
    (GaussianDominantPairAlgebra.radius_represents B A hA)
  exact le_congr (by ipra_ring) (by ipra_ring)
    (le_congr (GaussianDominantPairAlgebra.radius_numerator_norm B).eqSymm (.eqRefl _) (sq_le_sq hBA))

theorem ratio_unit (A B z : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A)
    (hz : Γ ⊢[PRAAx] bounded z A B) : Γ ⊢[PRAAx] bounded (ratio A B z) one one := by
  have hA := le_trans hB hBA
  have hAB := positive_product A B hA hB
  have product := GaussianRationalReciprocal.bounded_product (inverse A B) z B A A B hA hB
    (GaussianDominantPairAlgebra.radius_bounded B A hA) hz
  have raw := GaussianRationalMetric.bounded_to_cleared _ _ _ _ _ (GaussianRationalL1.raw_den_positive _)
    hAB (GaussianRationalL1.raw_represents _) (bound_congr (.eqRefl _) (mul_comm B A) (.eqRefl _) product)
  have small : Γ ⊢[PRAAx] le (ComplexLogarithmRemainder.normSq (GaussianRationalL1.rawGaussian (ratio A B z)))
      (GaussianRationalL1.rawDen (ratio A B z)*GaussianRationalL1.rawDen (ratio A B z)) :=
    RationalValueBounds.positive_cancel (positive_product _ _ hAB hAB) raw
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (GaussianRationalL1.raw_den_positive _)
    (le_refl one) (GaussianRationalL1.raw_represents _) (le_congr (by ipra_ring) (by ipra_ring) small)

theorem inverse_power_unit (A B e : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx] bounded (power (inverse A B) e) one one :=
  bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power e) (GaussianPolynomialPerturbation.one_power e)
    (GaussianRationalReciprocal.bounded_power _ one one e (le_refl one) (inverse_unit A B hB hBA))

theorem inverse_powers (A B e : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (power (inverse A B) e) (power (radius A B) e) ≐ qone :=
  (GaussianRationalPowerAlgebra.power_product (inverse A B) (radius A B) e).eqSymm.eqTrans
    ((congrAp2 powerF (.eqRefl e) (inverse_radius A B hA hB)).eqTrans
      (GaussianRationalRoundedPower.qone_power e))

theorem unscale_relative (A B e c : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hBA : Γ ⊢[PRAAx] le B A) (hc : Γ ⊢[PRAAx] canonical c) : Γ ⊢[PRAAx]
    relative c one one (scaled A B e c) := by
  have unit := inverse_power_unit A B e hB hBA
  have roundtrip := GaussianRationalInvertibleNorm.qmul_roundtrip _ _ c (inverse_powers A B e (le_trans hB hBA) hB) hc
  have contracted := GaussianRationalRelativeTwoTerm.unit_product_left _ _ one one (scaled A B e c) unit
    (GaussianRationalRelativeNormAlgebra.relative_refl (scaled A B e c) one)
  exact GaussianRationalRelativeNormAlgebra.relative_congr roundtrip (.eqRefl _) (.eqRefl _) (.eqRefl _) contracted

theorem scaled_point_congr (A B e : PTm n) {c d : PTm n} (h : Γ ⊢[PRAAx] c ≐ d) : Γ ⊢[PRAAx]
    scaled A B e c ≐ scaled A B e d := qmul_congr (.eqRefl _) h
theorem scaled_index_congr (A B c : PTm n) {e f : PTm n} (h : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx]
    scaled A B e c ≐ scaled A B f c := qmul_congr (congrAp2 powerF h (.eqRefl _)) (.eqRefl _)
theorem scaled_zero (A B c : PTm n) (hc : Γ ⊢[PRAAx] canonical c) : Γ ⊢[PRAAx] scaled A B zero c ≐ c :=
  (qmul_congr (GaussianRationalReciprocal.power_zero _) (.eqRefl _)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right c hc))

def ratioF : PR 3 := PTm.toPR (ratio (var 0) (var 1) (var 2))
def scaledF : PR 4 := PTm.toPR (scaled (var 0) (var 1) (var 2) (var 3))
theorem ratio_program (A B z : PTm n) : Γ ⊢[PRAAx] ap3 ratioF A B z ≐ ratio A B z := by
  simpa [ratioF,ap3] using toPR_eq (Γ := Γ) (ratio (var 0) (var 1) (var 2) : PTm 3) ![A,B,z]
theorem scaled_program (A B e c : PTm n) : Γ ⊢[PRAAx] PTm.app scaledF ![A,B,e,c] ≐ scaled A B e c := by
  simpa [scaledF] using toPR_eq (Γ := Γ) (scaled (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,B,e,c]

theorem actual_radius_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ le one (var 1) ⟶ qmul (inverse (var 0) (var 1)) (radius (var 0) (var 1)) ≐ qone) :=
  closeUniv 2 (.impI (.impI (inverse_radius _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_scaled_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 0) ⟶ le one (var 1) ⟶
      scaled (var 0) (var 1) (var 3) (qsub (var 4) (qmul (var 2) (var 5))) ≐
        qsub (scaled (var 0) (var 1) (var 3) (var 4))
          (qmul (ratio (var 0) (var 1) (var 2)) (scaled (var 0) (var 1) (succ (var 3)) (var 5)))) :=
  closeUniv 6 (.impI (.impI (scaled_difference _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_scaled_ratio_unit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶ bounded (var 2) (var 0) (var 1) ⟶
      bounded (ratio (var 0) (var 1) (var 2)) one one) :=
  closeUniv 3 (.impI (.impI (.impI (ratio_unit _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_relative_unscale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶ canonical (var 3) ⟶
      relative (var 3) one one (scaled (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (unscale_relative _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_travel_scaling_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((ap3 ratioF (var 0) (var 1) (var 2) ≐ ratio (var 0) (var 1) (var 2)) ⋏
      PTm.app scaledF ![var 0,var 1,var 3,var 4] ≐ scaled (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.andI (ratio_program _ _ _) (scaled_program _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalTravelScaling
