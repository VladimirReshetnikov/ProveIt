import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrationByPartsProductStep

/-!
# Genuine original finite integration-by-parts cell estimate

Multiplying the original power-times-decay observations by rational
time gives the boundary values. Its actual first-order term is the
checked Euler integration-by-parts cell. The uniform residual consists
of a quadratic mesh term and an explicit original sampling allowance.
This finite estimate does not assume an integral or derivative law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrationByPartsLinear (decay originalProduct primitive productLinear linear cell original_linear_is_cell)
open GaussianEulerIntegrationByPartsProductStep (source powerCurvature linearBound observationCost denominator denominator_positive)
open GaussianEulerPowerIncrement (point slopeTerm)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianRationalFirstOrderProductError (error productError decomposedError linearPart)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qadd qmul_canonical positive_product canonical)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr qmul_zero_right)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productSlopeBound (R E T : PTm n) : PTm n := num 3*linearBound R E T+num 3*majorant R E T
def curvature (R E T : PTm n) : PTm n := T*GaussianEulerIntegrationByPartsProductStep.curvature R E T+productSlopeBound R E T
def numerator (p R E T b c : PTm n) : PTm n := curvature R E T*c*c*unit p+T*observationCost R E T*(b*b)

theorem time_add (a b c : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qadd (fraction a b) (fraction c b) ≐ fraction (a+c) b := by
  have left : Γ ⊢[PRAAx] qadd (fraction a b) (fraction c b) ≐
      qadd (GaussianBetaPrimitiveLinearStep.argument a b one) (GaussianBetaPrimitiveLinearStep.step c b one) :=
    qadd_congr (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring))
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring))
  exact left.eqTrans ((GaussianBetaPrimitiveLinearStep.argument_step a b c one hb (le_refl one)).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)))

private theorem time_error_decomposition (X1 X0 L U1 U H : PTm n)
    (hd : Γ ⊢[PRAAx] qsub U1 U ≐ H) : Γ ⊢[PRAAx]
    productError X1 X0 U1 U L H ≐ qadd (qmul (error X1 X0 L) U1) (qmul L H) := by
  have zero : Γ ⊢[PRAAx] error U1 U H ≐ GaussianRationalHorner.qzero :=
    (qsub_congr hd (.eqRefl H)).eqTrans (GaussianCoefficientNormOrder.qsub_self H)
  have second := (qmul_congr (.eqRefl X0) zero).eqTrans (qmul_zero_right X0)
  have clear : Γ ⊢[PRAAx] qadd (qmul (error X1 X0 L) U1) (qmul X0 (error U1 U H)) ≐ qmul (error X1 X0 L) U1 :=
    (qadd_congr (.eqRefl _) second).eqTrans
    (GaussianReciprocalHorner.qadd_zero_right _ (qmul_canonical _ _))
  exact (GaussianRationalFirstOrderProductError.product_error_identity X1 X0 U1 U L H).eqTrans
    (qadd_congr clear (qmul_congr (.eqRefl L) hd))

theorem original_product_linear_bound (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    bounded (productLinear p z B a b c) (productSlopeBound R E T*c) b := by
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have ha := h.andE₁.andE₂.andE₁.andE₁.andE₁
  have raw1 := bounded_product _ _ _ _ _ _ hb (le_refl one)
    (GaussianEulerIntegrationByPartsProductStep.original_power_linear_bound p z R B E T a b c h)
    (GaussianEulerDecayIncrement.decay_observation_uniform_bound a b p ha hb)
  have first : Γ ⊢[PRAAx] bounded (qmul (slopeTerm p z B a b c) (decay p a b)) (num 3*linearBound R E T*c) b :=
    bound_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (by ipra_ring) raw1
  have raw2 := bounded_product _ _ _ _ _ _ (le_refl one) hb
    (GaussianEulerCompactPowerMajorant.original_power_observation p z R B E T a b h.andE₁.andE₁ h.andE₁.andE₂.andE₁)
    (GaussianEulerIntegrationByPartsProductStep.decay_linear_bound p a b c ha hb)
  have second : Γ ⊢[PRAAx] bounded (qmul (point p z B a b) (GaussianEulerIntegrationByPartsLinear.decayLinear p a b c))
      (num 3*majorant R E T*c) b := bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) raw2
  exact bound_congr (.eqRefl _) (by unfold productSlopeBound; ipra_ring) (.eqRefl _)
    (bounded_sum_same _ _ _ _ b hb first second)

/-- Actual original observations at the two endpoints. Every local
estimate is discharged from the native compact source. -/
theorem original_cell_error (p z R B E T a b c : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E T a b c) : Γ ⊢[PRAAx]
    distanceBounded (qsub (primitive p z B (a+c) b) (primitive p z B a b)) (cell p z B a b c)
      (numerator p R E T b c) (denominator p b) := by
  let X1 := originalProduct p z B (a+c) b
  let X0 := originalProduct p z B a b
  let L := productLinear p z B a b c
  let U1 := fraction (a+c) b
  let U := fraction a b
  let H := fraction c b
  let D := denominator p b
  have hb := h.andE₁.andE₂.andE₁.andE₁.andE₂
  have ha := h.andE₁.andE₂.andE₁.andE₁.andE₁
  have hB := h.andE₁.andE₁.andE₁
  have hD := denominator_positive p b hb
  have hbb := positive_product b b hb hb
  have hH : Γ ⊢[PRAAx] canonical H := GaussianRationalHorner.ofGaussian_canonical _ _ hb
  have hd : Γ ⊢[PRAAx] qsub U1 U ≐ H :=
    (qsub_congr (time_add a b c hb).eqSymm (.eqRefl U)).eqTrans (GaussianRationalSyntheticDivision.qadd_sub_cancel U H hH)
  have later := GaussianEulerExponentCompactBounds.fraction_bound (a+c) b T hb h.andE₁.andE₂.andE₂.andE₁.andE₂.andE₂
  have err := GaussianEulerIntegrationByPartsProductStep.original_product_increment p z R B E T a b c h
  have one := bounded_product (error X1 X0 L) U1 (GaussianEulerIntegrationByPartsProductStep.numerator p R E T b c) D T one hD (le_refl one) err later
  have first : Γ ⊢[PRAAx] bounded (qmul (error X1 X0 L) U1)
      (T*GaussianEulerIntegrationByPartsProductStep.numerator p R E T b c) D :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) one
  have timeBound := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point c b hb).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded c b hb)
  have raw := bounded_product L H (productSlopeBound R E T*c) b c b hb hb (original_product_linear_bound p z R B E T a b c h) timeBound
  have second : Γ ⊢[PRAAx] bounded (qmul L H) (productSlopeBound R E T*c*c*unit p) D :=
    bounded_radius_mono _ _ _ _ _ hbb hD (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring)) raw
  have sum := bounded_sum_same _ _ _ _ D hD first second
  have original : Γ ⊢[PRAAx] bounded (productError X1 X0 U1 U L H) (numerator p R E T b c) D :=
    bound_congr (time_error_decomposition X1 X0 L U1 U H hd).eqSymm
      (by unfold numerator curvature GaussianEulerIntegrationByPartsProductStep.numerator; ipra_ring) (.eqRefl _) sum
  have linearEq : Γ ⊢[PRAAx] cell p z B a b c ≐ linearPart X0 U L H :=
    (original_linear_is_cell p z B a b c hB ha hb).eqSymm.eqTrans
      ((GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans
        (qadd_congr (GaussianRationalPowerAlgebra.qmul_commutative U L) (.eqRefl _)))
  have equality : Γ ⊢[PRAAx] qsub (qsub (primitive p z B (a+c) b) (primitive p z B a b)) (cell p z B a b c) ≐ productError X1 X0 U1 U L H :=
    qsub_congr (qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative U1 X1) (GaussianRationalPowerAlgebra.qmul_commutative U X0)) linearEq
  exact bound_congr equality.eqSymm (.eqRefl _) (.eqRefl _) original

theorem original_Euler_integration_by_parts_cell_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (qsub (primitive (var 0) (var 1) (var 3) (var 6+var 8) (var 7))
        (primitive (var 0) (var 1) (var 3) (var 6) (var 7)))
        (cell (var 0) (var 1) (var 3) (var 6) (var 7) (var 8))
        (numerator (var 0) (var 2) (var 4) (var 5) (var 7) (var 8)) (denominator (var 0) (var 7))) :=
  closeUniv 9 (.impI (original_cell_error _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsStep
