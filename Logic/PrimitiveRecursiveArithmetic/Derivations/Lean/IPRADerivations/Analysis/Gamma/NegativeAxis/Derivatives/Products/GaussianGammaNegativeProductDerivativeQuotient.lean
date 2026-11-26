import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivativeRate
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumSignedStep

/-!
# Literal quotient and first-order remainder of the Gamma shift product

The exact difference identity licenses the actual reciprocal of the
input step once a rational separation is supplied. The derivative is
the original rising product times the signed reciprocal correction.
The remainder estimate also covers coincident endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeQuotient

open_ipra
open ComplexLogarithmRemainder (normSq)
open GaussianGammaLocalPoleGuards (center)
open GaussianGammaMinimumSignedStep (increment separated_norm)
open GaussianGammaNegativeCriticalCorrection (correction guard)
open GaussianGammaNegativeProductDerivative (dividedDifference firstCoefficient original_product_gap)
open GaussianGammaNegativeProductDerivativeCorrection (original_first_coefficient)
open GaussianGammaNegativeProductDerivativeRate (derivativeCost derivative_error)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian_represents positive_product qadd_canonical qmul represents_congr)
open GaussianRationalMetric (distanceBounded qnegative qsub qsub_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (normNumerator reciprocal reciprocal_identity bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianStirlingGammaLogarithm (arg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shiftProduct (a b N : PTm n) : PTm n := risingProduct (center (arg a) b (succ N)) b (succ (succ N))

def step (a c b : PTm n) : PTm n := qsub (fraction c b) (fraction a b)

def literalQuotient (a c b N : PTm n) : PTm n := qmul (reciprocal (step a c b)) (qsub (shiftProduct c b N) (shiftProduct a b N))

ipra_subst shiftProduct
ipra_subst step
ipra_subst literalQuotient

theorem separated_step (a c b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hs : Γ ⊢[PRAAx] lt a c ⋎ lt c a) : Γ ⊢[PRAAx] le one (normNumerator (step a c b)) := by
  let u := increment a c
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRootAlgebra.sub (arg c) (arg a)) u := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [arg,u,increment,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
        ComplexLogarithmRemainder.eval_re_code]
      simp only [ZT.toZ]
      ring
    · simp only [arg,u,increment,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
      ipra_simps
      ring
  have source := qsub_represents (fraction c b) (fraction a b) (arg c) (arg a) b hb
    (ofGaussian_represents (arg c) b hb) (ofGaussian_represents (arg a) b hb)
  have rep := represents_congr (.eqRefl (step a c b)) eq (.eqRefl b) source
  have lower := GaussianRationalLowerBounds.lower_from_representation (step a c b) u b one b hb hb rep
    (le_congr (by ipra_ring) (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono
      (le_refl (b*b)) (separated_norm a c hs)))
  exact GaussianNameReciprocal.lower_norm_positive (step a c b) b hb lower

theorem literal_quotient_at (a c b N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hs : Γ ⊢[PRAAx] lt a c ⋎ lt c a) :
    Γ ⊢[PRAAx] literalQuotient a c b N ≐ dividedDifference (arg a) (arg c) b (succ N) := by
  let x := dividedDifference (arg a) (arg c) b (succ N)
  let u := step a c b
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x := qadd_canonical _ _
  have i : Γ ⊢[PRAAx] qmul (reciprocal u) u ≐ qone :=
    (qmul_commutative _ _).eqTrans (reciprocal_identity u (separated_step a c b hb hs))
  exact (qmul_congr (.eqRefl _) (original_product_gap (arg a) (arg c) b (succ N) hb)).eqTrans
    ((qmul_associative (reciprocal u) u x).eqSymm.eqTrans
      ((qmul_congr i (.eqRefl x)).eqTrans ((qmul_commutative _ _).eqTrans (qmul_one_right _ hc))))

theorem literal_quotient_rate (a c b N A D : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hs : Γ ⊢[PRAAx] lt a c ⋎ lt c a) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) :
    Γ ⊢[PRAAx] distanceBounded (literalQuotient a c b N) (qmul (shiftProduct a b N) (qnegative (correction a b N)))
      (derivativeCost (succ N)*A) D :=
  distance_congr (literal_quotient_at a c b N (le_trans ha.andE₁ (le_of_lt ha.andE₂)) hs).eqSymm
    (original_first_coefficient a b N ha) (.eqRefl _) (.eqRefl _)
    (derivative_error a c b (succ N) A D ha hc hD hStep)

theorem original_product_remainder (a c b N A D : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) :
    Γ ⊢[PRAAx] distanceBounded (qsub (shiftProduct c b N) (shiftProduct a b N))
      (qmul (step a c b) (qmul (shiftProduct a b N) (qnegative (correction a b N))))
      (derivativeCost (succ N)*A*A) (D*D) := by
  let u := step a c b
  let v := dividedDifference (arg a) (arg c) b (succ N)
  let w := firstCoefficient (arg a) b (succ N)
  have gap : Γ ⊢[PRAAx] distanceBounded v w (derivativeCost (succ N)*A) D :=
    derivative_error a c b (succ N) A D ha hc hD hStep
  have near : Γ ⊢[PRAAx] distanceBounded (qmul u v) (qmul u w) (A*(derivativeCost (succ N)*A)) (D*D) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference u v w).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_product u (qsub v w) A D _ D hD hD hStep gap)
  exact distance_congr (original_product_gap (arg a) (arg c) b (succ N) (le_trans ha.andE₁ (le_of_lt ha.andE₂))).eqSymm
    (qmul_congr (.eqRefl _) (original_first_coefficient a b N ha)) (by ipra_ring) (.eqRefl _) near

theorem actual_negative_Gamma_shift_product_quotient_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 0) (var 2) ⋏ (guard (var 1) (var 2) ⋏ (lt (var 0) (var 1) ⋎ lt (var 1) (var 0)))) ⟶
        le one (var 5) ⟶ distanceBounded (fraction (var 1) (var 2)) (fraction (var 0) (var 2)) (var 4) (var 5) ⟶
        distanceBounded (literalQuotient (var 0) (var 1) (var 2) (var 3))
          (qmul (shiftProduct (var 0) (var 2) (var 3)) (qnegative (correction (var 0) (var 2) (var 3))))
          (derivativeCost (succ (var 3))*var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (literal_quotient_rate _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeQuotient
