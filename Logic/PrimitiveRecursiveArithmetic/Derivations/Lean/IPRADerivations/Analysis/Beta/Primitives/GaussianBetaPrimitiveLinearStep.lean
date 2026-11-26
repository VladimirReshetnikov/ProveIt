import IPRADerivations.Analysis.Polynomials.Taylor.GaussianTimeWeightedPolynomialIncrement
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRationalPolynomialEulerSlope
import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerIncrement
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison

/-!
# Exact linear part of the original beta primitive on a rational time grid

The polynomial argument and step are (a/(bN)) and (c/(bN)).
The original time-power increment is linear in (c/a). The product
of the time argument with that ratio is exactly the polynomial step.
The original beta operator then identifies the sum of the two linear
terms with the original beta row, at its existing replacement clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveLinearStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerBetaPolynomialPrimitive (primitive)
open GaussianEulerPowerIncrement (point slopeTerm)
open GaussianTimeWeightedPolynomialIncrement (value linear)
open GaussianBetaKernelExponential (base kernel)
open GaussianRationalHorner (qadd qmul evaluate ofGaussian ofGaussian_canonical
  ofGaussian_represents canonical_unique qadd_canonical qmul_canonical positive_product
  qadd_represents qmul_represents represents_congr represents_rescale)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalCoefficientScaling (qmul_add)
open ComplexLogarithmRemainder (oneCode scale)
open GaussianRootAlgebra (equal_of_values re_add im_add re_one im_one re_scale im_scale re_mul im_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (a b N : PTm n) : PTm n := fraction a (b*N)
def step (c b N : PTm n) : PTm n := fraction c (b*N)
def sample (p z B a b N : PTm n) : PTm n :=
  qmul (point p z B a b) (value (primitive z B N) (argument a b N))
def linearSum (q z B a b c N : PTm n) : PTm n :=
  qadd (qmul (slopeTerm q z B a b c) (value (primitive z B N) (argument a b N)))
    (qmul (point q z B a b) (qmul (step c b N) (linear (primitive z B N) (argument a b N) N)))

theorem argument_step (a b c N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qadd (argument a b N) (step c b N) ≐ argument (a+c) b N := by
  let D := b*N
  have hd := positive_product b N hb hN
  have add := qadd_represents (fraction a D) (fraction c D) (scale a oneCode) (scale c oneCode) D hd
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (scale a oneCode) (scale c oneCode)) (scale (a+c) oneCode) := by
    apply equal_of_values
    all_goals simp only [re_add,im_add,re_scale,im_scale,re_one,im_one]; ipra_simps; ring
  exact canonical_unique _ _ _ D (qadd_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) eq (.eqRefl _) add) (ofGaussian_represents _ _ hd)

theorem argument_ratio_step (a b c N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (fraction c a) (argument a b N) ≐ step c b N := by
  let D := b*N
  have hd := positive_product b N hb hN
  have both := positive_product a D ha hd
  have prod := qmul_represents (fraction c a) (fraction a D) (scale c oneCode) (scale a oneCode) a D ha hd
    (ofGaussian_represents _ _ ha) (ofGaussian_represents _ _ hd)
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.mul (scale c oneCode) (scale a oneCode)) (scale a (scale c oneCode)) := by
    apply equal_of_values
    all_goals simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one]; ring
  exact canonical_unique _ _ _ (a*D) (qmul_canonical _ _) (ofGaussian_canonical _ _ hd) both
    (represents_congr (.eqRefl _) eq (.eqRefl _) prod)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (by ipra_ring)
      (represents_rescale (fraction c D) (scale c oneCode) D a (ofGaussian_represents _ _ hd)))

private theorem exchange (K F P U : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul K F) (qmul P U) ≐ qmul (qmul F U) (qmul K P) :=
  (qmul_shuffle K F P U).eqTrans (qmul_commutative _ _)

private theorem add_coefficient_one (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (GaussianEulerIntegrandName.coefficient z B) qone ≐ ofGaussian z B :=
  (GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans
    (GaussianRationalLinearProduct.add_sub_right qone _ (ofGaussian_canonical _ _ hB))

theorem original_linear_sum (q z R B A a b c N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] linearSum q z B a b c N ≐ qmul (qmul (point q z B a b) (kernel a b N)) (step c b N) := by
  let U := argument a b N
  let H := step c b N
  let F := fraction c a
  let K := GaussianEulerIntegrandName.coefficient z B
  let X := point q z B a b
  let C := primitive z B N
  let P := evaluate C U
  let S := GaussianRationalFirstOrderPolynomial.betaSlope z B N U
  let D := qmul S U
  have hB : Γ ⊢[PRAAx] le one B := hz.andE₂.andE₁.andE₁
  have hD := positive_product b N hb hN
  have unitArg : Γ ⊢[PRAAx] GaussianRationalHorner.canonical U := ofGaussian_canonical _ _ hD
  have first : Γ ⊢[PRAAx] qmul (slopeTerm q z B a b c) (value C U) ≐ qmul X (qmul H (qmul K P)) :=
    (qmul_associative X (qmul K F) (qmul P U)).eqTrans
      (qmul_congr (.eqRefl _) ((exchange K F P U).eqTrans
        (qmul_congr (argument_ratio_step a b c N ha hb hN) (.eqRefl _))))
  have poly : Γ ⊢[PRAAx] qadd (qmul K P) (linear C U N) ≐ kernel a b N := by
    change Γ ⊢[PRAAx] qadd (qmul K P) (qadd D P) ≐ kernel a b N
    have shape : Γ ⊢[PRAAx] P ≐ GaussianRationalHorner.horner C U (succ N) :=
      congrAp3 GaussianRationalHorner.hornerF (GaussianEulerBetaPolynomialPrimitive.primitive_length z B N)
        (.eqRefl _) (.eqRefl _)
    have hP : Γ ⊢[PRAAx] GaussianRationalHorner.canonical P :=
      GaussianRationalHorner.canonical_congr
        (shape.eqTrans (GaussianRationalHorner.horner_succ C U N)) (qadd_canonical _ _)
    have add : Γ ⊢[PRAAx] qadd (qmul K P) P ≐ qmul (ofGaussian z B) P :=
      (qadd_congr (.eqRefl _) ((qmul_commutative qone P).eqTrans (qmul_one_right P hP)).eqSymm).eqTrans
        ((qadd_congr (qmul_commutative K P) (qmul_commutative qone P)).eqTrans
          ((qmul_add P K qone).eqSymm.eqTrans
            ((qmul_congr (.eqRefl _) (add_coefficient_one z B hB)).eqTrans (qmul_commutative P _))))
    have slope := GaussianRationalPolynomialEulerSlope.original_beta_first_order_equation z R B A N U hz unitArg
    have baseEq : Γ ⊢[PRAAx] base a b N ≐ GaussianRationalMetric.qsub qone U :=
      qadd_congr (.eqRefl _) (GaussianBetaKernelLogarithm.target_is_original_decay a (b*N) hD)
    exact (qadd_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_commutative D P)).eqTrans
      ((qadd_associative (qmul K P) P D).eqSymm.eqTrans
        ((qadd_congr add (qmul_commutative S U)).eqTrans
          (slope.eqTrans (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl N) baseEq.eqSymm))))
  exact (qadd_congr first (.eqRefl _)).eqTrans
    ((qmul_add X (qmul H (qmul K P)) (qmul H (linear C U N))).eqSymm.eqTrans
      ((qmul_congr (.eqRefl _) ((qmul_add H (qmul K P) (linear C U N)).eqSymm.eqTrans
        (qmul_congr (.eqRefl _) poly))).eqTrans
        ((qmul_congr (.eqRefl _) (qmul_commutative H (kernel a b N))).eqTrans
          (qmul_associative X (kernel a b N) H).eqSymm)))

theorem actual_row_linear_sum (p z R B A a b c N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] linearSum (GaussianEulerCompactProductComparison.clock p z B a b) z B a b c N ≐
      qmul (GaussianBetaKernelGridComparison.row p z B a b N) (step c b N) :=
  original_linear_sum _ _ _ _ _ _ _ _ _ hz ha hb hN

theorem original_beta_row_is_literal_primitive_linear_term_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((GaussianEulerLowerPowerCoefficients.source (var 1) (var 2) (var 3) (var 4) ⋏
      le one (var 5) ⋏ le one (var 6) ⋏ le one (var 8)) ⟶
      linearSum (GaussianEulerCompactProductComparison.clock (var 0) (var 1) (var 3) (var 5) (var 6))
        (var 1) (var 3) (var 5) (var 6) (var 7) (var 8) ≐
      qmul (GaussianBetaKernelGridComparison.row (var 0) (var 1) (var 3) (var 5) (var 6) (var 8))
        (step (var 7) (var 6) (var 8))) :=
  closeUniv 9 (.impI (actual_row_linear_sum _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveLinearStep
