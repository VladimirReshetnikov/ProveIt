import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetExponentialIntegralGrid
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetWeightedResolventGrid
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceScalarMajorant
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftSecants

/-!
# The exact shifted right-half-plane charts in the Binet rectangle

At the unit tag `u=j/M` the exponent of the product of the two
original Laplace factors is the actual chart for `z+u`.
Its real margin is inherited from z, uniformly in the unit mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetReciprocalRows (tagPoint)
open GaussianBinetExponentialIntegralGrid (exponent)
open GaussianBinetExponentialPanel (sample)
open GaussianCoefficientNameBounds (unit)
open GaussianEulerIntegrandName (decayPoint decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianInverseBinomialRows (negative_congr)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRadiusExponentialName (input)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd qadd_canonical qmul qzero ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qnegative qnegative_canonical qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_add)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def realNumerator (X D M j : PTm n) : PTm n := M*(X+zero*D)+j*D

theorem shifted_source (X Y D sign R M j : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R)
    (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] source (realNumerator X D M j) (M*Y) (M*D) sign (R+one) := by
  let A := realNumerator X D M j
  let B := M*Y
  let E := M*D
  let z := argument X Y D sign
  let w := argument A B E sign
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hM h.andE₁.andE₂
  have hx := le_trans h.andE₁.andE₁.andE₁ (le_add_right X (zero*D))
  have ha : Γ ⊢[PRAAx] le one A :=
    le_trans (positive_product _ _ hM hx) (le_add_right _ _)
  have frac := GaussianEulerExponentCompactBounds.fraction_bound j M one hM (le_congr (.eqRefl _) (one_mul M).eqSymm hj)
  have bw : Γ ⊢[PRAAx] bounded w (R+one) one :=
    bound_congr (GaussianBinetWeightedResolventGrid.tag_add X Y D sign M j h.andE₁ hM).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.bounded_sum_same z (fraction j M) R one one (le_refl one)
        (GaussianBinetLaplaceExponential.parameter_bound X Y D sign R h) frac)
  have cleared := (bounded_iff w (native A B sign) E (R+one) one he (le_refl one) (ofGaussian_represents _ _ he)).iffMp bw
  have bn : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (native A B sign) ((R+one)*E) :=
    le_congr (by ipra_ring) (by ipra_ring) cleared
  exact .andI (.andI (.andI ha h.andE₁.andE₁.andE₂) he) bn

theorem shifted_margin (X D K M j : PTm n) (hm : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] le (M*D) (K*realNumerator X D M j) := by
  dsimp only [realNumerator]
  ipra_le 𝔞(M)*sl hm+𝔞(K)*𝔞(j)*𝔞(D)

private theorem neg_sum (x y : PTm n) : Γ ⊢[PRAAx]
    qadd (qnegative x) (qnegative y) ≐ qnegative (qadd x y) := by
  have zx : Γ ⊢[PRAAx] qsub qzero x ≐ qnegative x := qzero_add _ (qnegative_canonical x)
  have zy : Γ ⊢[PRAAx] qsub qzero y ≐ qnegative y := qzero_add _ (qnegative_canonical y)
  have zz : Γ ⊢[PRAAx] qsub qzero (qadd x y) ≐ qnegative (qadd x y) :=
    qzero_add _ (qnegative_canonical _)
  exact (qadd_congr zx.eqSymm zy.eqSymm).eqTrans
    ((GaussianNameArithmetic.sum_difference qzero x qzero y).eqSymm.eqTrans
      ((qsub_congr (qzero_add qzero GaussianRationalSyntheticDivision.qzero_canonical) (.eqRefl _)).eqTrans zz))

private theorem real_product (a b j M : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (qnegative (fraction j M)) (fraction a b) ≐ decayPoint (a*j) (b*M) :=
  (qmul_commutative _ _).eqTrans ((GaussianGammaDigammaTwoShiftSecants.negative_mul (fraction a b) (fraction j M)).eqSymm.eqTrans
    (negative_congr (GaussianEulerDampedTimeRate.fraction_product a b j M hb hM)))

theorem exponent_shift (X Y D sign a b M j : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hb : Γ ⊢[PRAAx] le one b) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qadd (GaussianBinetLaplaceExponential.exponent X Y D sign a b) (decayPoint (a*j) (b*M)) ≐
      GaussianBinetLaplaceExponential.exponent (realNumerator X D M j) (M*Y) (M*D) sign a b := by
  let x := argument X Y D sign
  let y := fraction j M
  let w := tagPoint X Y D sign zero M j
  let t := fraction a b
  have eq : Γ ⊢[PRAAx] qadd (qnegative x) (qnegative y) ≐ qnegative w :=
    (neg_sum x y).eqTrans (negative_congr (GaussianBinetWeightedResolventGrid.tag_add X Y D sign M j h hM).eqSymm)
  have distribute : Γ ⊢[PRAAx] qadd (qmul (qnegative x) t) (qmul (qnegative y) t) ≐ qmul (qadd (qnegative x) (qnegative y)) t :=
    (qadd_congr (qmul_commutative _ _) (qmul_commutative _ _)).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add t (qnegative x) (qnegative y)).eqSymm.eqTrans (qmul_commutative _ _))
  exact (qadd_congr (.eqRefl _) (real_product a b j M hb hM).eqSymm).eqTrans
    (distribute.eqTrans (qmul_congr eq (.eqRefl _)))

private theorem input_congr (S x y : PTm n) (e : Γ ⊢[PRAAx] x ≐ y) (h : Γ ⊢[PRAAx] input constantF S x) :
    Γ ⊢[PRAAx] input constantF S y := by
  simpa only [GaussianRadiusExponentialName.subst_input,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    (Prf.eqSubst1 (input constantF (Syn.shift S) (var 0)) e
      (by simpa only [GaussianRadiusExponentialName.subst_input,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h))

private theorem sample_congr (p S x y : PTm n) (e : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] sample p x S ≐ sample p y S :=
  congrAp2 GaussianBinetExponentialPanel.expoF (.eqRefl p) (congrPairT (.eqRefl S) e)

theorem original_product (p X Y D sign R T a b M j : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hb : Γ ⊢[PRAAx] le one b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetLaplaceExponential.nameF p
        (GaussianBinetLaplaceExponential.data (realNumerator X D M j) (M*Y) (M*D) sign (R+one) T a b))
      (qmul (ap2 GaussianBinetLaplaceExponential.nameF p (GaussianBinetLaplaceExponential.data X Y D sign R T a b))
        (ap2 decayF p (decayData (a*j) (b*M)))) (num 10) (unit p) := by
  let A := realNumerator X D M j
  let B := M*Y
  let E := M*D
  let x := GaussianBinetLaplaceExponential.exponent X Y D sign a b
  let y := decayPoint (a*j) (b*M)
  let z := GaussianBinetLaplaceExponential.exponent A B E sign a b
  let C := (R+one)*T
  have shifted := shifted_source X Y D sign R M j h hM hj
  have hx := GaussianSignedNameExponentialOrder.constant_input _ _
    (GaussianBinetLaplaceExponential.exponent_bound X Y D sign R T a b h hb ht)
  have hy := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF y (constant_regular _)
  have hz := GaussianSignedNameExponentialOrder.constant_input _ _
    (GaussianBinetLaplaceExponential.exponent_bound A B E sign (R+one) T a b shifted hb ht)
  have e : Γ ⊢[PRAAx] qadd x y ≐ z := exponent_shift X Y D sign a b M j h.andE₁ hb hM
  have certificate := GaussianBinetExponentialPanel.product_sample p x y (R*T) (GaussianNameBounds.U constantF y) C
    hx hy (input_congr C z (qadd x y) e.eqSymm hz)
    (GaussianBinetLaplaceExponential.exponent_nonpositive X Y D sign a b h.andE₁.andE₂ hb)
    (GaussianBinetLaplaceScalarMajorant.decay_nonpositive (a*j) (b*M) (positive_product _ _ hb hM))
  exact distance_congr (sample_congr p C (qadd x y) z e) (.eqRefl _) (.eqRefl _) (.eqRefl _) certificate

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleShift
