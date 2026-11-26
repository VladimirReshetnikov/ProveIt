import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorGridUniformObservations
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductUniformMass
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalFiniteCentralDiskBound

/-!
# The original degree-two Barnes polynomial on its first two nodes

The first normalized difference of the stored polynomial is its linear
coefficient plus the step times the quadratic coefficient. Both entries
include the actual finite central scalar at the same cutoff and clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorFirstPolynomial

open_ipra
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteTaylorGrid (polynomial)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (polynomialGrid scaledPolynomial)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianNamedDifferenceQuotient (actual_inverse inverse separated)
open GaussianPolynomialForwardDifferenceGrid (point sample_lookup)
open GaussianRationalCoefficientScaling (scaled_lookup)
open GaussianRationalHorner (evaluate hornerF horner_succ horner_zero ofGaussian ofGaussian_canonical qadd qadd_canonical qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticCoefficientValues (qadd_recode_left qadd_sub_recode qmul_recode_left)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_left qmul_zero_right qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qmul_associative qmul_one_right)
open GaussianRationalNaturalScale (natScale_zero natScale_one_canonical)
open GaussianTranslatedNonconstant (recode recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quadraticCap (R : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteCentralDiskBound.cap (R+one)*
    GaussianBarnesCanonicalTaylorProductUniformMass.cap (R+one) zero

private theorem horner_at_one (P x : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.horner P x one ≐ recode (entry P zero) :=
  (horner_succ P x zero).eqTrans
    (qadd_congr ((qmul_congr (horner_zero P x) (.eqRefl x)).eqTrans (qmul_zero_left x)) (.eqRefl _))

theorem first_quotient (P h B : PTm n) (hLen : Γ ⊢[PRAAx] length P ≐ succ two)
    (hs : Γ ⊢[PRAAx] separated h B) :
    Γ ⊢[PRAAx] qmul (inverse h B) (qsub (evaluate P (ofGaussian h B)) (evaluate P GaussianRationalHorner.qzero)) ≐
      qadd (qmul (entry P zero) (ofGaussian h B)) (entry P one) := by
  let w := ofGaussian h B
  let a := qadd (qmul (entry P zero) w) (entry P one)
  let c := entry P two
  let s := inverse h B
  have atTwo : Γ ⊢[PRAAx] GaussianRationalHorner.horner P w two ≐ a :=
    (horner_succ P w one).eqTrans (qadd_congr
      ((qmul_congr (horner_at_one P w) (.eqRefl _)).eqTrans (qmul_recode_left _ _)) (.eqRefl _))
  have ev : Γ ⊢[PRAAx] evaluate P w ≐ qadd (qmul a w) c :=
    (congrAp3 hornerF hLen (.eqRefl _) (.eqRefl _)).eqTrans
      ((horner_succ P w two).eqTrans (qadd_congr (qmul_congr atTwo (.eqRefl _)) (.eqRefl _)))
  have base : Γ ⊢[PRAAx] evaluate P GaussianRationalHorner.qzero ≐ recode c :=
    (congrAp3 hornerF hLen (.eqRefl _) (.eqRefl _)).eqTrans
      ((horner_succ P _ two).eqTrans (qadd_congr (qmul_zero_right _) (.eqRefl _)))
  have sub : Γ ⊢[PRAAx] qsub (qadd (qmul a w) c) (recode c) ≐ qmul a w :=
    (qsub_congr ((qadd_commutative _ _).eqTrans (qadd_recode_left c (qmul a w)).eqSymm) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.qmul_canonical _ _))
  have cancel : Γ ⊢[PRAAx] qmul s (qmul a w) ≐ a :=
    (qmul_congr (.eqRefl s) (GaussianRationalPowerAlgebra.qmul_commutative a w)).eqTrans
      ((qmul_associative s w a).eqSymm.eqTrans
        ((qmul_congr (actual_inverse h B hs) (.eqRefl a)).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (qmul_one_right a (qadd_canonical _ _)))))
  exact (qmul_congr (.eqRefl s) ((qsub_congr ev base).eqTrans sub)).eqTrans cancel

theorem first_row (t q z h R B H r : PTm n)
    (hs : Γ ⊢[PRAAx] separated h B) :
    Γ ⊢[PRAAx] qmul (inverse h B)
      (qsub (entry (polynomialGrid t q z h R B H r zero two) one)
        (entry (polynomialGrid t q z h R B H r zero two) zero)) ≐
      qadd (qmul (entry (scaledPolynomial t q z R B H r zero two) zero) (ofGaussian h B))
        (entry (scaledPolynomial t q z R B H r zero two) one) := by
  let P := scaledPolynomial t q z R B H r zero two
  let w := ofGaussian h B
  let c : PTm n := GaussianRationalHorner.qzero
  have oneAt : Γ ⊢[PRAAx] point c w one ≐ w :=
    (qadd_congr (.eqRefl _) (natScale_one_canonical _ (ofGaussian_canonical _ _ hs.andE₁))).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (ofGaussian_canonical _ _ hs.andE₁))
  have zeroAt : Γ ⊢[PRAAx] point c w zero ≐ c :=
    (qadd_congr (.eqRefl _) (natScale_zero w)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qzero_canonical)
  have front := (sample_lookup P (succ two) c w one (le_succ_self two)).eqTrans
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl P) oneAt)
  have base := (sample_lookup P (succ two) c w zero (zero_lt_succ two)).eqTrans
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl P) zeroAt)
  exact (qmul_congr (.eqRefl _) (qsub_congr front base)).eqTrans
    (first_quotient P h B (GaussianBarnesCanonicalFiniteTaylorGridObservations.scaled_polynomial_length t q z R B H r zero two) hs)

theorem leading_bound (t q z R B H r : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B) :
    Γ ⊢[PRAAx] bounded (entry (scaledPolynomial t q z R B H r zero two) zero) (quadraticCap R) one := by
  let S := R+one
  let Q := GaussianBarnesCanonicalExponentTaylorBallSchedule.precision q S (two*H)
  let P := polynomial q z R B H r zero two
  let s := ap2 finiteNameF t (finiteData z S B r)
  have hP : Γ ⊢[PRAAx] length P ≐ succ two :=
    GaussianBarnesCanonicalFiniteWeightedTaylorValue.polynomial_length q z S B (two*H) r zero
  have at0 : Γ ⊢[PRAAx] entry P zero ≐ GaussianBarnesCanonicalTaylorProductCoefficientCauchy.productCoefficient Q z S B r zero two :=
    entry_congr (.eqRefl _) (monus_self (two : PTm n)).eqSymm
  have level := GaussianBarnesCanonicalTaylorProductUniformMass.raw_bound Q z S B r zero two hz (le_refl two)
  have cap := GaussianBarnesCanonicalFiniteCentralDiskBound.samples z S B r hz
  have observable := GaussianNamedMultiplyRate.sample_bound_at finiteNameF (finiteData z S B r) _ t cap
  have product := GaussianRationalReciprocal.bounded_product s (entry P zero) _ _ _ _ (le_refl one) (le_refl one) observable
    (GaussianRationalReciprocal.bound_congr at0.eqSymm (.eqRefl _) (.eqRefl _) level)
  exact GaussianRationalReciprocal.bound_congr
    (scaled_lookup P s zero (lt_congr (.eqRefl _) hP.eqSymm (zero_lt_succ two))).eqSymm
      (.eqRefl _) (one_mul one) product

theorem to_linear (t q z h R B H r : PTm n) (hz : Γ ⊢[PRAAx] source z (R+one) B)
    (hn : Γ ⊢[PRAAx] separated h B) (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] distanceBounded (qmul (inverse h B)
      (qsub (entry (polynomialGrid t q z h R B H r zero two) one)
        (entry (polynomialGrid t q z h R B H r zero two) zero)))
      (entry (scaledPolynomial t q z R B H r zero two) one) (quadraticCap R*H) B := by
  let P := scaledPolynomial t q z R B H r zero two
  let a := entry P zero
  let b := entry P one
  let w := ofGaussian h B
  let m := qmul a w
  have step := GaussianBarnesCanonicalHeadPolynomialDerivative.step_bound h B H hn.andE₁ hh
  have product := GaussianRationalReciprocal.bounded_product a w _ _ _ _ (le_refl one) hn.andE₁
    (leading_bound t q z R B H r hz) step
  have cancel : Γ ⊢[PRAAx] qsub (qadd m b) b ≐ m :=
    (qsub_congr (qadd_commutative _ _) (.eqRefl _)).eqTrans
      ((qadd_sub_recode b m).eqTrans (recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)))
  exact GaussianRationalReciprocal.bound_congr
    ((qsub_congr (first_row t q z h R B H r hn) (.eqRefl b)).eqTrans cancel).eqSymm
    (.eqRefl _) (one_mul B) product

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorFirstPolynomial
