import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadQuadratic
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaReciprocalDegreeCells
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# Original finite harmonic-power points for the Gamma head

The SAME original reciprocal-power finite sums, embedded on the real
axis, start at zero and acquire the actual power (1/(N+1))^m at every
original numerical successor. At m=1 they equal the unchanged original
factorial harmonicPoint. These exact identities provide the harmonic
power kernel for the original Euler-head logarithmic derivative; no
head or Gamma coefficient recurrence is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHarmonicPowerPoints

open_ipra
open GaussianRationalHorner (qzero qadd qmul ofGaussian)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr)
open GaussianRationalReciprocal (power)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (m N : PTm n) : PTm n := embed (RationalReciprocalPowerName.harmonicPrefix m N)
ipra_subst point

theorem point_canonical (m N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (point m N) :=
  RationalGaussianEmbedding.embed_canonical _

theorem reciprocal_power (m N : PTm n) : Γ ⊢[PRAAx]
    power (reciprocalPoint N) m ≐ embed (RationalReciprocalPowerTail.reciprocalPower m (succ N)) := by
  have base : Γ ⊢[PRAAx] ofGaussian ComplexLogarithmRemainder.oneCode (one*succ N) ≐ reciprocalPoint N :=
    GaussianIntegerFractionPowers.fraction_congr (.eqRefl _) (one_mul _)
  have separated := GaussianGammaReciprocalDegreeCells.separated_power (Γ := Γ)
    ComplexLogarithmRemainder.oneCode one (succ N) m (le_refl one) (zero_lt_succ N)
  exact (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl m) base).eqSymm.eqTrans
    (separated.eqTrans ((qmul_congr (GaussianRationalRoundedPower.qone_power m) (.eqRefl _)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (RationalGaussianEmbedding.embed_canonical _))))

theorem point_zero (m : PTm n) : Γ ⊢[PRAAx] point m zero ≐ qzero :=
  (RationalGaussianRealPart.embed_congr (RationalReciprocalPowerTail.tail_zero m zero)).eqTrans
    RationalGaussianEmbedding.embed_zero

theorem point_step (m N : PTm n) : Γ ⊢[PRAAx]
    point m (succ N) ≐ qadd (point m N) (power (reciprocalPoint N) m) :=
  (RationalGaussianRealPart.embed_congr ((RationalReciprocalPowerTail.tail_succ m zero N).eqTrans
    (RationalAlgebra.add_congr (.eqRefl _)
      (RationalReciprocalPowerTail.reciprocal_congr (.eqRefl m) (congrSucc (zero_add N)))))).eqTrans
        ((RationalGaussianEmbedding.embed_add _ _).eqTrans (qadd_congr (.eqRefl _) (reciprocal_power m N).eqSymm))

def firstLaw (N : PTm n) : Fm PTm n := point one N ≐ GaussianGammaCanonicalExponent.harmonicPoint N
ipra_subst firstLaw

theorem first_zero : Γ ⊢[PRAAx] firstLaw (zero : PTm n) :=
  (point_zero one).eqTrans GaussianGammaEulerHeadQuadratic.harmonic_zero.eqSymm

theorem first_step (N : PTm n) (ih : Γ ⊢[PRAAx] firstLaw N) : Γ ⊢[PRAAx] firstLaw (succ N) :=
  (point_step one N).eqTrans
    ((qadd_congr ih (GaussianRationalPowerAlgebra.power_one _ (GaussianGammaEulerHeadQuadratic.reciprocal_canonical N))).eqTrans
      (GaussianGammaHarmonicIncrement.harmonic_point_increment N).eqSymm)

theorem first_is_original_harmonic (N : PTm n) : Γ ⊢[PRAAx] firstLaw N := by
  have all : Γ ⊢[PRAAx] .all (firstLaw (var 0)) := by
    ipra_qfind [subst_firstLaw]
    · exact first_zero
    · exact first_step _ Prf.hyp0
  simpa only [subst_firstLaw,Syn.subst_var,Syn.inst_zero] using all.allE N

theorem original_harmonic_power_point_numerical_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (point (var 0) (succ (var 1)) ≐ qadd (point (var 0) (var 1)) (power (reciprocalPoint (var 1)) (var 0))) :=
  closeUniv 2 (point_step _ _)

theorem original_first_harmonic_power_is_factorial_harmonic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (point one (var 0) ≐ GaussianGammaCanonicalExponent.harmonicPoint (var 0)) :=
  closeUniv 1 (first_is_original_harmonic _)

end LeanProofs.IPRA.Analysis.GaussianGammaHarmonicPowerPoints
