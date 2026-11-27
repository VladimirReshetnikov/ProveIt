import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.Chords.GaussianGammaNegativeIntervalChordRate
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.GaussianGammaNegativeIntervalGammaSign
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.Chords.GaussianGammaMinimumQuotientReadback
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate

/-!
# Small derivative residuals control the original signed Gamma variation

The actual divided difference, multiplied by the literal chord step,
gives the endpoint variation with the additional factor `1/W`.
The same rate is preserved under the fixed interval sign.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCenterVariation

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator increment)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalChordStep (quotientData quotient_input exact_increment increment_distance)
open GaussianGammaNegativeIntervalChordInverse (poleMargin)
open GaussianGammaNegativeIntervalChordRate (chordWeight cost original_derivative_rate)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameBounds (all_samples_bounded)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalPowerAlgebra (unit_bounded unit_power norm_one)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "T" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "td" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "gd" => GaussianGammaNegativeIntervalNative.data

private theorem sign_samples (N : PTm n) : Γ ⊢[PRAAx] sampleBound constantF (signUnit (succ N)) one := by
  refine .allI ?_
  have fixed : Γ.map Fm.shift ⊢[PRAAx] bounded (signUnit (succ (Syn.shift N))) one one :=
    unit_bounded _ (unit_power _ _ ((GaussianRationalRelativeTwoTerm.norm_negative qone).eqTrans norm_one))
  simpa only [sampleBound,Syn.shift,GaussianGammaNegativeIntervalProductSign.subst_signUnit,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (constant_at (var 0) (signUnit (succ (Syn.shift N)))).eqSymm (.eqRefl _) (.eqRefl _) fixed

theorem original_center_rate (p a c b N K C z : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (GaussianCoefficientNameBounds.unit p)) : Γ ⊢[PRAAx]
    independentRate gammaF gammaF
      (gd (centerNumerator a c (chordWeight p a b)) (centerDenominator b (chordWeight p a b)) N) (gd a b N)
      (cost a b N K+C) (chordWeight p a b*GaussianCoefficientNameBounds.unit p) := by
  let W := chordWeight p a b
  let A := centerNumerator a c W
  let D := centerDenominator b W
  let U := GaussianCoefficientNameBounds.unit p
  have hu := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) p
  have hw : Γ ⊢[PRAAx] le one W := le_trans hu (GaussianGammaNegativeIntervalChordRate.unit_le_chord_weight p a b)
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have h := quotient_input a c b N W ha hc hw apart
  have inc : Γ ⊢[PRAAx] bounded (ofGaussian (increment a c) D) one W :=
    bound_congr (exact_increment a c b W hb hw) (.eqRefl _) (.eqRefl _) (increment_distance a c b W ha hc hw)
  have rate := GaussianNamedRateComposition.same_denominator QF T zeroF (quotientData a c b N W) (td a b N) z
    (cost a b N K) U C hu (original_derivative_rate p a c b N K ha hc apart hma hmc) residual
  have move := GaussianGammaMinimumQuotientReadback.original_endpoint_rate gammaF gammaF (gd A D N) (gd a b N)
    (increment a c) D z one W _ U h hu hw inc rate
  exact GaussianNamedDifferenceRate.rate_parameters_congr gammaF gammaF _ _ _ _ _ _ (one_mul _) (.eqRefl _) move

theorem signed_center_rate (p a c b N K C z : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (GaussianCoefficientNameBounds.unit p)) : Γ ⊢[PRAAx]
    independentRate signedF signedF
      (signedData (centerNumerator a c (chordWeight p a b)) (centerDenominator b (chordWeight p a b)) N)
      (signedData a b N) (cost a b N K+C) (chordWeight p a b*GaussianCoefficientNameBounds.unit p) := by
  let W := chordWeight p a b
  let U := GaussianCoefficientNameBounds.unit p
  let A := centerNumerator a c W
  let D := centerDenominator b W
  let x := gd A D N
  let y := gd a b N
  let s := signUnit (succ N)
  let C' := cost a b N K+C
  have hu := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) p
  have hw : Γ ⊢[PRAAx] le one W := le_trans hu (GaussianGammaNegativeIntervalChordRate.unit_le_chord_weight p a b)
  have hd := positive_product _ _ hw hu
  have hr := GaussianGammaNegativeIntervalChordStep.center_guard a c b W ha hc hw
  have hx := GaussianGammaNegativeIntervalNative.negative_regular A D N hr
  have hy := GaussianGammaNegativeIntervalNative.negative_regular a b N ha
  have hs := constant_regular (Γ := Γ) s
  have rate := GaussianNamedMultiplyRate.independent_rate constantF gammaF constantF gammaF s x s y
    zero one C' (W*U) (GaussianNameBounds.U gammaF x) one (le_refl one) hd hs hx hs hy
    (all_samples_bounded gammaF x hx) (sign_samples N)
    (GaussianNamedAddRate.self_rate constantF s hs) (original_center_rate p a c b N K C z ha hc apart hma hmc residual)
  exact GaussianNamedDifferenceRate.rate_parameters_congr signedF signedF _ _ _ _ _ _
    (by dsimp only [GaussianNamedMultiplyRate.leadingNumerator,C']; ipra_ring)
    (by dsimp only [GaussianNamedMultiplyRate.leadingDenominator]; ipra_ring) rate

theorem actual_original_negative_Gamma_signed_center_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((guard (var 1) (var 3) ⋏ (guard (var 2) (var 3) ⋏ ((lt (var 1) (var 2) ⋎ lt (var 2) (var 1)) ⋏
        (poleMargin (var 1) (var 3) (var 5) ⋏ poleMargin (var 2) (var 3) (var 5))))) ⟶
        independentRate T zeroF (td (var 1) (var 3) (var 4)) (var 7) (var 6) (GaussianCoefficientNameBounds.unit (var 0)) ⟶
        independentRate signedF signedF
          (signedData (centerNumerator (var 1) (var 2) (chordWeight (var 0) (var 1) (var 3)))
            (centerDenominator (var 3) (chordWeight (var 0) (var 1) (var 3))) (var 4))
          (signedData (var 1) (var 3) (var 4)) (cost (var 1) (var 3) (var 4) (var 5)+var 6)
          (chordWeight (var 0) (var 1) (var 3)*GaussianCoefficientNameBounds.unit (var 0))) :=
  closeUniv 8 (.impI (.impI (signed_center_rate _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCenterVariation
