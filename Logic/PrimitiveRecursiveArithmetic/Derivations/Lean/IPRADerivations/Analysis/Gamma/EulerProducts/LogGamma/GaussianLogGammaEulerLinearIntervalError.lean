import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerLinearInterval
import IPRADerivations.Analysis.Logarithm.GaussianPositiveRationalLogarithmIncrement

/-!
# The original Euler logarithm interval and its harmonic interval

The common factorial C1 refinement bounds the change of the right-endpoint
harmonic interval from mesh one to any positive mesh by 1/N. Thus the
original logarithms differ from the same harmonic interval used by the exact
linear row sum, with only the two independent observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearIntervalError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GammaEulerConstantName (mesh mesh_positive common_quotient_upper)
open GammaEulerMesh (factorial_quotient synchronous_cleared)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerLinearInterval (harmonicInterval)
open GaussianPositiveRationalLogarithm (baseF)
open GaussianPositiveRationalLogarithmIncrement (increment increment_interval_error)
open GaussianPositiveRationalLogarithmProperness (original_finite_difference)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr)
open Products (fact)
open RationalGaussianEmbedding (embed)
open RationalHarmonicInterval (at_common common common_value horizon interval left_horizon numerator)
open RationalValueBounds (radius radius_congr radius_of_upper)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem sharp_common_refinement (N M K L : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hNM : Γ ⊢[PRAAx] le N M)
    (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K*M) L) :
    Γ ⊢[PRAAx] radius (common M N K L) (common M N one L) one N := by
  let F := fact L
  have hM := le_trans hN hNM
  have mKM : Γ ⊢[PRAAx] le M (K*M) := by ipra_le 𝔞 M*sl hK
  have nL := le_trans hNM (le_trans mKM hL)
  have sharp := synchronous_cleared N M K L hN hNM hK hL
  have gap : Γ ⊢[PRAAx] le (monus M N) M :=
    le_congr (.eqRefl _) (eq_add_of_le hNM).eqSymm (le_add_left _ _)
  have quotient : Γ ⊢[PRAAx] (N*M)*quo F N ≐ M*F :=
    (by ipra_ring : Γ ⊢[PRAAx] (N*M)*quo F N ≐ M*(N*quo F N)).eqTrans
      (congrMul (.eqRefl _) (factorial_quotient N L hN nL))
  have budget : Γ ⊢[PRAAx] le (monus M N*F) ((N*M)*quo F N) :=
    le_congr (.eqRefl _) quotient.eqSymm (mul_le_mul_right F gap)
  let low := S M F+S (K*N) F
  let high := S N F+S (K*M) F
  have added := add_le_add_right (N*M*low) budget
  have scaled : Γ ⊢[PRAAx] le (N*M*high) (N*M*(low+quo F N)) :=
    le_trans sharp.andE₂ (le_congr (by dsimp only [F,low]; ipra_ring) (by ipra_ring) added)
  have upper : Γ ⊢[PRAAx] le high (low+quo F N) :=
    RationalValueBounds.positive_cancel (positive_product _ _ hN hM) scaled
  have lower : Γ ⊢[PRAAx] le low (high+quo F N) :=
    le_trans sharp.andE₁ (le_add_right high (quo F N))
  have hn : Γ ⊢[PRAAx] S (one*N) F ≐ S N F := congrAp2 (sumF hB) (one_mul N) (.eqRefl _)
  have hm : Γ ⊢[PRAAx] S (one*M) F ≐ S M F := congrAp2 (sumF hB) (one_mul M) (.eqRefl _)
  let fine := numerator M N K L
  let coarse := numerator M N one L
  have fineLeft : Γ ⊢[PRAAx] fine.pos+coarse.neg ≐ high :=
    (congrAdd (.eqRefl _) hn).eqTrans (add_comm _ _)
  have fineRight : Γ ⊢[PRAAx] fine.neg+coarse.pos+quo F N ≐ low+quo F N :=
    congrAdd ((congrAdd (.eqRefl _) hm).eqTrans (add_comm _ _)) (.eqRefl _)
  have coarseLeft : Γ ⊢[PRAAx] coarse.pos+fine.neg ≐ low := congrAdd hm (.eqRefl _)
  have coarseRight : Γ ⊢[PRAAx] coarse.neg+fine.pos+quo F N ≐ high+quo F N :=
    congrAdd (congrAdd hn (.eqRefl _)) (.eqRefl _)
  exact radius_of_upper _ _ _ _
    (common_quotient_upper _ _ fine coarse L N hN nL (common_value M N K L) (common_value M N one L)
      (le_congr fineLeft.eqSymm fineRight.eqSymm upper))
    (common_quotient_upper _ _ coarse fine L N hN nL (common_value M N one L) (common_value M N K L)
      (le_congr coarseLeft.eqSymm coarseRight.eqSymm lower))

/-- The same literal harmonic interval changes by at most 1/N under
every positive numerical refinement of mesh one. -/
theorem harmonic_refinement (N r K : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (embed (interval (N+r) N K)) (harmonicInterval N r) one N := by
  let M := N+r
  let L := horizon M N K
  have coarse : Γ ⊢[PRAAx] le (horizon M N one) L :=
    le_mul_mono hK (le_refl _)
  have raw := sharp_common_refinement N M K L hN (le_add_right N r) hK (left_horizon M N K)
  exact RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hN
    (radius_congr (at_common M N K L (le_refl L)) (at_common M N one L coarse) (.eqRefl _) (.eqRefl _) raw)

/-- On a common clock the original base integer logarithm samples are
literally the refined interval, with no extra precision allowance. -/
theorem base_logarithms_at (p N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 baseF p (N+r)) (ap2 baseF p N)) (harmonicInterval N r) one N := by
  have normalized := (qsub_congr (GaussianGammaFiniteApproximantName.log_sample_at p (N+r))
    (GaussianGammaFiniteApproximantName.log_sample_at p N)).eqTrans
      (original_finite_difference (N+r) N (mesh p) (le_trans hN (le_add_right N r)) hN)
  exact distance_congr normalized.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (harmonic_refinement N r (mesh p) hN (mesh_positive p))

def errorNumerator (p q N : PTm n) : PTm n := unit p*unit q+N*(unit p+unit q)
def errorDenominator (p q N : PTm n) : PTm n := N*(unit p*unit q)

private theorem logarithm_slack (p q t N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (qsub (increment p q N one r) (harmonicInterval N r)) (errorNumerator p q N) (errorDenominator p q N) (num 18) t := by
  have h := harmonic_refinement N r (mesh t) hN (mesh_positive t)
  have hU : Γ ⊢[PRAAx] le one ((unit p*unit q)*unit t) :=
    positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hU hN
    (increment_interval_error p q t N one r hN (le_refl one)) h
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold errorNumerator errorDenominator unit; ipra_ring)
    (by unfold errorDenominator unit; ipra_ring) joined

/-- The actual positive-rational logarithm observations used by the
Euler head differ by the same harmonic interval up to 1/N and their
two requested observation errors, uniformly in the interval length. -/
theorem logarithms_at (p q N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (increment p q N one r) (harmonicInterval N r)
      (errorNumerator p q N) (errorDenominator p q N) := by
  let t := GaussianRationalSlackRemoval.precision
    (qsub (increment p q N one r) (harmonicInterval N r)) (errorNumerator p q N) (errorDenominator p q N) (num 18)
  exact GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 18)
    (positive_product _ _ hN (positive_product _ _ (unit_positive p) (unit_positive q)))
    (logarithm_slack p q t N r hN)

theorem original_Euler_logarithm_harmonic_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 2) ⟶ distanceBounded (increment (var 0) (var 1) (var 2) one (var 3))
        (harmonicInterval (var 2) (var 3)) (errorNumerator (var 0) (var 1) (var 2))
        (errorDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (logarithms_at _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerLinearIntervalError
