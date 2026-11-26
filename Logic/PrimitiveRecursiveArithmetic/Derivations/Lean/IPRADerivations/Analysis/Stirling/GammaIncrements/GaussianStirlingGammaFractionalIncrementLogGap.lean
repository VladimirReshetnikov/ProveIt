import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationLogarithm
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingGlobalBoundsShiftArguments
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementConvexity

/-!
# A unit gap for the literal log observations

The finite rational harmonic interval from one is exactly the
original integer harmonic logarithm on its enlarged factorial scale.
The same-mesh relative logarithm bound then applies to consecutive
integer observations without any change to its leading coefficient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementLogGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianHarmonicLogarithmName (clock observation sample sample_at)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaFractionalIncrementConvexity (pred_positive)
open GaussianStirlingNames (logXF logXData)
open RationalGaussianEmbedding (embed embed_at embedF)
open RationalHarmonicInterval (common horizon interval left_horizon)
open GaussianPositiveRationalLogarithmProperness (commonLog log_at_common)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (pred monus)
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem interval_from_one (a Q : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] interval a one Q ≐ GammaMeshRobinLogBridge.harmonicLog a Q := by
  let L := horizon a one Q
  let F := fact L
  let X := S (Q*a) F
  let Y := S (Q*one) F
  let Z := S Q F
  have e : Γ ⊢[PRAAx] Y ≐ Z := congrAp2 (sumF hB) (by ipra_ring) (.eqRefl _)
  have same : Γ ⊢[PRAAx] common a one Q L ≐ commonLog a Q L :=
    (RationalIntegerNormalization.normalize_at X Y F).eqSymm.eqTrans
      ((congrAp3 RationalIntegerNormalization.normalizeF (.eqRefl X) e (.eqRefl F)).eqTrans
        (RationalIntegerNormalization.normalize_at X Z F))
  exact same.eqTrans (log_at_common a Q L ha (left_horizon a one Q))

theorem sample_from_one (a p : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] ap2 logXF p (logXData a one) ≐
      ap2 GaussianGammaFiniteApproximantName.logF (clock p) a := by
  let Q := GammaEulerConstantName.mesh (clock p)
  let X := interval a one Q
  let Y := GammaMeshRobinLogBridge.harmonicLog a Q
  have e : Γ ⊢[PRAAx] embed X ≐ embed Y :=
    (embed_at X).eqSymm.eqTrans ((congrAp1 embedF (interval_from_one a Q ha)).eqTrans (embed_at Y))
  exact (sample_at p a one).eqTrans (e.eqTrans (GaussianGammaFiniteApproximantName.log_sample_at (clock p) a).eqSymm)

theorem log_gap (i p : PTm n) (hi : Γ ⊢[PRAAx] le two i) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logXF p (logXData i one))
      (ap2 logXF p (logXData (pred i) one)) one (pred i) := by
  have ha := pred_positive i hi
  have hb := le_trans RationalAlgebra.two_positive hi
  have e := pos_of_one_le hb
  have hpi : Γ ⊢[PRAAx] le (pred i) i :=
    le_congr (.eqRefl _) e.eqSymm (le_succ_self _)
  have hg : Γ ⊢[PRAAx] monus i (pred i) ≐ one := by
    have h := natEq (eq_add_of_le hpi)
    have ep := natEq e
    apply deriveNat
    ipra_simps
    linear_combination ep-h
  have hgap : Γ ⊢[PRAAx] le (pred i*monus i (pred i)) (one*pred i) :=
    le_congr (congrMul (.eqRefl _) hg).eqSymm (by ipra_ring) (le_refl (pred i*one))
  exact distance_congr (sample_from_one i p hb).eqSymm (sample_from_one (pred i) p ha).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianGaussMultiplicationLogarithm.integer_log_distance_at (pred i) i (clock p) one (pred i) ha hpi ha hgap)

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementLogGap
