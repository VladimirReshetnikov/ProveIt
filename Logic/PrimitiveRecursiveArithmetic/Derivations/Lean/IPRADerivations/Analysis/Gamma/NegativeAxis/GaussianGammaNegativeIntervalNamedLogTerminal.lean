import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalUniformBounds
import IPRADerivations.Analysis.Stirling.GaussianStirlingOddCoefficients

/-!
# Uniform variation of the positive terminal Gamma

After shifting a negative-interval argument, the positive terminal
argument lies in (1,2). A fixed disk and real margin give one dyadic
modulus for all rational encodings of the offset.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedLogTerminal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qone)
open GaussianStirlingGammaLogarithm (arg gammaData gamma_source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def terminalModulus (s : PTm n) : PTm n := GaussianGammaHalfPlaneInputContinuity.modulus s two one

private def compactData (a b : PTm n) : PTm n :=
  GaussianGammaReciprocalInverse.gammaData (arg (b+a)) two b one

@[simp] private theorem subst_compactData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (compactData a b) = compactData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [compactData,GaussianGammaReciprocalInverse.gammaData,GaussianGammaReciprocalInverse.gammaHeight,one,two]

@[simp] theorem subst_terminalModulus {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (terminalModulus s) = terminalModulus (Syn.subst σ s) := by
  simp [terminalModulus,two,one]

theorem modulus_later (s : PTm n) : Γ ⊢[PRAAx] le s (terminalModulus s) := by
  let i := GaussianGammaHalfPlaneInputContinuity.inverseClock s two one
  let X := GaussianGammaEulerContinuityReference.inputGain (GaussianGammaInputContinuity.accuracy i two) two
    (GaussianGammaInputContinuity.cutoff i two)
  have h : Γ ⊢[PRAAx] le s i := le_add_right s _
  exact le_trans h (le_trans (le_add_right i X) (le_add_right (i+X) _))

private theorem compact_source (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source (arg (b+a)) two b one := by
  let A := b+a
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hA : Γ ⊢[PRAAx] le A (two*b) := by unfold A; ipra_le sl (le_of_lt h.andE₂)
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (arg A) (two*b) :=
    le_congr (GaussianGammaGaussReference.scaled_one_norm A).eqSymm (.eqRefl _) (le_mul_mono hA hA)
  have edge : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (arg A) one b := by
    unfold GaussianEulerLowerPowerCoefficients.realLower
    apply zle_of_toZ a
    simp only [A,arg,ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    ring
  exact .andI (.andI (le_refl one) (.andI (.andI hb disk) edge)) (le_succ_self one)

private theorem translated_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qadd qone (fraction a b) ≐ fraction (b+a) b :=
  (qadd_congr (GaussianRationalExponentialTangent.fraction_one b hb).eqSymm (.eqRefl _)).eqTrans
    (GaussianStirlingOddCoefficients.fraction_add_same b a b hb)

theorem translated_distance (a b c d A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) : Γ ⊢[PRAAx]
    distanceBounded (fraction (b+a) b) (fraction (d+c) d) A D :=
  distance_congr (translated_fraction a b hb) (translated_fraction c d hd) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.sum_right_error qone _ _ _ _ hD h)

private theorem terminal_cross (a b : PTm n) (h : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    crossEquivalent gammaF gammaF (compactData a b) (gammaData (b+a) b) :=
  GaussianGammaRadiusOverlap.original_Gamma_overlap (arg (b+a)) two (b+a) b one one one b
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ (compact_source a b h))
    (gamma_source _ _ (GaussianGammaNegativeCriticalEndpoints.shifted_source a b h))

private theorem fixed_rate (s a b c d : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) one (unit (terminalModulus s))) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF (compactData a b) (compactData c d) one (unit s) := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have sa : Δ ⊢[PRAAx] guard (sh a) (sh b) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaNegativeCriticalCorrection.subst_guard] using ha.shift.shift
  have sc : Δ ⊢[PRAAx] guard (sh c) (sh d) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaNegativeCriticalCorrection.subst_guard] using hc.shift.shift
  have near : Δ ⊢[PRAAx] distanceBounded (fraction (sh a) (sh b)) (fraction (sh c) (sh d)) one
      (unit (terminalModulus (sh s))) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianPositiveRationalLogarithm.subst_fraction,
      GaussianRationalMetric.subst_distanceBounded,GaussianCoefficientNameBounds.subst_unit,
      subst_terminalModulus,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hIn.shift.shift
  have shifted := translated_distance (sh a) (sh b) (sh c) (sh d) one (unit (terminalModulus (sh s)))
    (le_trans sa.andE₁ (le_of_lt sa.andE₂)) (le_trans sc.andE₁ (le_of_lt sc.andE₂)) (unit_positive _) near
  have core : Δ ⊢[PRAAx] distanceBounded
      (ap2 gammaF (var 1) (compactData (sh a) (sh b))) (ap2 gammaF (var 0) (compactData (sh c) (sh d)))
      (rateNumerator one (unit (sh s)) (var 1) (var 0)) (rateDenominator (unit (sh s)) (var 1) (var 0)) :=
    GaussianGammaHalfPlaneInputContinuity.original_gamma_observations (var 1) (var 0) (sh s)
      (arg (sh b+sh a)) (arg (sh d+sh c)) two (sh b) (sh d) one
      (compact_source _ _ sa) (compact_source _ _ sc) shifted
  refine .allI (.allI ?_)
  simpa only [independentRate,sh,Syn.shift,subst_compactData,GaussianCoefficientNameBounds.subst_unit,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using core

theorem terminal_rate (s a b c d : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (hIn : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) one (unit (terminalModulus s))) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF (gammaData (b+a) b) (gammaData (d+c) d) one (unit s) :=
  GaussianNamedRateTransport.transport gammaF gammaF gammaF gammaF (compactData a b) (compactData c d)
    (gammaData (b+a) b) (gammaData (d+c) d) one (unit s) (unit_positive s)
    (fixed_rate s a b c d ha hc hIn)
    (cross_symm _ _ _ _ (terminal_cross a b ha)) (cross_symm _ _ _ _ (terminal_cross c d hc))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedLogTerminal
