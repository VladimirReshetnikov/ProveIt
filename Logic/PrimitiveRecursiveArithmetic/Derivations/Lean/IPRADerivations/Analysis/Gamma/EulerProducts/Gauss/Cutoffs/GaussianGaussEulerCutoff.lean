import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.Heads.GaussianGammaGaussEulerHeads
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ShiftedProducts.GaussianGammaGaussDomain
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerInverseApproximationName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationLogarithm

/-!
# Uniform upward Euler cutoffs for the Gauss comparison

The finite Euler error remains valid at every cutoff above its
computed cofinal threshold. The larger scaled cutoff (m(N+1)-1)
also dominates (N) at positive order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerCutoff

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerInverseApproximationName (cutoff_guards cutoff_threshold rateScale)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator
  coefficient_denominator_positive actual_observation_error)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaReciprocalInverse (source gammaF gammaData)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "neededCutoff" => GaussianGammaEulerInverseApproximationName.cutoff
local notation "gaussCutoff" => GaussianGammaGaussEulerHeads.cutoff

theorem larger_cutoff_error (p q z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a d) (hN : Γ ⊢[PRAAx] le (neededCutoff p R a d) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 eulerF (succ p) (eulerData z R B d N)) (ap2 gammaF q (gammaData z R B d))
      (unit p+unit q) (unit p*unit q) := by
  have guards := cutoff_guards (Γ := Γ) p R a d
  have full : Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source z R B a d N :=
    .andI h (.andI (le_trans guards.andE₁ hN) (le_trans guards.andE₂.andE₁ hN))
  have pos := coefficient_denominator_positive z R B a d N full
  have hm := le_trans (cutoff_threshold p R a d h.andE₂.andE₁)
    (le_mul_mono (le_refl (rateScale R a)) hN)
  have comparison : Γ ⊢[PRAAx]
      le (rateNumerator (coefficientNumerator R d) (coefficientDenominator R a N) (succ p) q*(unit p*unit q))
        ((unit p+unit q)*rateDenominator (coefficientDenominator R a N) (succ p) q) := by
    have step := natEq (pw_succ (Γ := Γ) two p)
    ipra_le 𝔞 (unit p)*𝔞 (unit q)*𝔞 (unit q)*sl hm using
      unfold rateNumerator rateDenominator coefficientDenominator rateScale unit
      ipra_simps
      rw [step]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ (succ p) q pos)
    (positive_product _ _ (unit_positive p) (unit_positive q)) comparison
    (actual_observation_error (succ p) q z R B a d N full)

theorem scaled_cutoff_later (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le N (gaussCutoff m N) := by
  have count := GaussianGammaGaussEulerHeads.cutoff_count m N hm
  have h := le_congr (one_mul (succ N)) count
    (le_mul_mono hm (le_refl (succ N)))
  exact succ_monus_succ _ _ |>.eqSymm.eqTrans h

theorem scaled_log_cutoff (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] GaussianGaussMultiplicationLogarithm.top m N ≐ gaussCutoff m N := by
  let L := gaussCutoff m N
  have e := (congrMul (.eqRefl m) (succ_eq_add_one (Γ := Γ) N).eqSymm).eqTrans
    (GaussianGammaGaussEulerHeads.cutoff_count m N hm)
  exact (congrMonus e (.eqRefl one)).eqTrans ((succ_monus_succ L _).eqTrans (monus_zero L))

def commonCutoff (p R m a d : PTm n) : PTm n :=
  neededCutoff p (R+one) a (d*m)+neededCutoff p (scaledRadius R m) a d+neededCutoff p one one m+one

ipra_subst commonCutoff [one]

theorem common_guards (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    let N := commonCutoff p R m a d
    Γ ⊢[PRAAx] le one N ⋏ (le (neededCutoff p (R+one) a (d*m)) N ⋏
      (le (neededCutoff p (scaledRadius R m) a d) (gaussCutoff m N) ⋏ le (neededCutoff p one one m) N)) := by
  let N := commonCutoff p R m a d
  let s := neededCutoff p (R+one) a (d*m)
  let t := neededCutoff p (scaledRadius R m) a d
  let u := neededCutoff p one one m
  have hs : Γ ⊢[PRAAx] le s N :=
    le_congr (.eqRefl _) (by dsimp only [N,commonCutoff,s,t,u]; ipra_ring) (le_add_right s (t+u+one))
  have ht : Γ ⊢[PRAAx] le t N :=
    le_congr (.eqRefl _) (by dsimp only [N,commonCutoff,s,t,u]; ipra_ring) (le_add_right t (s+u+one))
  have hu : Γ ⊢[PRAAx] le u N :=
    le_congr (.eqRefl _) (by dsimp only [N,commonCutoff,s,t,u]; ipra_ring) (le_add_right u (s+t+one))
  exact .andI (le_add_left one (s+t+u)) (.andI hs (.andI (le_trans ht (scaled_cutoff_later m N hm)) hu))

theorem actual_larger_Euler_cutoff_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      le (neededCutoff (var 0) (var 3) (var 5) (var 6)) (var 7) ⟶
        distanceBounded (ap2 eulerF (succ (var 0)) (eulerData (var 2) (var 3) (var 4) (var 6) (var 7)))
          (ap2 gammaF (var 1) (gammaData (var 2) (var 3) (var 4) (var 6)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (.impI (larger_cutoff_error _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_Gauss_common_Euler_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶
      let N := commonCutoff (var 0) (var 1) (var 2) (var 3) (var 4)
      le one N ⋏ (le (neededCutoff (var 0) (var 1+one) (var 3) (var 4*var 2)) N ⋏
        (le (neededCutoff (var 0) (scaledRadius (var 1) (var 2)) (var 3) (var 4)) (gaussCutoff (var 2) N) ⋏
          le (neededCutoff (var 0) one one (var 2)) N))) :=
  closeUniv 5 (.impI (common_guards _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerCutoff
