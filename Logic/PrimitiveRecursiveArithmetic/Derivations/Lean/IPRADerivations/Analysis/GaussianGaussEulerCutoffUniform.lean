import IPRADerivations.Analysis.GaussianGaussEulerCutoff

/-!
# Uniform estimates for the fixed Euler cutoffs in Gauss multiplication

Once a cutoff pays for a cofinal clock, all observations at that fixed
cutoff have a uniform error. The shift by one in the finite row
precision leaves at most two units of total error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerCutoffUniform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerInverseApproximationName (cutoff cutoff_guards cutoff_threshold rateScale)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator actual_observation_error coefficient_denominator_positive)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaReciprocalInverse (source gammaF gammaData)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem cutoff_source (p z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a d) (hN : Γ ⊢[PRAAx] le (cutoff p R a d) N) :
    Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source z R B a d N := by
  have guards := cutoff_guards (Γ := Γ) p R a d
  exact .andI h (.andI (le_trans guards.andE₁ hN) (le_trans guards.andE₂.andE₁ hN))

theorem euler_regular (p z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a d) (hN : Γ ⊢[PRAAx] le (cutoff p R a d) N) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN eulerF (eulerData z R B d N) :=
  GaussianGammaEulerReciprocalInverse.euler_regular z R B a d N
    (.andI h (cutoff_source p z R B a d N h hN).andE₂.andE₁)

private theorem leading_cutoff (p R a d N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le (cutoff p R a d) N) :
    Γ ⊢[PRAAx] le (two*coefficientNumerator R d) (coefficientDenominator R a N) := by
  have unit2 : Γ ⊢[PRAAx] le two (unit (succ p)) := le_congr (one_mul two) (pw_succ two p).eqSymm
    (mul_le_mul_right two (unit_positive p))
  have twice : Γ ⊢[PRAAx] le (two*coefficientNumerator R d) (coefficientNumerator R d*unit (succ p)) :=
    le_congr (mul_comm _ _) (.eqRefl _) (le_mul_mono (le_refl _) unit2)
  exact le_trans twice (le_trans (cutoff_threshold p R a d ha) (le_mul_mono (le_refl (rateScale R a)) hN))

theorem uniform_succ_error (p q z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a d) (hN : Γ ⊢[PRAAx] le (cutoff p R a d) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 eulerF (succ q) (eulerData z R B d N)) (ap2 gammaF q (gammaData z R B d)) two one := by
  let A := coefficientNumerator R d
  let D := coefficientDenominator R a N
  let U := unit q
  have full := cutoff_source p z R B a d N h hN
  have hd := coefficient_denominator_positive z R B a d N full
  have hC : Γ ⊢[PRAAx] le (two*A) D := leading_cutoff p R a d N h.andE₂.andE₁ hN
  have hU := unit_positive (Γ := Γ) q
  have cost : Γ ⊢[PRAAx] le (rateNumerator A D (succ q) q*one) (two*rateDenominator D (succ q) q) := by
    have step := natEq (pw_succ (Γ := Γ) two q)
    ipra_le 𝔞 U*𝔞 U*sl hC+3*𝔞 D*𝔞 U*sl hU using
      unfold rateNumerator rateDenominator U unit
      ipra_simps
      rw [step]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive D _ _ hd) (le_refl one) cost
    (actual_observation_error (succ q) q z R B a d N full)

theorem uniform_error (p q z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a d) (hN : Γ ⊢[PRAAx] le (cutoff p R a d) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 eulerF q (eulerData z R B d N)) (ap2 gammaF q (gammaData z R B d)) (num 3) one := by
  let A := coefficientNumerator R d
  let D := coefficientDenominator R a N
  let U := unit q
  have full := cutoff_source p z R B a d N h hN
  have hd := coefficient_denominator_positive z R B a d N full
  have hC : Γ ⊢[PRAAx] le A D := le_trans (le_of_eq_add (d := A) (by ipra_ring))
    (leading_cutoff p R a d N h.andE₂.andE₁ hN)
  have hU := unit_positive (Γ := Γ) q
  have cost : Γ ⊢[PRAAx] le (rateNumerator A D q q*one) (num 3*rateDenominator D q q) := by
    unfold rateNumerator rateDenominator
    ipra_le 𝔞 U*𝔞 U*sl hC+2*𝔞 D*𝔞 U*sl hU
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive D _ _ hd) (le_refl one) cost
    (actual_observation_error q q z R B a d N full)

theorem retimed_distance (f : PR 2) (p q x : PTm n) (h : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f (succ p) x) (ap2 f (succ q) x) (one*(unit p+unit q)) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have first := GaussianNameEquivalence.point_at f x (succ p) (succ q) h
  have guard : Γ ⊢[PRAAx] le ((unit (succ p)+unit (succ q))*(unit p*unit q))
      ((one*(unit p+unit q))*(unit (succ p)*unit (succ q))) := by
    have eqP := natEq (pw_succ (Γ := Γ) two p)
    have eqQ := natEq (pw_succ (Γ := Γ) two q)
    ipra_le 2*𝔞 P*𝔞 Q*(𝔞 P+𝔞 Q) using
      unfold P Q unit
      rw [eqP,eqQ]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive (succ p)) (unit_positive (succ q)))
    (positive_product _ _ hp hq) guard first

end LeanProofs.IPRA.Analysis.GaussianGaussEulerCutoffUniform
