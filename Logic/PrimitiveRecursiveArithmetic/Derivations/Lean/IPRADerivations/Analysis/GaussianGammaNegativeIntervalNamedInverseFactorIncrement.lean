import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedInverseFactor
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedInverseIncrementInput
import IPRADerivations.Analysis.GaussianNamedMultiplyRate

/-!
# Variation of the named inverse shift factor along an actual increment

Both inverse factors are compared to their own rational readings at
one late clock. The certified increment controls the two frozen offsets
while the common window bounds every inverse observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseFactorIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaNegativeIntervalInverseRationalEnvelope (inverse_bound_on_window window_envelope)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator)
open GaussianGammaNegativeIntervalNamedInverseFactor (nameF data clock rationalMap rational_at)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedEulerUnitTime (source encoded_source)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (E N : PTm n) : PTm n := two*inverseGapCost (succ N) (E*E)

def freezeClock (p q E N : PTm n) : PTm n := (p+num 3)+clock q E N

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (E N : PTm n) :
    Syn.subst σ (gain E N) = gain (Syn.subst σ E) (Syn.subst σ N) := by
  simp [gain,two]

theorem sample_at (f : PR 2) (q x E N : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) q (data x E N) ≐
      inverse (sampleNumerator f (clock q E N) x) (sampleDenominator f (clock q E N) x) N :=
  (GaussianNamedUnitIntervalRationalLift.sample_at rationalMap f q x E N).eqTrans (rational_at _ _ _)

theorem observation_bounded (f : PR 2) (q x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) q (data x E N)) (E*E) one := by
  let r := clock q E N
  exact GaussianRationalReciprocal.bound_congr (sample_at f q x E N).eqSymm (.eqRefl _) (.eqRefl _)
    (inverse_bound_on_window (sampleNumerator f r x) (sampleDenominator f r x) E N (encoded_source f r x E hf))

theorem all_samples_bounded (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] sampleBound (nameF f) (data x E N) (E*E) := by
  let sh (t : PTm n) := Syn.shift t
  have h : Γ.map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) :=
    by simpa only [Fm.shift,GaussianNamedEulerUnitTime.subst_source,Syn.shift,sh] using hf.shift
  refine .allI ?_
  simpa only [Syn.shift,sh,GaussianNamedUnitIntervalRationalLift.subst_data,PTm.subst_mul] using
    observation_bounded f (var 0) (sh x) (sh E) (sh N) h

private theorem freeze_clock_growth (p q E N : PTm n) :
    Γ ⊢[PRAAx] le (num 8*unit p) (unit (freezeClock p q E N)) := by
  have pow : Γ ⊢[PRAAx] pw two (num 3) ≐ num 8 :=
    (pw_succ two (num 2)).eqTrans
      ((congrMul ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))) (.eqRefl _)).eqTrans (by ipra_ring))
  have step : Γ ⊢[PRAAx] unit (p+num 3) ≐ num 8*unit p :=
    (pw_add two p (num 3)).eqTrans ((congrMul (.eqRefl _) pow).eqTrans (mul_comm _ _))
  exact le_congr step (.eqRefl _) (GaussianExponentialReference.unit_monotone (le_add_right _ _))

private theorem frozen_observation (f : PR 2) (q r x E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hr : Γ ⊢[PRAAx] le (clock q E N) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) q (data x E N))
      (inverse (sampleNumerator f r x) (sampleDenominator f r x) N) (num 3) (unit q) := by
  let u := inverse (sampleNumerator f r x) (sampleDenominator f r x) N
  have hq := unit_positive (Γ := Γ) q
  have near := diagonal_rate (nameF f) constantF (data x E N) u one (unit q) q hq
    (GaussianGammaNegativeIntervalNamedInverseFactor.original_frozen_rate f q r x E N hf hr)
  exact distance_congr (.eqRefl _) (constant_at q u) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (num 3) (unit q) (positive_product _ _ hq hq) hq
      (le_of_eq_add (d := zero) (by ipra_ring)) near)

theorem original_diagonal (f g K : PR 2) (p q x y z E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF g f) K (GaussianNamedDifference.data y x) z)
    (hs : Γ ⊢[PRAAx] smallSamples K z one (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) q (data x E N)) (ap2 (nameF g) q (data y E N))
      (diagonalNumerator (gain E N) (unit p) (num 6) q) (diagonalDenominator (unit p) q) := by
  let r := freezeClock p q E N
  let A := sampleNumerator f r x
  let B := sampleDenominator f r x
  let C := sampleNumerator g r y
  let D := sampleDenominator g r y
  let P := unit p
  let Q := unit q
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive q
  have wide := positive_product _ _ hp hq
  have late : Γ ⊢[PRAAx] le (clock q E N) r := le_add_left _ _
  have step := GaussianGammaNegativeIntervalNamedInverseIncrementInput.frozen_step_small f g K p r x y z E
    hf hg he hs (freeze_clock_growth p q E N)
  have frozen := (window_envelope A B C D E N two P
    (encoded_source f r x E hf) (encoded_source g r y E hg) hp step).andE₁
  have mid : Γ ⊢[PRAAx] distanceBounded (inverse A B N) (inverse C D N) (gain E N*Q) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ hp wide
      (le_of_eq_add (d := zero) (by unfold gain; ipra_ring))
      (distance_symmetric _ _ _ _ hp frozen)
  have lift (u v : PTm n) (h : Γ ⊢[PRAAx] distanceBounded u v (num 3) Q) :
      Γ ⊢[PRAAx] distanceBounded u v (num 3*P) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ hq wide (le_of_eq_add (d := zero) (by ipra_ring)) h
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,P,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ wide (lift _ _ (frozen_observation f q r x E N hf late))
      (distance_triangle_same _ _ _ _ _ _ wide mid (lift _ _
        (distance_symmetric _ _ _ _ hq (frozen_observation g q r y E N hg late)))))

theorem original_rate (f g K : PR 2) (p x y z E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF g f) K (GaussianNamedDifference.data y x) z)
    (hs : Γ ⊢[PRAAx] smallSamples K z one (unit p)) : Γ ⊢[PRAAx]
    independentRate (nameF f) (nameF g) (data x E N) (data y E N) (gain E N) (unit p) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 6) (unit_positive p)
    (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular f x E N hf)
    (GaussianGammaNegativeIntervalNamedInverseFactor.name_regular g y E N hg)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hF : Γ.map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) := by
    simpa only [Fm.shift,GaussianNamedEulerUnitTime.subst_source,Syn.shift,sh] using hf.shift
  have hG : Γ.map Fm.shift ⊢[PRAAx] source g (sh y) (sh E) := by
    simpa only [Fm.shift,GaussianNamedEulerUnitTime.subst_source,Syn.shift,sh] using hg.shift
  have hE : Γ.map Fm.shift ⊢[PRAAx]
      crossEquivalent (GaussianNamedDifference.nameF g f) K (GaussianNamedDifference.data (sh y) (sh x)) (sh z) := by
    simpa only [Fm.shift,GaussianNameEquivalence.subst_crossEquivalent,GaussianNamedDifference.subst_data,Syn.shift,sh] using he.shift
  have hS : Γ.map Fm.shift ⊢[PRAAx] smallSamples K (sh z) one (unit (sh p)) := by
    simpa only [Fm.shift,GaussianExponentialSmallPerturbation.subst_smallSamples,
      GaussianCoefficientNameBounds.subst_unit,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift,sh] using hs.shift
  simpa only [diagonalEnvelope,Syn.shift,sh,GaussianNamedUnitIntervalRationalLift.subst_data,
    GaussianCoefficientNameBounds.subst_unit,subst_gain,PTm.subst_num] using
    original_diagonal f g K (sh p) (var 0) (sh x) (sh y) (sh z) (sh E) (sh N) hF hG hE hS

theorem actual_named_negative_Gamma_inverse_factor_bounded_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ sampleBound (nameF f) (data (var 0) (var 1) (var 2)) (var 1*var 1)) :=
  closeUniv 3 (.impI (all_samples_bounded f _ _ _ Prf.hyp0))

theorem actual_named_negative_Gamma_inverse_factor_increment_closed (f g K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 1) (var 4) ⋏ (source g (var 2) (var 4) ⋏
        (crossEquivalent (GaussianNamedDifference.nameF g f) K (GaussianNamedDifference.data (var 2) (var 1)) (var 3) ⋏
         smallSamples K (var 3) one (unit (var 0))))) ⟶
        independentRate (nameF f) (nameF g) (data (var 1) (var 4) (var 5)) (data (var 2) (var 4) (var 5))
          (gain (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 6 (.impI (original_rate f g K _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseFactorIncrement
