import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Coefficients.GaussianGammaFixedCoefficientRecurrence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Coefficients.GaussianGammaRecurrenceWeightCompatibility
import IPRADerivations.Analysis.Gamma.EulerProducts.OriginalPrefixes.GaussianGammaOriginalPrefixCoefficientNames
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale

/-!
# Actual original recurrence samples against canonical named observations

The original C19 common coefficient clock supplies ONE source precision
and radius for every coefficient in the proved finite recurrence.
Every such coefficient compares to the SAME canonical all-degree name
with its original independent observation error. The genuine C17 error
compares the same source weights to the literal full gamma/zeta names.
The exact finite recurrence then gives an independent-p/t bound between
the scaled canonical coefficient observation and the SAME original
weighted finite sum. No coefficient or recurrence comparison is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceSourceObservations

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaRecurrenceWeights (weight)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (e : PTm n) : PTm n := succ e
def sourceRadius (e : PTm n) : PTm n := two*radius e
def precision (t e : PTm n) : PTm n := GaussianGammaOriginalPrefixCoefficientVariation.precision t (radius e) e
def cap (e : PTm n) : PTm n := GaussianGammaOriginalPrefixCoefficientVariation.cap (radius e) e
def sourceCoefficient (t e j : PTm n) : PTm n := fixedCoefficient (precision t e) (sourceRadius e) j
def sourceSum (t e : PTm n) : PTm n := GaussianGammaFixedCoefficientRecurrence.weightedSum (precision t e) (sourceRadius e) e
@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (e : PTm n) : Syn.subst σ (radius e) = radius (Syn.subst σ e) := by simp [radius]
@[simp] theorem subst_sourceRadius {l : ℕ} (σ : Fin n → PTm l) (e : PTm n) :
    Syn.subst σ (sourceRadius e) = sourceRadius (Syn.subst σ e) := by simp [sourceRadius]
@[simp] theorem subst_precision {l : ℕ} (σ : Fin n → PTm l) (t e : PTm n) :
    Syn.subst σ (precision t e) = precision (Syn.subst σ t) (Syn.subst σ e) := by simp [precision]
@[simp] theorem subst_cap {l : ℕ} (σ : Fin n → PTm l) (e : PTm n) : Syn.subst σ (cap e) = cap (Syn.subst σ e) := by simp [cap]
@[simp] theorem subst_sourceCoefficient {l : ℕ} (σ : Fin n → PTm l) (t e j : PTm n) :
    Syn.subst σ (sourceCoefficient t e j) = sourceCoefficient (Syn.subst σ t) (Syn.subst σ e) (Syn.subst σ j) := by simp [sourceCoefficient]
@[simp] theorem subst_sourceSum {l : ℕ} (σ : Fin n → PTm l) (t e : PTm n) :
    Syn.subst σ (sourceSum t e) = sourceSum (Syn.subst σ t) (Syn.subst σ e) := by simp [sourceSum]

theorem denominator_positive (p q : PTm n) : Γ ⊢[PRAAx] le one (unit p*unit q) :=
  GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)

theorem precision_later (t e : PTm n) : Γ ⊢[PRAAx] le t (precision t e) :=
  GaussianGammaOriginalPrefixCoefficientVariation.precision_later t (radius e) e

theorem original_coefficient_error (t p e j : PTm n) (hj : Γ ⊢[PRAAx] le j e) : Γ ⊢[PRAAx]
    distanceBounded (sourceCoefficient t e j) (sample p j) (cap e*unit p+unit t) (unit t*unit p) :=
  distance_congr (GaussianGammaOriginalPrefixCoefficientNames.reader_fixed t (radius e) e j hj)
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianGammaOriginalPrefixCoefficientNames.original_reader_to_canonical t p (radius e) e j (zero_lt_succ e) hj)

theorem original_source_recurrence (t s : PTm n) : Γ ⊢[PRAAx]
    natScale s (sourceCoefficient t (succ s) (succ s)) ≐ sourceSum t (succ s) :=
  GaussianGammaFixedCoefficientRecurrence.original_fixed_coefficient_recurrence _ _ _
    (le_of_eq_add (d := num 3*succ s+num 5) (by unfold sourceRadius radius; ipra_ring))

theorem original_weight_error (t p e m : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (weight (precision t e) (two*sourceRadius e) m) (weight p zero m)
      (unit t+unit p) (unit t*unit p) := by
  have grow : Γ ⊢[PRAAx] le (unit t) (unit (precision t e)) :=
    GaussianFactorBudget.power_monotone_length two t (precision t e) (le_succ_self one) (precision_later t e)
  have budget : Γ ⊢[PRAAx]
      le ((unit (precision t e)+unit p)*(unit t*unit p)) ((unit t+unit p)*(unit (precision t e)*unit p)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit (precision t e)*unit t*unit p) (mul_le_mul_right (unit p*unit p) grow))
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive (precision t e) p) (denominator_positive t p) budget
    (GaussianGammaRecurrenceWeightCompatibility.original_source_full_error (precision t e) p (two*sourceRadius e) m)

theorem scale_distance (s q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    distanceBounded (natScale s q) (natScale s r) (s*A) B :=
  distance_congr (GaussianRationalNaturalScale.natScale_as_product s q).eqSymm
    (GaussianRationalNaturalScale.natScale_as_product s r).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance _ _ _ _ _ _ hB (GaussianNamedNaturalScale.natural_point_bound s) h)

theorem original_canonical_recurrence_source_error (p t s : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (natScale s (sample p (succ s))) (sourceSum t (succ s))
      (s*(cap (succ s)*unit p+unit t)) (unit t*unit p) :=
  distance_congr (.eqRefl _) (original_source_recurrence t s) (.eqRefl _) (.eqRefl _)
    (scale_distance s _ _ _ _ (denominator_positive t p)
      (distance_symmetric _ _ _ _ (denominator_positive t p) (original_coefficient_error t p (succ s) (succ s) (le_refl _))))

theorem original_Gamma_canonical_coefficients_source_independent_observation_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le (var 3) (var 2) ⟶ distanceBounded (sourceCoefficient (var 0) (var 2) (var 3)) (sample (var 1) (var 3))
        (cap (var 2)*unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (.impI (original_coefficient_error _ _ _ _ Prf.hyp0))

theorem original_Gamma_canonical_scaled_coefficient_against_actual_recurrence_source_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (natScale (var 2) (sample (var 0) (succ (var 2)))) (sourceSum (var 1) (succ (var 2)))
        (var 2*(cap (succ (var 2))*unit (var 0)+unit (var 1))) (unit (var 1)*unit (var 0))) :=
  closeUniv 3 (original_canonical_recurrence_source_error _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceSourceObservations
