import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianExponentialSmallPerturbation

/-!
# Rational observations of a named negative-interval increment

The two offsets are decoded at one late clock. The exact difference
of these fractions approximates any equivalent increment name. This
lets a small named increment control the rational derivative envelope.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseIncrementInput

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianFastValueCut (recode_distance)
open GaussianGammaNegativeIntervalNamedInput (sampleNumerator sampleDenominator)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianNamedEulerUnitTime (source source_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_two_errors distance_symmetric distance_triangle_same norm_from_distance_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianUnitIntervalInputDecoding (fraction_recode)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def frozenFraction (f : PR 2) (r x : PTm n) : PTm n :=
  fraction (sampleNumerator f r x) (sampleDenominator f r x)

def increment (f g : PR 2) (r x y : PTm n) : PTm n :=
  qsub (frozenFraction g r y) (frozenFraction f r x)

ipra_subst frozenFraction

ipra_subst increment

private theorem fraction_distance (f : PR 2) (r x E : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (frozenFraction f r x) zero (unit r) := by
  let u := ap2 f r x
  have recoded := fraction_recode u E (source_at f r x E hf)
  have zero_at_one := distance_congr recoded.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (recode_distance u)
  exact distance_radius_mono _ _ zero one zero (unit r) (le_refl _) (unit_positive r)
    (by ipra_le 0) (distance_symmetric _ _ _ _ (le_refl one) zero_at_one)

theorem frozen_sample_error (f g : PR 2) (r x y E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (D g f) r (dd y x)) (increment f g r x y) (num 6) (unit r) := by
  have hr := unit_positive (Γ := Γ) r
  have raw := GaussianNamedDifference.sample_error g f y x r hg.andE₁ hf.andE₁
  have decode := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hr
    (fraction_distance g r y E hg) (fraction_distance f r x E hf)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hr raw decode)

theorem approx_increment (f g K : PR 2) (q r x y z E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent (D g f) K (dd y x) z) (hqr : Γ ⊢[PRAAx] le q r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 K q z) (increment f g r x y) (num 8) (unit q) := by
  have hq := unit_positive (Γ := Γ) q
  have hr := unit_positive (Γ := Γ) r
  have late := unit_monotone hqr
  have diff := cross_at K (D g f) z (dd y x) q r (cross_symm _ _ _ _ he)
  have near := distance_two_errors _ _ _ _ _ hq hr hq (le_refl _) late diff
  have freeze := distance_radius_mono _ _ (num 6) (unit r) (num 6) (unit q) hr hq
    (by ipra_le 6*sl late) (frozen_sample_error f g r x y E hf hg)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hq near freeze)

theorem frozen_step_small (f g K : PR 2) (p r x y z E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent (D g f) K (dd y x) z)
    (small : Γ ⊢[PRAAx] smallSamples K z one (unit p)) (hr : Γ ⊢[PRAAx] le (num 8*unit p) (unit r)) :
    Γ ⊢[PRAAx] distanceBounded (frozenFraction g r y) (frozenFraction f r x) two (unit p) := by
  let u := ap2 K r z
  let v := increment f g r x y
  have hp := unit_positive (Γ := Γ) p
  have hR := unit_positive (Γ := Γ) r
  have compare := approx_increment f g K r r x y z E hf hg he (le_refl r)
  have near := distance_radius_mono v u (num 8) (unit r) one (unit p) hR hp
    (le_congr (.eqRefl _) (one_mul _).eqSymm hr) (distance_symmetric _ _ _ _ hR compare)
  change Γ ⊢[PRAAx] GaussianRationalMetric.bounded v two (unit p)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (norm_from_distance_same hp near (small_samples_at K z one (unit p) r small))

theorem actual_named_inverse_increment_rational_approximation_closed (f g K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 0) (var 3) ⋏ (source g (var 1) (var 3) ⋏
        crossEquivalent (D g f) K (dd (var 1) (var 0)) (var 2))) ⟶ le (var 4) (var 5) ⟶
          distanceBounded (ap2 K (var 4) (var 2)) (increment f g (var 5) (var 0) (var 1)) (num 8) (unit (var 4))) :=
  closeUniv 6 (.impI (.impI (approx_increment f g K _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

theorem actual_named_inverse_increment_rational_step_small_closed (f g K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 0) (var 3) ⋏ (source g (var 1) (var 3) ⋏
        crossEquivalent (D g f) K (dd (var 1) (var 0)) (var 2))) ⟶
        smallSamples K (var 2) one (unit (var 4)) ⟶ le (num 8*unit (var 4)) (unit (var 5)) ⟶
          distanceBounded (frozenFraction g (var 5) (var 1)) (frozenFraction f (var 5) (var 0)) two (unit (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (frozen_step_small f g K _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedInverseIncrementInput
