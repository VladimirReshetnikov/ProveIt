import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithm
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate

/-!
# Exponential recovers the original compact positive input

Compare the actual exponential of the lifted logarithm with the original
exponential at one frozen decoded input sample. The finite exponential
uses the same radius and cutoff on both inputs. The original rational
logarithm recovers the decoded input exactly as a name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmExponential

open_ipra
open GaussianNamedPositiveLogarithm (source rationalData numerator denominator)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianCompactLogarithmBounds (domain radius)
open GaussianRadiusExponentialName (input query inputPrecision)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev nameF (f : PR 2) : PR 2 := GaussianRadiusExponentialName.nameF (GaussianNamedPositiveLogarithm.nameF f)
def data (x E T : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius E T) (GaussianNamedPositiveLogarithm.data x E)
def budget (E T : PTm n) : PTm n := factor (radius E T)*(E+two)+two

ipra_subst data
ipra_subst budget

theorem original_rational_input (a b E T : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] input logF (radius E T) (GaussianPositiveRationalLogarithm.data a b) := by
  refine .andI (GaussianPositiveRationalLogarithm.name_regular a b ht.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by
    simpa only [Fm.shift,Syn.shift,GaussianCompactLogarithmBounds.subst_domain] using ht.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift,one] using hE.shift
  simpa only [GaussianPositiveRationalLogarithm.sample,GaussianRadiusExponentialName.boundedSamples,
    GaussianPositiveRationalLogarithm.subst_data,GaussianCompactLogarithmBounds.subst_radius,Syn.shift] using
    GaussianCompactLogarithmBounds.sample_bound (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) es hs

private theorem frozen_query (f : PR 2) (p x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] distanceBounded
      (query (GaussianNamedPositiveLogarithm.nameF f) (radius E T) p (GaussianNamedPositiveLogarithm.data x E))
      (query logF (radius E T) p (rationalData f p x)) (E+two) (unit p) := by
  let r := inputPrecision (radius E T) p
  have later : Γ ⊢[PRAAx] le p r := GaussianRadiusExponentialLipschitzRate.original_clock_later _ _
  have grow := GaussianExponentialReference.unit_monotone later
  have raw := GaussianNamedPositiveLogarithm.original_frozen_observations f r r p x E T hs
  exact distance_radius_mono _ _ _ _ (E+two) (unit p)
    (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive p)) (unit_positive p) (by
      unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
      ipra_le (2*𝔞(unit p)*𝔞(unit r))*sl grow) raw

theorem original_diagonal (f : PR 2) (p x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E T)) (ap2 f p x) (budget E T) (unit p) := by
  let F := GaussianNamedPositiveLogarithm.nameF f
  let R := radius E T
  let X := GaussianNamedPositiveLogarithm.data x E
  let a := numerator f p x
  let b := denominator f p x
  let Y := rationalData f p x
  let c := fraction a b
  have hxy := GaussianNamedPositiveLogarithm.decoded_domain f p x E T hs
  have hX := GaussianNamedPositiveLogarithm.exponential_input f x E T hs
  have hY : Γ ⊢[PRAAx] input logF R Y := original_rational_input a b E T hs.andE₂.andE₁ hxy
  have close := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz (query F R p X) (query logF R p Y)
    R (E+two) (unit p) (GaussianRadiusExponentialName.index R p) (unit_positive p)
    (GaussianRadiusExponentialName.query_bound _ _ _ _ hX) (GaussianRadiusExponentialName.query_bound _ _ _ _ hY)
    (frozen_query f p x E T hs)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E T))
      (GaussianRadiusExponentialName.sample logF R p Y) (factor R*(E+two)) (unit p) :=
    distance_congr (GaussianRadiusExponentialName.sample_at F R p X).eqSymm
      (GaussianRadiusExponentialName.sample_at logF R p Y).eqSymm (.eqRefl _) (.eqRefl _) close
  have rational := cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross logF R (GaussianPositiveRationalLogarithm.radius a b) Y hY
      (GaussianPositiveRationalLogarithm.exponential_input a b hxy.andE₁))
    (GaussianPositiveRationalLogarithm.exponential_fraction a b hxy.andE₁)
  have last := cross_at _ _ _ _ p p rational
  have lastCode := (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) p c).eqTrans
    (GaussianNamedPositiveLogarithm.decoded_value f p x E T hs)
  have second := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive p) (unit_positive p))
    (unit_positive p) (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) lastCode (.eqRefl _) (.eqRefl _) last)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second

theorem original_recovery (f : PR 2) (x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) f (data x E T) x := by
  have regular := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianNamedPositiveLogarithm.exponential_input f x E T hs)
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget E T) regular hs.andE₁ (.allI ?_)
  have ss : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) (Syn.shift T) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedPositiveLogarithm.subst_source] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_data,subst_budget,Syn.shift] using
    original_diagonal f (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift T) ss

theorem actual_original_exponential_recovers_named_positive_input_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ crossEquivalent (nameF f) f (data (var 0) (var 1) (var 2)) (var 0)) :=
  closeUniv 3 (.impI (original_recovery f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmExponential
