import IPRADerivations.Analysis.Euler.Integration.Decay.CompactBounds.GaussianEulerDecayCompactLower
import IPRADerivations.Analysis.Euler.Integration.Decay.CompactBounds.GaussianEulerDecayCompactUpper
import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalCompactObservationTightening
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.Named.GaussianNamedEulerUnitKernel
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayRealSamples
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadraturePrecision

/-!
# An actual compact unit-interval input from the original Euler decay

For native 1/E <= a/b <= T, use the unchanged original decay sample at
Fast(G,p), where G=2*(3^T+4E). Both genuine scalar margins absorb its
actual dyadic allowance. Every actual observation is therefore real
and lies exactly in [1/G,1-1/G]. The actual retimed PR2 name remains
cross-equivalent to the original decay, with independent observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitDecayInput

open_ipra
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
export GaussianEulerIntegrandName (subst_originalDecayData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def compactDenominator (E T : PTm n) : PTm n := two*(pw (num 3) T+two*(two*E))
def clock (p E T : PTm n) : PTm n := GaussianFastValueCut.exponent (compactDenominator E T) p
abbrev nameF : PR 2 := GaussianFastValueCut.nameF decayF
def data (a b E T : PTm n) : PTm n := GaussianFastValueCut.nameData (compactDenominator E T) (decayData a b)
def source (a b E T : PTm n) : Fm PTm n := le one b ⋏
  (le one E ⋏ (le one T ⋏ (le b (E*a) ⋏ le a (T*b))))

ipra_subst compactDenominator
ipra_subst clock
ipra_subst data
ipra_subst source

theorem lower_margin_budget (E T : PTm n) : Γ ⊢[PRAAx] le (two*pw (num 3) T) (compactDenominator E T) :=
  le_congr (by ipra_ring) (by unfold compactDenominator; ipra_ring)
    (mul_le_mul_right two (le_add_right (pw (num 3) T) (two*(two*E))))

theorem upper_margin_budget (E T : PTm n) : Γ ⊢[PRAAx] le (two*(two*(two*E))) (compactDenominator E T) :=
  le_congr (by ipra_ring) (by unfold compactDenominator; ipra_ring)
    (mul_le_mul_right two (le_add_left (two*(two*E)) (pw (num 3) T)))

theorem denominator_positive (E T : PTm n) : Γ ⊢[PRAAx] le one (compactDenominator E T) := by
  have hM := GaussianPolynomialPerturbation.power_positive (Γ := Γ) (num 3) T (zero_lt_succ two)
  have double : Γ ⊢[PRAAx] le (pw (num 3) T) (two*pw (num 3) T) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right (pw (num 3) T) (pw (num 3) T))
  exact le_trans hM (le_trans double (lower_margin_budget E T))

theorem clock_later (p E T : PTm n) : Γ ⊢[PRAAx] le p (clock p E T) := le_add_right _ _

theorem read_budget (p E T : PTm n) : Γ ⊢[PRAAx] le (compactDenominator E T) (unit (clock p E T)) :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (compactDenominator E T) (unit_positive p)))
    (GaussianFastValueCut.query_budget _ _)

/-- Code equality with the original decay, including its actual read query. -/
theorem sample_at (p a b E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data a b E T) ≐ ap2 decayF (clock p E T) (decayData a b) :=
  (GaussianFastValueCut.name_at decayF (compactDenominator E T) (decayData a b) p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRadiusExponentialName.sample_canonical constantF
      (GaussianNameBounds.U constantF (decayPoint a b)) (clock p E T) (decayPoint a b)))

theorem sample_canonical (p a b E T : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 nameF p (data a b E T)) := GaussianFastValueCut.name_canonical _ _ _ _

private theorem scaled_regularity_at (p q a b E T : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 decayF p (decayData a b)) (ap2 decayF q (decayData a b))
      (compactDenominator E T*(unit p+unit q)) (unit p*unit q) := by
  have bound := denominator_positive (Γ := Γ) E T
  have raw := GaussianNameEquivalence.point_at (Γ := Γ) decayF (decayData a b) p q
    (GaussianEulerDecayQuadraturePrecision.observation_regular _ _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (by ipra_le (𝔞(unit p)+𝔞(unit q))*𝔞(unit p)*𝔞(unit q)*sl bound) raw

private theorem original_scaled_regularity (a b E T : PTm n) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular decayF (compactDenominator E T) (decayData a b) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  refine .allI (.allI ?_)
  simpa only [GaussianFastValueCut.regular,subst_compactDenominator,subst_originalDecayData,Syn.shift,sh] using
    scaled_regularity_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (sh a) (sh b) (sh E) (sh T)

theorem name_regular (a b E T : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data a b E T) :=
  GaussianFastValueCut.name_fast decayF _ _ (original_scaled_regularity a b E T)

theorem original_observations (p q a b E T : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data a b E T)) (ap2 decayF q (decayData a b))
      (unit p+unit q) (unit p*unit q) := by
  have grow := GaussianExponentialReference.unit_monotone (clock_later (Γ := Γ) p E T)
  have raw := GaussianNameEquivalence.point_at (Γ := Γ) decayF (decayData a b) (clock p E T) q
    (GaussianEulerDecayQuadraturePrecision.observation_regular a b)
  exact distance_congr (sample_at p a b E T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
      (positive_product _ _ (unit_positive p) (unit_positive q)) (by ipra_le 𝔞(unit q)^2*sl grow) raw)

theorem original_decay (a b E T : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF decayF (data a b E T) (decayData a b) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,subst_originalDecayData,Syn.shift,sh] using
    original_observations (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (sh a) (sh b) (sh E) (sh T)

theorem observation_source (p a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianUnitIntervalInputDecoding.source (ap2 nameF p (data a b E T)) (compactDenominator E T) := by
  let r := clock p E T
  let x := ap2 decayF r (decayData a b)
  have lower := RationalCompactObservationTightening.lower_guard (fstT x) (pw (num 3) T) (compactDenominator E T) (unit r)
    (GaussianPolynomialPerturbation.power_positive (num 3) T (zero_lt_succ two)) (lower_margin_budget E T) (read_budget p E T)
    (GaussianEulerDecayCompactLower.original_decay_lower r a b T h.andE₁ h.andE₂.andE₂.andE₂.andE₂)
  have hM : Γ ⊢[PRAAx] le one (two*(two*E)) := positive_product _ _ (le_succ_self one)
    (positive_product _ _ (le_succ_self one) h.andE₂.andE₁)
  have upper := RationalCompactObservationTightening.upper_guard (fstT x) (two*(two*E)) (compactDenominator E T) (unit r)
    hM (upper_margin_budget E T) (read_budget p E T)
    (GaussianEulerDecayCompactUpper.original_decay_upper r a b E h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁)
  have actual : Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source x (compactDenominator E T) :=
    .andI (GaussianEulerDecayRealSamples.original_observation_axis r a b h.andE₁)
      (.andI (denominator_positive E T) (.andI lower upper))
  simpa using Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
    (GaussianUnitIntervalInputDecoding.source (var 0) (Syn.shift (compactDenominator E T)))
    (sample_at p a b E T).eqSymm (by simpa using actual)

theorem admissible_samples (a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianNamedEulerUnitKernel.admissibleSamples nameF (data a b E T) (compactDenominator E T) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedEulerUnitKernel.admissibleSamples,subst_data,subst_compactDenominator,Syn.shift] using
    observation_source (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) hs

/-- Supply the native parameter disk independently; no kernel-output premise. -/
theorem unit_kernel_source (z R B a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    GaussianNamedEulerUnitKernel.source nameF (data a b E T) z R B (compactDenominator E T) :=
  .andI (.andI hB (.andI (denominator_positive E T) hz)) (.andI (name_regular a b E T) (admissible_samples a b E T h))

theorem actual_original_compact_decay_unit_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN nameF (data (var 0) (var 1) (var 2) (var 3)) ⋏ GaussianNamedEulerUnitKernel.admissibleSamples nameF
        (data (var 0) (var 1) (var 2) (var 3)) (compactDenominator (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (name_regular _ _ _ _) (admissible_samples _ _ _ _ Prf.hyp0)))

theorem actual_retimed_unit_input_is_original_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (crossEquivalent nameF decayF (data (var 0) (var 1) (var 2) (var 3)) (decayData (var 0) (var 1))) :=
  closeUniv 4 (original_decay _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitDecayInput
