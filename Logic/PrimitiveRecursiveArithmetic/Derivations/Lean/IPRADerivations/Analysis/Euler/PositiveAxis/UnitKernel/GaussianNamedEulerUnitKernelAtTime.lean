import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianNamedEulerUnitOuterLogRate
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianNamedEulerUnitKernelFrozenRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactPowerMajorant

/-!
# The genuine named unit kernel at a known rational logarithmic time

The actual frozen kernel and the actual Euler power use the same
coefficient of two independently evaluated logarithms. Their original
multiplication and exponential programs retain their own clocks and
radii. Together with the named kernel's frozen-input rate, this proves
equality of the represented values at the known positive time.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernelAtTime

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedEulerUnitKernel (nameF data lipschitz encodedData)
open GaussianEulerIntegrandName (coefficient powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x z R B a b E : PTm n) : Fm PTm n :=
  GaussianNamedEulerUnitKernel.source f x z R B E ⋏ GaussianNamedEulerUnitOuterLogRate.source f x a b E
def budget (R E : PTm n) : PTm n := (lipschitz R E+two)+(lipschitz R E+two)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x z R B a b E : PTm n) :
    (source f x z R B a b E).subst σ = source f (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) := by simp [source]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (R E : PTm n) :
    Syn.subst σ (budget R E) = budget (Syn.subst σ R) (Syn.subst σ E) := by simp [budget]

private theorem coefficient_samples (z R B E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound constantF (coefficient z B) (R+one) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianEulerIntegrandName.subst_coefficient,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (coefficient (Syn.shift z) (Syn.shift B))).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianEulerIntegrandName.coefficient_bound _ _ _ hs.andE₁ hs.andE₂.andE₂)

private theorem frozen_log_samples (c d E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source c d E) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound GaussianEulerUnitLogarithmicComposition.nameF
      (GaussianEulerUnitLogarithmicComposition.data c d) (GaussianEulerUnitCompactTimeBounds.radius E) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source (Syn.shift c) (Syn.shift d) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianEulerUnitLogarithmicComposition.subst_data,
    GaussianEulerUnitCompactTimeBounds.subst_radius,Syn.shift,GaussianEulerUnitLogarithmicComposition.sample] using
    GaussianEulerUnitCompactTimeBounds.original_composition_bound (var 0) (Syn.shift c) (Syn.shift d) (Syn.shift E) hs

private theorem power_common_input (z R B a b E : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E E) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input powerExponentF (GaussianEulerUnitKernelCompactRate.exponentRadius R E)
      (powerExponentData z B a b) := by
  refine .andI (GaussianEulerIntegrandName.power_exponent_regular z B a b (.andI hz.andE₁ ht.andE₁)) (.allI ?_)
  have zs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using hz.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerUnitKernelCompactRate.subst_exponentRadius,
    GaussianEulerIntegrandName.subst_powerExponentData,GaussianEulerUnitKernelCompactRate.exponentRadius,
    GaussianEulerUnitCompactTimeBounds.radius,GaussianEulerCompactPowerMajorant.exponentRadius,
    GaussianCompactLogarithmBounds.subst_radius,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    GaussianEulerCompactPowerMajorant.exponent_sample (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift E) (Syn.shift E) (Syn.shift a) (Syn.shift b) zs ts

/-- Keep the original rational kernel and original Euler power evaluators. -/
theorem original_frozen_power_rate (f : PR 2) (k x z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B a b E) :
    Γ ⊢[PRAAx] independentRate GaussianEulerUnitSubstitutionKernel.nameF powerF
      (encodedData f k x z B) (powerData z B a b) (lipschitz R E) (unit k) := by
  let c := numerator (ap2 f k x)
  let d := denominator (ap2 f k x)
  let F := GaussianEulerUnitSubstitutionKernel.exponentF
  let G := powerExponentF
  let X := GaussianEulerUnitSubstitutionKernel.exponentData z B c d
  let Y := powerExponentData z B a b
  let M := GaussianEulerUnitKernelCompactRate.exponentRadius R E
  let A := (R+one)*(E*E)
  let U := coefficient z B
  have hz := h.andE₁.andE₁
  have ht := h.andE₂.andE₂.andE₁
  have hn := unit_positive (Γ := Γ) k
  have hcd : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.source z R B c d E :=
    GaussianNamedEulerUnitKernel.encoded_source f k x z R B E h.andE₁
  have hc := GaussianEulerUnitKernelCompactRate.kernel_source z R B c d E hcd
  have hb : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b := .andI hz.andE₁ ht.andE₁
  have hu := constant_regular (Γ := Γ) U
  have rate := GaussianNamedEulerUnitOuterLogRate.original_rate f k x a b E h.andE₂
  have prod := GaussianNamedMultiplyRate.independent_rate constantF GaussianEulerUnitLogarithmicComposition.nameF
    constantF GaussianPositiveRationalLogarithm.logF U (GaussianEulerUnitLogarithmicComposition.data c d) U
    (GaussianPositiveRationalLogarithm.data a b) zero one (E*E) (unit k) (GaussianEulerUnitCompactTimeBounds.radius E) (R+one)
    (le_refl one) hn hu (GaussianEulerUnitLogarithmicComposition.name_regular c d hc.andE₂)
    hu (GaussianPositiveRationalLogarithm.name_regular a b ht.andE₁) (frozen_log_samples c d E hcd.andE₂)
    (coefficient_samples z R B E hz) (GaussianNamedDifferenceRate.self_rate constantF U hu) rate
  have exponentRate : Γ ⊢[PRAAx] independentRate F G X Y A (unit k) :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by dsimp only [GaussianNamedMultiplyRate.leadingNumerator,A]; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) prod
  have cx := GaussianEulerUnitKernelCompactRate.common_input z R B c d E hcd
  have cy := power_common_input z R B a b E hz ht
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate F G M X Y A (unit k)
    (.andI hn (.andI cx (.andI cy exponentRate)))
  have left := GaussianExponentialRadiusIndependence.same_input_cross F _ M X
    (GaussianEulerUnitSubstitutionKernel.exponential_input z B c d hc) cx
  have right := GaussianExponentialRadiusIndependence.same_input_cross G (powerRadius z B a b) M Y
    (GaussianEulerIntegrandName.power_input z B a b hb) cy
  have own := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hn common left right
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [lipschitz,GaussianEulerUnitKernelCompactRate.lipschitz,GaussianEulerUnitKernelCompactRate.majorant,
          GaussianEulerUnitLogarithmicRate.lipschitz,GaussianRadiusExponentialLipschitzRate.factor,A,M]; ipra_ring)
    (.eqRefl _) own

theorem original_diagonal (f : PR 2) (p x z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B a b E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x z R B E)) (ap2 powerF p (powerData z B a b)) (budget R E) (unit p) := by
  have hn := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hn hn
  have first := GaussianNamedInverseRate.diagonal_rate _ _ _ _ (lipschitz R E) (unit p) p hn
    (GaussianNamedEulerUnitKernelFrozenRate.original_rate f p x z R B E h.andE₁)
  have second := GaussianNamedInverseRate.diagonal_rate _ _ _ _ (lipschitz R E) (unit p) p hn
    (original_frozen_power_rate f p x z R B a b E h)
  have clear : Γ ⊢[PRAAx] le ((lipschitz R E*unit p+two*unit p)*unit p) ((lipschitz R E+two)*(unit p*unit p)) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  exact distance_triangle_same _ _ _ _ _ _ hn
    (distance_radius_mono _ _ _ _ _ _ hd hn clear first)
    (distance_radius_mono _ _ _ _ _ _ hd hn clear second)

theorem original_kernel_at_time (f : PR 2) (x z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B a b E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) powerF (data x z R B E) (powerData z B a b) := by
  have left := GaussianNamedEulerUnitKernel.name_regular f x z R B E h.andE₁
  have right := GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  refine GaussianNameRingLaws.equivalent_of_envelope (nameF f) powerF (data x z R B E) (powerData z B a b) (budget R E) left right (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift a) (Syn.shift b) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNamedEulerUnitKernel.subst_data,
    GaussianEulerIntegrandName.subst_powerData,subst_budget,Syn.shift] using
    original_diagonal f (var 0) (Syn.shift x) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift E) hs

theorem actual_named_unit_kernel_at_rational_time_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent (nameF f) powerF (data (var 0) (var 1) (var 2) (var 3) (var 6)) (powerData (var 1) (var 3) (var 4) (var 5))) :=
  closeUniv 7 (.impI (original_kernel_at_time f _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernelAtTime
