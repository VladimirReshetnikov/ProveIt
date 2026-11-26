import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitLogarithmicRate
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionKernel
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerExponentCompactBounds
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate

/-!
# Uniform variation of the unchanged actual unit-interval Euler kernel

The original nested kernel and its own computed radii are retained.
Every exponent observation lies in (R+1)*J(E,E). The genuine normalized
product rate and the checked common-radius exponential rate therefore
give 3^((R+1)J)*(R+1)*E^2 times the original time distance. Independent
radius properness returns the estimate to the original kernel data.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactRate

open_ipra
open GaussianEulerUnitSubstitutionKernel (nameF data exponentF exponentData)
open GaussianEulerIntegrandName (coefficient)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a b E : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏
  GaussianEulerUnitCompactTimeBounds.source a b E
def input (z R B a b c d E X Y : PTm n) : Fm PTm n := source z R B a b E ⋏
  (source z R B c d E ⋏ (le one Y ⋏ distanceBounded (GaussianPositiveRationalLogarithm.fraction a b) (GaussianPositiveRationalLogarithm.fraction c d) X Y))
def exponentRadius (R E : PTm n) : PTm n := (R+one)*GaussianEulerUnitCompactTimeBounds.radius E
def majorant (R E : PTm n) : PTm n := pw (num 3) (exponentRadius R E)
def lipschitz (R E : PTm n) : PTm n := majorant R E*(R+one)*GaussianEulerUnitLogarithmicRate.lipschitz E

ipra_subst source
ipra_subst input
ipra_subst exponentRadius
ipra_subst majorant
ipra_subst lipschitz

theorem kernel_source (z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source z R B a b E) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionKernel.source z B a b := .andI h.andE₁.andE₁ h.andE₂.andE₁

theorem exponent_bound (p z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source z R B a b E) : Γ ⊢[PRAAx]
    bounded (ap2 exponentF p (exponentData z B a b)) (exponentRadius R E) one := by
  have prod := GaussianRationalReciprocal.bounded_product _ _ (R+one) one (GaussianEulerUnitCompactTimeBounds.radius E) one
    (le_refl one) (le_refl one) (GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁.andE₁ h.andE₁.andE₂.andE₂)
    (GaussianEulerUnitCompactTimeBounds.original_composition_bound (GaussianEulerUnitSubstitutionKernel.powerClock p z B a b) a b E h.andE₂)
  exact GaussianRationalReciprocal.bound_congr (GaussianEulerUnitSubstitutionKernel.exponent_at p z B a b).eqSymm
    (.eqRefl _) (by ipra_ring) prod

theorem common_input (z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source z R B a b E) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (exponentRadius R E) (exponentData z B a b) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .andI (GaussianEulerUnitSubstitutionKernel.exponent_regular z B a b (kernel_source z R B a b E h)) (.allI ?_)
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerUnitSubstitutionKernel.subst_exponentData,
    subst_exponentRadius,Syn.shift] using
    exponent_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift E) hs

theorem original_bound (p z R B a b E : PTm n) (h : Γ ⊢[PRAAx] source z R B a b E) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data z B a b)) (majorant R E) one := by
  let U := GaussianEulerUnitSubstitutionKernel.radius z B a b
  have raw := GaussianPositiveExponentialMajorant.disk_bound _ (exponentRadius R E) (GaussianRadiusExponentialName.index U p)
    (exponent_bound (GaussianRadiusExponentialName.inputPrecision U p) z R B a b E h)
  exact GaussianRationalReciprocal.bound_congr (GaussianRadiusExponentialName.sample_at exponentF U p (exponentData z B a b)).eqSymm (.eqRefl _) (.eqRefl _) raw

private theorem log_samples (a b E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source a b E) : Γ ⊢[PRAAx]
    GaussianNamedMultiplyRate.sampleBound GaussianEulerUnitLogarithmicComposition.nameF (GaussianEulerUnitLogarithmicComposition.data a b)
      (GaussianEulerUnitCompactTimeBounds.radius E) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source (Syn.shift a) (Syn.shift b) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianEulerUnitLogarithmicComposition.subst_data,
    GaussianEulerUnitCompactTimeBounds.subst_radius,Syn.shift,GaussianEulerUnitLogarithmicComposition.sample] using
    GaussianEulerUnitCompactTimeBounds.original_composition_bound (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) hs

private theorem coefficient_samples (z R B E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E) : Γ ⊢[PRAAx]
    GaussianNamedMultiplyRate.sampleBound constantF (coefficient z B) (R+one) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianEulerIntegrandName.subst_coefficient,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (coefficient (Syn.shift z) (Syn.shift B))).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerIntegrandName.coefficient_bound _ _ _ hs.andE₁ hs.andE₂.andE₂)

theorem exponent_rate (z R B a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input z R B a b c d E X Y) : Γ ⊢[PRAAx]
    independentRate exponentF exponentF (exponentData z B a b) (exponentData z B c d)
      ((R+one)*GaussianEulerUnitLogarithmicRate.lipschitz E*X) Y := by
  let L := GaussianEulerUnitLogarithmicComposition.nameF
  let u := coefficient z B
  let x := GaussianEulerUnitLogarithmicComposition.data a b
  let y := GaussianEulerUnitLogarithmicComposition.data c d
  have hc := constant_regular (Γ := Γ) u
  have hx := GaussianEulerUnitLogarithmicComposition.name_regular a b h.andE₁.andE₂.andE₁
  have hy := GaussianEulerUnitLogarithmicComposition.name_regular c d h.andE₂.andE₁.andE₂.andE₁
  have rate := GaussianEulerUnitLogarithmicRate.original_rate a b c d E X Y
    (.andI h.andE₁.andE₂ (.andI h.andE₂.andE₁.andE₂ h.andE₂.andE₂))
  have product := GaussianNamedMultiplyRate.independent_rate constantF L constantF L u x u y zero one
    (GaussianEulerUnitLogarithmicRate.lipschitz E*X) Y (GaussianEulerUnitCompactTimeBounds.radius E) (R+one)
    (le_refl one) h.andE₂.andE₂.andE₁ hc hx hc hy (log_samples a b E h.andE₁.andE₂)
    (coefficient_samples z R B E h.andE₁.andE₁) (GaussianNamedDifferenceRate.self_rate constantF u hc) rate
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring) (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) product

theorem original_rate (z R B a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input z R B a b c d E X Y) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z B a b) (data z B c d) (lipschitz R E*X) Y := by
  let M := exponentRadius R E
  let x := exponentData z B a b
  let y := exponentData z B c d
  have hx := GaussianEulerUnitSubstitutionKernel.exponent_regular z B a b (kernel_source z R B a b E h.andE₁)
  have hy := GaussianEulerUnitSubstitutionKernel.exponent_regular z B c d (kernel_source z R B c d E h.andE₂.andE₁)
  have cx := common_input z R B a b E h.andE₁
  have cy := common_input z R B c d E h.andE₂.andE₁
  have rate := GaussianRadiusExponentialLipschitzRate.independent_rate exponentF exponentF M x y
    ((R+one)*GaussianEulerUnitLogarithmicRate.lipschitz E*X) Y
    (.andI h.andE₂.andE₂.andE₁ (.andI cx (.andI cy (exponent_rate z R B a b c d E X Y h))))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF _ M x x
    (GaussianEulerUnitSubstitutionKernel.exponential_input z B a b (kernel_source z R B a b E h.andE₁)) cx (cross_refl _ _ hx)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF exponentF _ M y y
    (GaussianEulerUnitSubstitutionKernel.exponential_input z B c d (kernel_source z R B c d E h.andE₂.andE₁)) cy (cross_refl _ _ hy)
  have own := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ h.andE₂.andE₂.andE₁ rate left right
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold lipschitz majorant GaussianRadiusExponentialLipschitzRate.factor; dsimp only [M]; ipra_ring) (.eqRefl _) own

theorem original_observations (p q z R B a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input z R B a b c d E X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z B a b)) (ap2 nameF q (data z B c d))
      (rateNumerator (lipschitz R E*X) Y p q) (rateDenominator Y p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate z R B a b c d E X Y h)

theorem actual_original_unit_kernel_uniform_compact_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      independentRate nameF nameF (data (var 0) (var 2) (var 3) (var 4)) (data (var 0) (var 2) (var 5) (var 6))
        (lipschitz (var 1) (var 7)*var 8) (var 9)) :=
  closeUniv 10 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactRate
