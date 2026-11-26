import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerRational

/-!
# Compact Euler integrand with named positive parameters

Compose the actual named compact power chart with the original decay
and the unchanged Euler power. A single finite modulus controls changes
of the damping coefficient, exponent, time, and observation indices.
At exact rational parameters this is the original power-damped kernel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerIntegrand

open_ipra
open GaussianNamedDampingPowerChart (product_same_denominator product_observation_bound)
open GaussianEulerDampedNamedIntegrand (decayF decayData)
open GaussianEulerExponentialNamedKernelRate (innerBound)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianGammaCanonicalExponent (constantF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (F G : PR 2) (z Rz B x y C₀ C R₀ R E T a b : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z Rz B E ⋏ GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T a b
abbrev chartF (F G : PR 2) : PR 2 := GaussianNamedDampingPowerChart.nameF F G
abbrev nameF (F G : PR 2) : PR 2 := GaussianEulerDampedNamedIntegrand.nameF (chartF F G)
def data (F G : PR 2) (z B x y a b : PTm n) : PTm n :=
  GaussianEulerDampedNamedIntegrand.data (chartF F G) z B a b (GaussianNamedDampingPowerChart.data F G x y a b)
def decayBound (C R E T : PTm n) : PTm n := innerBound (GaussianNamedDampingPowerChart.majorant C R E T)
def majorant (Rz C R E T : PTm n) : PTm n :=
  GaussianEulerCompactPowerMajorant.majorant Rz E T*decayBound C R E T
def gain (Rz C R E T A₀ A₁ A₂ : PTm n) : PTm n :=
  decayBound C R E T*(GaussianEulerCompactPowerVariation.lipschitz Rz E T*A₂)+
    GaussianEulerCompactPowerMajorant.majorant Rz E T*
      (decayBound C R E T*GaussianNamedDampingPowerChart.gain C R E T A₀ A₁ A₂)

ipra_subst source

ipra_subst data

private theorem chart_disk (F G : PR 2) (x y C₀ C R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T a b) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (chartF F G) (GaussianNamedDampingPowerChart.majorant C R E T)
      (GaussianNamedDampingPowerChart.data F G x y a b) := by
  refine .andI (GaussianNamedDampingPowerChart.name_regular F G x y C₀ C R₀ R E T a b h) (.allI ?_)
  let sh (s : PTm n) := Syn.shift s
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G (sh x) (sh y) (sh C₀) (sh C)
      (sh R₀) (sh R) (sh E) (sh T) (sh a) (sh b) := by simpa only [Fm.shift,Syn.shift,GaussianNamedDampingPowerChart.subst_source,sh] using h.shift
  simpa [GaussianRadiusExponentialName.boundedSamples,GaussianNamedDampingPowerChart.majorant,Syn.shift,sh] using
    GaussianNamedDampingPowerChart.original_observation_bound F G (var 0) (sh x) (sh y) (sh C₀) (sh C)
      (sh R₀) (sh R) (sh E) (sh T) (sh a) (sh b) hs

private theorem decay_samples (F G : PR 2) (x y C₀ C R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G x y C₀ C R₀ R E T a b) :
    Γ ⊢[PRAAx] sampleBound (decayF (chartF F G)) (decayData (chartF F G) (GaussianNamedDampingPowerChart.data F G x y a b))
      (decayBound C R E T) := by
  let sh (s : PTm n) := Syn.shift s
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianNamedDampingPowerChart.source F G (sh x) (sh y) (sh C₀) (sh C)
      (sh R₀) (sh R) (sh E) (sh T) (sh a) (sh b) := by simpa only [Fm.shift,Syn.shift,GaussianNamedDampingPowerChart.subst_source,sh] using h.shift
  let c := GaussianNamedDampingPowerChart.data F G (sh x) (sh y) (sh a) (sh b)
  let M := GaussianNamedDampingPowerChart.majorant (sh C) (sh R) (sh E) (sh T)
  have orig := chart_disk F G (sh x) (sh y) (sh C₀) (sh C) (sh R₀) (sh R) (sh E) (sh T) (sh a) (sh b) hs
  have neg := GaussianExponentialInverse.negative_input (chartF F G) M c orig
  have bound : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 (decayF (chartF F G)) (var 0) (decayData (chartF F G) c))
      (decayBound (sh C) (sh R) (sh E) (sh T)) one :=
    GaussianEulerExponentialNamedKernelRate.inner_observation_bound (negativeF (chartF F G)) (var 0) M (negativeData c) neg
  refine .allI ?_
  simpa [sampleBound,decayBound,GaussianNamedDampingPowerChart.majorant,Syn.shift,sh,c] using bound

theorem original_observation_bound (F G : PR 2) (p z Rz B x y C₀ C R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R E T a b) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF F G) p (data F G z B x y a b)) (majorant Rz C R E T) one :=
  product_observation_bound powerF (decayF (chartF F G)) p (powerData z B a b) _ _ _
    (GaussianEulerDampedTimeRate.power_sample_bound z Rz B E T a b h.andE₁ h.andE₂.andE₂.andE₂.andE₂)
    (decay_samples F G x y C₀ C R₀ R E T a b h.andE₂)

theorem original_rate (F G F' G' : PR 2) (z Rz B x y u v C₀ C R₀ R E T a b a' b' A₀ A₁ A₂ D : PTm n)
    (h : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R E T a b)
    (h' : Γ ⊢[PRAAx] source F' G' z Rz B u v C₀ C R₀ R E T a' b')
    (hD : Γ ⊢[PRAAx] le one D)
    (h₀ : Γ ⊢[PRAAx] independentRate F F' x u A₀ D)
    (h₁ : Γ ⊢[PRAAx] independentRate G G' y v A₁ D)
    (h₂ : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction a' b') A₂ D) :
    Γ ⊢[PRAAx] independentRate (nameF F G) (nameF F' G') (data F G z B x y a b) (data F' G' z B u v a' b')
      (gain Rz C R E T A₀ A₁ A₂) D := by
  let c := GaussianNamedDampingPowerChart.data F G x y a b
  let c' := GaussianNamedDampingPowerChart.data F' G' u v a' b'
  let t := powerData z B a b
  let t' := powerData z B a' b'
  let M := GaussianNamedDampingPowerChart.majorant C R E T
  let A := GaussianNamedDampingPowerChart.gain C R E T A₀ A₁ A₂
  let F₀ := chartF F G
  let F₁ := chartF F' G'
  have l := chart_disk F G x y C₀ C R₀ R E T a b h.andE₂
  have r := chart_disk F' G' u v C₀ C R₀ R E T a' b' h'.andE₂
  have chartRate := GaussianNamedDampingPowerChart.original_rate F G F' G' x y u v C₀ C R₀ R E T a b a' b'
    A₀ A₁ A₂ D h.andE₂ h'.andE₂ hD h₀ h₁ h₂
  have neg := GaussianEulerPowerScalingCompactRate.negative_rate F₀ F₁ c c' A D l.andE₁ r.andE₁ hD chartRate
  have decay := GaussianEulerExponentialNamedKernelRate.inner_rate (negativeF F₀) (negativeF F₁) M
    (negativeData c) (negativeData c') A D (GaussianExponentialInverse.negative_input F₀ M c l)
    (GaussianExponentialInverse.negative_input F₁ M c' r) hD neg
  have lt := h.andE₂.andE₂.andE₂.andE₂
  have rt := h'.andE₂.andE₂.andE₂.andE₂
  have power := GaussianEulerCompactPowerVariation.original_power_rate z Rz B E T a b a' b' A₂ D
    (.andI h.andE₁ (.andI lt (.andI rt (.andI hD h₂))))
  exact product_same_denominator powerF (decayF F₀) powerF (decayF F₁) t (decayData F₀ c) t' (decayData F₁ c')
    _ _ D _ _ hD
    (GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁ lt.andE₁))
    (GaussianEulerDampedNamedIntegrand.decay_regular F₀ c l.andE₁)
    (GaussianEulerIntegrandName.power_regular z B a' b' (.andI h.andE₁.andE₁ rt.andE₁))
    (GaussianEulerDampedNamedIntegrand.decay_regular F₁ c' r.andE₁)
    (decay_samples F G x y C₀ C R₀ R E T a b h.andE₂)
    (GaussianEulerDampedTimeRate.power_sample_bound z Rz B E T a' b' h'.andE₁ rt) power decay

theorem actual_rational_specialization (z B e f d h Q S E T a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF constantF) GaussianEulerPowerScalingCompactRate.nameF
      (data constantF constantF z B (fraction d h) (fraction e f) a b)
      (GaussianEulerPowerScalingCompactRate.data z B e f d h S a b) := by
  let F := chartF constantF constantF
  let G := GaussianEulerPositivePowerChart.nameF
  let x := GaussianNamedDampingPowerChart.data constantF constantF (fraction d h) (fraction e f) a b
  let y := GaussianEulerPositivePowerChart.data e f d h S a b
  let t := powerData z B a b
  have cross := GaussianNamedDampingPowerRational.actual_rational_chart e f d h Q S E T a b hs
  have hr := GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs
  have hl : Γ ⊢[PRAAx] pointCN F x := GaussianNameEquivalence.cross_trans F G F x y x cross
    (GaussianNameEquivalence.cross_symm _ _ _ _ cross)
  have neg := GaussianNameRingLaws.negative_equivalent F G x y hl hr (cross_to_diagonal _ _ _ _ cross)
  let i := GaussianGammaFiniteApproximantName.exponential_input (negativeF F) (negativeData x) (negative_fast _ _ hl)
  let j := GaussianGammaFiniteApproximantName.exponential_input (negativeF G) (negativeData y) (negative_fast _ _ hr)
  have d := GaussianExponentialRadiusIndependence.independent_radii_proper (negativeF F) (negativeF G) _ _
    (negativeData x) (negativeData y) i j neg
  have p := GaussianEulerIntegrandName.power_regular z B a b (.andI hB hs.andE₂.andE₂.andE₁)
  exact GaussianGammaAdjacentCutoff.multiply_cross powerF powerF (decayF F) (decayF G) t t (decayData F x) (decayData G y)
    p p (GaussianEulerDampedNamedIntegrand.decay_regular F x hl) (GaussianEulerDampedNamedIntegrand.decay_regular G y hr)
    (cross_refl _ _ p) d

theorem actual_named_damped_Euler_kernel_rational_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    ((le one (var 1) ⋏ GaussianEulerPositivePowerChart.source (var 2) (var 3) (var 4) (var 5) (var 6)
      (var 7) (var 8) (var 9) (var 10) (var 11)) ⟶
      crossEquivalent (nameF constantF constantF) GaussianEulerPowerScalingCompactRate.nameF
        (data constantF constantF (var 0) (var 1) (fraction (var 4) (var 5)) (fraction (var 2) (var 3)) (var 10) (var 11))
        (GaussianEulerPowerScalingCompactRate.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 10) (var 11))) :=
  closeUniv 12 (.impI (actual_rational_specialization _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerIntegrand
