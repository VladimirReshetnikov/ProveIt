import IPRADerivations.Analysis.Euler.GaussianEulerCompactModulus
import IPRADerivations.Analysis.Euler.GaussianEulerCompactPowerMajorant

/-!
# Uniform compact time variation of the original Euler power observations

The original powerExponent multiplication clocks and original powerF
exponential samples are retained. The proved original logarithm rate
and one computed compact radius give an independent-observation rate
for the actual power, with the two ordinary observation errors. No
power-name output or time-variation identity is supplied as a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactPowerVariation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerExponentCompactBounds (source input)
open GaussianCompactLogarithmBounds (domain)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerClock coefficient)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def radius (R E T : PTm n) : PTm n := GaussianEulerCompactPowerMajorant.exponentRadius R E T
def factor (R E : PTm n) : PTm n := (R+one)*E
def lipschitz (R E T : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (radius R E T)*factor R E
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (radius R E T) = radius (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [radius,GaussianEulerCompactPowerMajorant.exponentRadius]
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (R E : PTm n) :
    Syn.subst σ (factor R E) = factor (Syn.subst σ R) (Syn.subst σ E) := by simp [factor]
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (lipschitz R E T) = lipschitz (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [lipschitz]

theorem clock_later (p z B a b : PTm n) : Γ ⊢[PRAAx] le p (powerClock p z B a b) := le_add_right _ _

theorem exponent_bound (p z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 powerExponentF p (powerExponentData z B a b)) (radius R E T) one := by
  have prod := GaussianRationalReciprocal.bounded_product _ _ (R+one) one (GaussianCompactLogarithmBounds.radius E T) one
    (le_refl one) (le_refl one) (GaussianEulerIntegrandName.coefficient_bound z R B hz.andE₁ hz.andE₂.andE₂)
    (GaussianCompactLogarithmBounds.sample_bound (powerClock p z B a b) a b E T hz.andE₂.andE₁ ht)
  exact GaussianRationalReciprocal.bound_congr (GaussianEulerIntegrandName.power_exponent_at p z B a b).eqSymm
    (.eqRefl _) (by ipra_ring) prod

private theorem logarithm_distance (p z B a b c d E A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] independentRate GaussianPositiveRationalLogarithm.logF GaussianPositiveRationalLogarithm.logF
      (GaussianPositiveRationalLogarithm.data a b) (GaussianPositiveRationalLogarithm.data c d) (E*A) D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.sample (powerClock p z B a b) a b)
      (GaussianPositiveRationalLogarithm.sample (powerClock p z B c d) c d) ((E*A)*unit p+two*D) (D*unit p) := by
  let s := powerClock p z B a b
  let t := powerClock p z B c d
  have old := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ s t h
  have gs : Γ ⊢[PRAAx] le (unit p) (unit s) := GaussianExponentialReference.unit_monotone (clock_later p z B a b)
  have gt : Γ ⊢[PRAAx] le (unit p) (unit t) := GaussianExponentialReference.unit_monotone (clock_later p z B c d)
  apply distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive D s t hD) (positive_product _ _ hD (unit_positive p)) _ old
  unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
  ipra_le (𝔞 D*𝔞 D*𝔞(unit t))*sl gs+(𝔞 D*𝔞 D*𝔞(unit s))*sl gt

theorem exponent_diagonal (p z R B E T a b c d A D : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B E) (ha : Γ ⊢[PRAAx] domain a b E T) (hc : Γ ⊢[PRAAx] domain c d E T)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] distanceBounded (GaussianPositiveRationalLogarithm.fraction a b) (GaussianPositiveRationalLogarithm.fraction c d) A D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 powerExponentF p (powerExponentData z B a b)) (ap2 powerExponentF p (powerExponentData z B c d))
      ((factor R E*A)*unit p+(two*(R+one))*D) (D*unit p) := by
  have logs := logarithm_distance p z B a b c d E A D hD
    (GaussianCompactLogarithmBounds.original_log_rate a b c d E A D ha.andE₁ hc.andE₁ hD ha.andE₂.andE₁ hc.andE₂.andE₁ hd)
  have multiplied := GaussianNameRingLaws.product_right_error (coefficient z B) _ _ _ _ (GaussianCompactLogarithmBounds.radius E T) (R+one)
    (positive_product _ _ hD (unit_positive p)) logs (GaussianCompactLogarithmBounds.sample_bound _ a b E T hz.andE₂.andE₁ ha)
    (GaussianEulerIntegrandName.coefficient_bound z R B hz.andE₁ hz.andE₂.andE₂)
  exact distance_congr (GaussianEulerIntegrandName.power_exponent_at p z B a b).eqSymm
    (GaussianEulerIntegrandName.power_exponent_at p z B c d).eqSymm (by unfold factor; ipra_ring) (.eqRefl _) multiplied

private theorem exponent_envelope (z R B E T a b c d A D : PTm n) (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope powerExponentF powerExponentF (powerExponentData z B a b) (powerExponentData z B c d)
      (factor R E*A) D (two*(R+one)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianEulerIntegrandName.subst_powerExponentData,
    PTm.subst_mul,PTm.subst_add,subst_factor,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    exponent_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift A) (Syn.shift D)
      hs.andE₁ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂

theorem exponent_rate (z R B E T a b c d A D : PTm n) (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    independentRate powerExponentF powerExponentF (powerExponentData z B a b) (powerExponentData z B c d) (factor R E*A) D :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ h.andE₂.andE₂.andE₂.andE₁
    (GaussianEulerIntegrandName.power_exponent_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁))
    (GaussianEulerIntegrandName.power_exponent_regular z B c d (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)) (exponent_envelope z R B E T a b c d A D h)

theorem common_input (z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input powerExponentF (radius R E T) (powerExponentData z B a b) := by
  refine .andI (GaussianEulerIntegrandName.power_exponent_regular z B a b (.andI hz.andE₁ ht.andE₁)) (.allI ?_)
  have zs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hz.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerIntegrandName.subst_powerExponentData,subst_radius,Syn.shift] using
    exponent_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) zs ts

/-- The actual original powerF/data retain both independent observation
precisions and their original, separately computed exponential radii. -/
theorem original_power_rate (z R B E T a b c d A D : PTm n) (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    independentRate powerF powerF (powerData z B a b) (powerData z B c d) (lipschitz R E T*A) D := by
  let M := radius R E T
  let H := factor R E
  have ca := common_input z R B E T a b h.andE₁ h.andE₂.andE₁
  have cc := common_input z R B E T c d h.andE₁ h.andE₂.andE₂.andE₁
  have origA := GaussianEulerIntegrandName.power_input z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁)
  have origC := GaussianEulerIntegrandName.power_input z B c d (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate powerExponentF powerExponentF M
    (powerExponentData z B a b) (powerExponentData z B c d) (H*A) D
    (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI ca (.andI cc (exponent_rate z R B E T a b c d A D h))))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper powerExponentF powerExponentF
    (GaussianEulerIntegrandName.powerRadius z B a b) M (powerExponentData z B a b) (powerExponentData z B a b) origA ca
    (GaussianNameEquivalence.cross_refl _ _ origA.andE₁)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper powerExponentF powerExponentF
    (GaussianEulerIntegrandName.powerRadius z B c d) M (powerExponentData z B c d) (powerExponentData z B c d) origC cc
    (GaussianNameEquivalence.cross_refl _ _ origC.andE₁)
  have moved := GaussianNamedRateTransport.transport (GaussianRadiusExponentialName.nameF powerExponentF) (GaussianRadiusExponentialName.nameF powerExponentF)
    powerF powerF (GaussianRadiusExponentialName.data M (powerExponentData z B a b)) (GaussianRadiusExponentialName.data M (powerExponentData z B c d))
    (powerData z B a b) (powerData z B c d) (GaussianRadiusExponentialLipschitzRate.factor M*(H*A)) D h.andE₂.andE₂.andE₂.andE₁ common left right
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by unfold lipschitz M H; ipra_ring) moved

theorem original_compact_power_exponent_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ domain (var 6) (var 7) (var 4) (var 5)) ⟶
      bounded (ap2 powerExponentF (var 0) (powerExponentData (var 1) (var 3) (var 6) (var 7))) (radius (var 2) (var 4) (var 5)) one) :=
  closeUniv 8 (.impI (exponent_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_compact_power_independent_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      independentRate powerF powerF (powerData (var 0) (var 2) (var 5) (var 6)) (powerData (var 0) (var 2) (var 7) (var 8))
        (lipschitz (var 1) (var 3) (var 4)*var 9) (var 10)) :=
  closeUniv 11 (.impI (original_power_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactPowerVariation
