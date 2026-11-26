import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialPowerTerm
import IPRADerivations.Analysis.Logarithm.GaussianUpperTimeLogarithmPower
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmPower
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds

/-!
# Factorial majorants for actual logarithmic powers above one

The unchanged original logarithm at a/b>=1 satisfies
|log_p(a/b)^j| <= j! a/b + gain(j,a) 2^-p.
The proof includes the actual j-th exponential term at a later original
harmonic-logarithm query, uses the proved exp(log(a/b))=a/b identity,
and removes only the auxiliary observation error at one finite gap.
The numerical exponent j is unrestricted, including zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogarithmFactorialPowerBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (source fraction)
open GaussianHarmonicLogarithmName (sample)
open GaussianRationalReciprocal (power bound_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianUpperTimeLogarithmPower (gain rawPower)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def radius (a b : PTm n) : PTm n := GaussianHarmonicLogarithmPower.radius a b
def exponentClock (t j : PTm n) : PTm n := t+j
def logClock (t j a b : PTm n) : PTm n := GaussianRadiusExponentialName.inputPrecision (radius a b) (exponentClock t j)
def numerator (p j a b : PTm n) : PTm n := fact j*a*unit p+gain j a*b
def denominator (p b : PTm n) : PTm n := b*unit p
def auxiliaryCost (j a : PTm n) : PTm n := two*fact j+gain j a

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (radius a b) = radius (Syn.subst σ a) (Syn.subst σ b) := by simp [radius]
@[simp] theorem subst_exponentClock {m : ℕ} (σ : Fin n → PTm m) (t j : PTm n) :
    Syn.subst σ (exponentClock t j) = exponentClock (Syn.subst σ t) (Syn.subst σ j) := by simp [exponentClock]
@[simp] theorem subst_logClock {m : ℕ} (σ : Fin n → PTm m) (t j a b : PTm n) :
    Syn.subst σ (logClock t j a b) = logClock (Syn.subst σ t) (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ b) := by simp [logClock]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p j a b : PTm n) :
    Syn.subst σ (numerator p j a b) = numerator (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ b) := by simp [numerator,fact]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p b : PTm n) :
    Syn.subst σ (denominator p b) = denominator (Syn.subst σ p) (Syn.subst σ b) := by simp [denominator]
@[simp] theorem subst_auxiliaryCost {m : ℕ} (σ : Fin n → PTm m) (j a : PTm n) :
    Syn.subst σ (auxiliaryCost j a) = auxiliaryCost (Syn.subst σ j) (Syn.subst σ a) := by simp [auxiliaryCost,fact]

theorem clock_later (t j a b : PTm n) : Γ ⊢[PRAAx] le t (logClock t j a b) :=
  le_trans (le_add_right t j) (le_of_eq_add (d := LeanProofs.IPRA.PTm.num 4+
    (radius a b+two)*GaussianRadiusExponentialName.index (radius a b) (exponentClock t j)) (by unfold logClock GaussianRadiusExponentialName.inputPrecision exponentClock; ipra_ring))

theorem cutoff_includes_degree (t j a b : PTm n) : Γ ⊢[PRAAx]
    le j (GaussianRadiusExponentialName.index (radius a b) (exponentClock t j)) :=
  le_congr (.eqRefl _) (GaussianRadiusExponentialName.index_add (radius a b) t j).eqSymm (le_add_left _ _)

theorem exponential_sample_bound (t a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    bounded (GaussianRadiusExponentialName.sample GaussianHarmonicLogarithmName.nameF (radius a b) t
      (GaussianHarmonicLogarithmName.data a b)) (a*unit t+two*b) (b*unit t) := by
  have cross := GaussianHarmonicLogarithmName.original_exponential_fraction a b b a hs.andE₂
    (GaussianHarmonicLogarithmPower.compact_domain a b hs)
  have actual := GaussianNameEquivalence.cross_at _ _ _ _ t t cross
  have diagonal := distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at t (fraction a b)) (.eqRefl _) (.eqRefl _) actual
  have reduced := distance_radius_mono _ _ _ _ two (unit t)
    (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive t)
    (le_of_eq_add (d := zero) (by ipra_ring)) diagonal
  have exactBound : Γ ⊢[PRAAx] bounded (fraction a b) a b :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hs.andE₂).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded a b hs.andE₂)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ two (unit t) a b (unit_positive t) hs.andE₂ reduced exactBound)

theorem harmonic_cofinal_power_bound (t j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (power (sample (logClock t j a b) a b) j)
      (fact j*(a*unit (exponentClock t j)+two*b)) (b*unit (exponentClock t j)) := by
  have old := exponential_sample_bound (exponentClock t j) a b hs
  have same := GaussianRadiusExponentialName.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF (radius a b)
    (exponentClock t j) (GaussianHarmonicLogarithmName.data a b)
  exact GaussianPositiveExponentialPowerTerm.finite_power_bound _ j _ _ _
    (GaussianPositiveExponentialPowerTerm.harmonic_sample_positive _ a b hba) (cutoff_includes_degree t j a b)
    (positive_product _ _ hs.andE₂ (unit_positive (exponentClock t j)))
    (bound_congr same (.eqRefl _) (.eqRefl _) old)

theorem original_power_slack (p t j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (rawPower p j a b) (numerator p j a b) (denominator p b) (auxiliaryCost j a) t := by
  have near := GaussianUpperTimeLogarithmPower.original_harmonic_power_distance p (logClock t j a b) j a b hs hba
  have late := GaussianExponentialReference.unit_monotone (clock_later (Γ := Γ) t j a b)
  have weakened := distance_radius_mono _ _ _ _ (gain j a*(unit p+unit t)) (unit p*unit t)
    (positive_product _ _ (unit_positive p) (unit_positive (logClock t j a b)))
    (positive_product _ _ (unit_positive p) (unit_positive t))
    (by ipra_le (Groth.ι (Q.mk Γ (gain j a))*Groth.ι (Q.mk Γ (unit p))*Groth.ι (Q.mk Γ (unit p)))*sl late) near
  have rawBound := harmonic_cofinal_power_bound t j a b hs hba
  have grow : Γ ⊢[PRAAx] le (unit t) (unit (exponentClock t j)) :=
    GaussianExponentialReference.unit_monotone (le_add_right t j)
  have major := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _
    (fact j*(a*unit t+two*b)) (b*unit t)
    (positive_product _ _ hs.andE₂ (unit_positive (exponentClock t j))) (positive_product _ _ hs.andE₂ (unit_positive t))
    (by ipra_le (2*𝔞(fact j)*𝔞 b*𝔞 b)*sl grow) rawBound
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive t)) (positive_product _ _ hs.andE₂ (unit_positive t)) weakened major
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive t))
      (positive_product _ _ hs.andE₂ (unit_positive t)))
    (positive_product _ _ (positive_product _ _ hs.andE₂ (unit_positive p)) (unit_positive t)) _ joined
  exact le_of_eq_add (d := zero) (by unfold numerator denominator auxiliaryCost unit; ipra_ring)

/-- Actual original log observations retain only their requested power
amplification. The factorial/time majorant has no auxiliary precision. -/
theorem original_power_bound (p j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (rawPower p j a b) (numerator p j a b) (denominator p b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost j a)
    (positive_product _ _ hs.andE₂ (unit_positive p))
    (original_power_slack p _ j a b hs hba)

theorem actual_original_logarithm_factorial_power_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 2) (var 3) ⋏ le (var 3) (var 2)) ⟶
      bounded (rawPower (var 0) (var 1) (var 2) (var 3))
        (numerator (var 0) (var 1) (var 2) (var 3)) (denominator (var 0) (var 3))) :=
  closeUniv 4 (.impI (original_power_bound _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogarithmFactorialPowerBound
