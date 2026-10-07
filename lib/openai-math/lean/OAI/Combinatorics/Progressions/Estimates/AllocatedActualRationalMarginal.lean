import OAI.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
import OAI.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "law" => principalTupleWeights (α := Empty) B degree sides hSides

theorem allocatedShort_rationalForecast_tsum_marginal
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    {Z : Type*} (grid : ShortTuple → Z)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    (∑' z, 𝔼 b : Out → ZMod N,
      ((rationalInactiveForecast (law)
        (fun _ => FiniteProbabilityWeights.uniform (Long → ZMod N))
        (fun v => grid (principalAxisRestrict short v))
        (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
        N gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        𝔼 t : Long → ZMod q,
          test (grid u) (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim t (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
            (poly o))) := by
  classical
  intro poly
  rw [rationalInactivePolynomialForecast_tsum_marginal (law)
    (fun v => grid (principalAxisRestrict short v)) poly
    (fun v k => (v k.1 k.2 : ℤ)) hq hV test]
  have he (v : PrincipalIntegerTuples B degree Empty sides) (t : Long → ZMod q) :
      (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim t (fun k => ((v k.1 k.2 : ℤ) : ZMod q))) (poly o)) =
      (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim t (fun k => (allocatedShortPrincipalRaw B U basis S
          (principalAxisRestrict short v) k : ZMod q))) (poly o)) := by
    funext o
    exact allocatedForecastPolynomial_short_raw B U basis S base noise deck projection q t v o
  simp_rw [he]
  rw [principalTupleWeights_partition short sides hSides]
  simp only [principalAxisRestrict_join_left, FiniteProbabilityWeights.complexMean_const]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "hSides" => allocatedPrincipalSides_pos B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "law" => principalTupleWeights (α := Empty) B degree sides hSides

theorem allocatedActual_rationalForecast_tsum_marginal
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    (∑' z, 𝔼 b : Out → ZMod N,
      ((rationalInactiveForecast (law)
        (fun _ => FiniteProbabilityWeights.uniform (Long → ZMod N))
        (forecastInactiveFixedOutput B U basis S selected c x)
        (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
        N gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
        𝔼 t : Long → ZMod q,
          test (forecastInactiveShortGrid B U basis S selected c u)
            (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
              (Sum.elim t (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
              (poly o))) := by
  intro poly
  rw [forecastInactiveFixedOutput_eq_shortGrid_comp B U basis S hR hσ selected hsmall c hc x]
  exact allocatedShort_rationalForecast_tsum_marginal B U basis S base noise deck projection
    (forecastInactiveShortGrid B U basis S selected c) hq hV test

end Erdos3.VectorPolynomial

end

end OAI
