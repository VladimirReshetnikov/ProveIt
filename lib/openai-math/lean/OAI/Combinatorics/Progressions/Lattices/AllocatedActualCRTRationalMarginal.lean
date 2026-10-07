import OAI.Combinatorics.Progressions.Estimates.AllocatedActualRationalMarginal

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

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance actualCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

theorem allocatedActual_crtRationalForecast_tsum_marginal
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
    (hp : ∀ l, (primes l).Prime) (hinj : Function.Injective primes)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    (origin : ∀ l, Long → ZMod (primes l ^ exponent l))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    (∑' z, 𝔼 b : Out → ZMod N,
      ((rationalInactiveForecast (law)
        (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
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
  have hcrt := rationalInactivePolynomialForecast_unrestrictedCRT_tsum_marginal (law)
    (forecastInactiveFixedOutput B U basis S selected c x) primes exponent hp hinj hcoprime origin
    poly (fun v k => (v k.1 k.2 : ℤ)) hq hV test
  have huniform := rationalInactivePolynomialForecast_tsum_marginal (law)
    (forecastInactiveFixedOutput B U basis S selected c x) poly
    (fun v k => (v k.1 k.2 : ℤ)) hq hV test
  exact hcrt.trans (huniform.symm.trans
    (allocatedActual_rationalForecast_tsum_marginal B U basis S hR hσ selected hsmall c hc x
      base noise deck projection hq hV test))

end Erdos3.VectorPolynomial

end

end OAI
