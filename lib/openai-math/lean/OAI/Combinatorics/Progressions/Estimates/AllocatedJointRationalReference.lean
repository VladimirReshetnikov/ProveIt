import OAI.Combinatorics.Progressions.Geometry.UniformSumCoordinates
import OAI.Combinatorics.Progressions.Lattices.AllocatedActualCRTRationalMarginal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

private theorem uniform_sum_elim_flip_decidable
    {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype R] [Nonempty R] (f : ((A ⊕ B) → R) → ℂ) :
    (FiniteProbabilityWeights.uniform (B → R)).complexMean (fun b =>
      (FiniteProbabilityWeights.uniform (A → R)).complexMean (fun a => f (Sum.elim a b))) =
      (FiniteProbabilityWeights.uniform ((A ⊕ B) → R)).complexMean f := by
  simp only [FiniteProbabilityWeights.uniform_complexMean]
  calc
    _ = 𝔼 a : A → R, 𝔼 b : B → R, f (Sum.elim a b) := Finset.expect_comm _ _ _
    _ = 𝔼 p : (A → R) × (B → R), f (Sum.elim p.1 p.2) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (A → R))
          (Finset.univ : Finset (B → R)) (fun a b => f (Sum.elim a b))).symm
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi (fun _ : A ⊕ B => R)).symm
      intro p
      rfl

private theorem retained_uniform_sum_elim_flip
    {K A B R Ω : Type*} [Fintype K] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Fintype R] [Nonempty R] [Fintype Ω]
    (s : FiniteProbabilityWeights K) (p : FiniteProbabilityWeights Ω)
    (f : K → Ω → ((A ⊕ B) → R) → ℂ) :
    s.complexMean (fun k =>
      (FiniteProbabilityWeights.uniform (B → R)).complexMean (fun b =>
        (FiniteProbabilityWeights.uniform (A → R)).complexMean (fun a =>
          p.complexMean (fun ω => f k ω (Sum.elim a b))))) =
      p.complexMean (fun ω => s.complexMean (fun k =>
        (FiniteProbabilityWeights.uniform ((A ⊕ B) → R)).complexMean (f k ω))) := by
  calc
    _ = s.complexMean (fun k => p.complexMean (fun ω =>
        (FiniteProbabilityWeights.uniform (B → R)).complexMean (fun b =>
          (FiniteProbabilityWeights.uniform (A → R)).complexMean (fun a =>
            f k ω (Sum.elim a b))))) := by
      simp only [FiniteProbabilityWeights.uniform_complexMean]
      simp_rw [← p.complexMean_average]
    _ = s.complexMean (fun k => p.complexMean (fun ω =>
        (FiniteProbabilityWeights.uniform ((A ⊕ B) → R)).complexMean (f k ω))) := by
      simp_rw [uniform_sum_elim_flip_decidable]
    _ = _ := FiniteProbabilityWeights.complexMean_commute s p _

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
local notation "Active" => PrincipalTupleIndex
  (fun a : {a // ¬short a} => B (Subtype.val a))
  (fun a : {a // ¬short a} => layerSamplerDegree I n (Subtype.val a))
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "law" => principalTupleWeights (α := Empty) B degree sides hSides

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance jointCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

theorem allocatedJoint_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
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
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (x : Ω → G → IntegerScalarCubeBox Empty S.value)
    (test : Ω → (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Active → ZMod q)).complexMean (fun ar =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          p.complexMean (fun ω =>
            test ω (forecastInactiveShortGrid B U basis S selected c u)
              (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
                (Sum.elim (Sum.elim rG ar)
                  (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
                (poly o)))))) =
      p.complexMean (fun ω => ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (law)
          (fun _ => crtPolynomialInputLaw primes exponent (fun _ => 0) hcoprime origin)
          (forecastInactiveFixedOutput B U basis S selected c (x ω))
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test ω z (fun j => ZMod.castHom hq (ZMod q) (b j))) := by
  intro poly
  have hcollapse := retained_uniform_sum_elim_flip
    (K := ShortTuple) (A := G) (B := Active) (R := ZMod q) (Ω := Ω)
    (allocatedUnconditionalShortPrincipalLaw B U basis S) p
    (fun u ω (t : Long → ZMod q) =>
      test ω (forecastInactiveShortGrid B U basis S selected c u)
        (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim t (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
          (poly o)))
  rw [hcollapse]
  apply congrArg p.complexMean
  funext ω
  simp only [FiniteProbabilityWeights.uniform_complexMean]
  have hactual :=
    allocatedActual_crtRationalForecast_tsum_marginal
      (G := G) (X := X) (I := I) (E := E) (n := n) (J := J)
      (R := R) (σ := σ) (PrimeIndex := PrimeIndex) (A := A) (q := q)
      (gridVolume := gridVolume) B U basis S primes exponent
      hR hσ selected hsmall c hc (x ω) base noise deck projection hp hinj hcoprime origin
      hq hV (test ω)
  erw [hactual]
  apply congrArg (allocatedUnconditionalShortPrincipalLaw B U basis S).complexMean
  funext u
  apply Finset.expect_congr
  · ext t
    simp only [Finset.mem_univ]
  · intro t _
    rfl

end Erdos3.VectorPolynomial

end

end OAI
