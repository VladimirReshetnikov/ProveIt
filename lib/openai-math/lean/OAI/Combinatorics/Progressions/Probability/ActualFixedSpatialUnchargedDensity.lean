import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
import OAI.Combinatorics.Progressions.Lattices.CRTInactiveDensityGoodPrimeDeletion

namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def localReferencePolynomial
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (j : Fin m) : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j →
      MvPolynomial (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B) ℤ :=
  allocatedCongruenceIntegerPolynomial (allocatedShortAxis (I := I) U b S.value) j
    path.base path.noise (allocatedReadDeck path.read)
    (fun a => allocatedReadProjection path.read ⟨j, a.val⟩)
    (samplerFrozenRaw (layerSamplerDegree I n) raw)

noncomputable def referenceBadDepth (p : ℕ) : ℕ := by
  letI := path.primeNeZero
  exact allocatedCongruenceBadDepth (allocatedShortAxis (I := I) U b S.value)
    path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    spatial kernel block path.primes path.exponent
    (modularForecastRankConstant m Dmod : ℝ) p

omit [Fintype Tsp] in

theorem referenceBadDepth_product_le :
    (∏ p : path.primes, p.val ^ path.referenceBadDepth p.val) ≤ path.Rbad := by
  exact path.hbad

omit [Fintype Tsp] in
theorem localReference_degree
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j) :
    (path.localReferencePolynomial raw j o).totalDegree ≤ j.val + 1 :=
  allocatedCongruenceIntegerPolynomial_degree (allocatedShortAxis (I := I) U b S.value)
    j path.base path.noise (allocatedReadDeck path.read)
    (fun a => allocatedReadProjection path.read ⟨j, a.val⟩)
    (samplerFrozenRaw (layerSamplerDegree I n) raw) o

omit [Fintype Tsp] in

theorem localReference_rank
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (a : ℕ) (ha : path.referenceBadDepth p.val < a)
    (hA : a ≤ path.exponent p.val) (j : Fin m)
    (row : AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value) j → ZMod (p.val ^ a))
    (hunit : ∃ o, IsUnit (row o)) :
    letI := path.primeNeZero
    integerPolynomialRankProbability p.val a j.val
      (path.localReferencePolynomial raw j) row ≤
      (p.val : ℝ) ^ (-(modularForecastRankConstant m Dmod : ℝ) * a) := by
  let := path.primeNeZero
  exact allocatedCongruenceIntegerPolynomial_rank_of_good
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    spatial kernel block path.primes (modularForecastRankConstant m Dmod : ℝ) p a
    (allocatedCongruence_largest_bad_depth_good
      (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
      (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
      spatial kernel block path.primes path.exponent
      (modularForecastRankConstant m Dmod : ℝ) p a ha hA)
    path.base (samplerFrozenRaw (layerSamplerDegree I n) raw) j row hunit

omit [Fintype Tsp] in

theorem localReference_integerOutput_eq
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes)
    (x : LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod (p.val ^ path.exponent p.val)) :
    integerLongPolynomialOutput path.referencePolynomial raw (p.val ^ path.exponent p.val)
      (fun v => path.origin p v + (p.val : ZMod (p.val ^ path.exponent p.val)) ^
        path.prescribed p.val * x v) =
    localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
      (path.localReferencePolynomial raw) (path.origin p) x := by
  funext o
  exact allocatedSeparatedCongruencePolynomial_integerLongOutput
    (allocatedShortAxis (I := I) U b S.value) o.1 path.base path.noise
    (allocatedReadDeck path.read) (fun a => allocatedReadProjection path.read ⟨o.1, a.val⟩)
    o.2 raw (p.val ^ path.exponent p.val) _

omit [Fintype Tsp] in

theorem localReference_uncharged_density
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (p : path.primes) (hbad : path.referenceBadDepth p.val = 0)
    (hpres : path.prescribed p.val = 0)
    (z : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod (p.val ^ path.exponent p.val)) :
    letI := path.primeNeZero
    let density := rationalOutputDensity
      (FiniteProbabilityWeights.uniform
        (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
          ZMod (p.val ^ path.exponent p.val)))
      (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
        (path.localReferencePolynomial raw) (path.origin p))
      (p.val ^ path.exponent p.val) z
    |density - 1| ≤ 2 / (p.val : ℝ) ^ 2 ∧ density ≤ 1 + 2 / (p.val : ℝ) ^ 2 := by
  let := path.primeNeZero
  have hdim :
      ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X Eout
        (allocatedShortAxis (I := I) U b S.value))) + 2 : ℕ) : ℝ) ≤
      modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) :=
    allocatedCongruenceForecastRankConstant_dimension
      (allocatedShortAxis (I := I) U b S.value) hm Dmod hD
  have hrank (a : ℕ) (ha : 0 < a) (hA : a ≤ path.exponent p.val) (j : Fin m)
      (row : AllocatedCongruenceRankOutput X Eout
        (allocatedShortAxis (I := I) U b S.value) j → ZMod (p.val ^ a))
      (hunit : ∃ o, IsUnit (row o)) :
      integerPolynomialRankProbability p.val a j.val (path.localReferencePolynomial raw j) row ≤
        (p.val : ℝ) ^ (-(modularForecastRankConstant m Dmod : ℝ) * a) :=
    path.localReference_rank raw p a (by simpa only [hbad] using ha) hA j row hunit
  have hdensity := localPrimePowerIntegerPolynomialOutput_uncharged_density hm p.val
    (path.exponent p.val) (path.prime p.val p.property)
    (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) hdim
    (path.localReferencePolynomial raw) (path.localReference_degree raw) hrank (path.origin p) z
  simpa only [hpres, rationalOutputDensity, ← Nat.card_eq_fintype_card] using hdensity

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
