import OAI.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
import OAI.Combinatorics.Progressions.Polynomial.ActualFixedSpatialPhysicalPolynomialRange
import OAI.Combinatorics.Progressions.Sampling.ActualSlicedForecastLateData
import OAI.Combinatorics.Progressions.Sampling.ForecastLawPhysicalTargetReal

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

noncomputable def referenceModulus : ℕ := ∏ p : path.primes, p.val ^ path.exponent p.val

omit [Fintype Tsp] in
theorem referenceModulus_pos : 0 < path.referenceModulus := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (path.prime p.val p.property).pos _

local instance actualPathReferenceNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

noncomputable def referencePolynomial :=
  allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value) path.base path.noise
    (allocatedReadDeck path.read) (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩)

noncomputable def referenceInputLaw : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod path.referenceModulus) := by
  letI := path.primeNeZero
  exact crtPolynomialInputLaw (fun p : path.primes => p.val)
    (fun p : path.primes => path.exponent p.val) (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective) path.origin

omit [Fintype Tsp] in
theorem reference_characteristic_decay (hm : 0 < m)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (χ : AddChar (Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) ℂ) :
    ‖finiteImageCharacteristic path.referenceInputLaw
      (fun t j => (integerLongPolynomialOutput path.referencePolynomial
        (fun k => (y k.1 k.2 : ℤ)) path.referenceModulus t j : ZMod path.referenceModulus)) χ‖ ≤
      ((path.Rbad * ∏ p : path.primes, p.val ^ path.prescribed p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
          modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ)) := by
  let _ := path.primeNeZero
  exact allocatedForecastPolynomial_crt_decay_of_bad_product
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j,a.val⟩) spatial kernel block
    hm path.primes path.exponent path.prescribed path.prime
    (modularForecastRankConstant m Dmod : ℝ) (Nat.cast_nonneg _) path.Rbad path.hbad
    path.base path.origin (fun k => (y k.1 k.2 : ℤ)) χ

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem boundedPrimes_log_prime_power_le_slicedTargetReal (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p ^ Nat.log p Q ≤ Q := by
  intro p hp
  exact boundedPrimePower_le Q ⟨p, hp⟩

theorem boundedPrimes_prime_slicedTargetReal (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p.Prime := by
  intro p hp
  exact ((mem_boundedPrimes Q p).mp hp).1

namespace VectorPolynomial

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceModulus_eq_boundedPrimeProduct_slicedTargetReal (Q : ℕ)
    (hprimes : path.primes = boundedPrimes Q)
    (hexponent : path.exponent = fun p => Nat.log p Q) :
    path.referenceModulus = boundedPrimeProduct Q := by
  unfold referenceModulus
  rw [hexponent, hprimes]
  rfl

omit [Fintype Tsp] in

theorem dvd_referenceModulus_of_le_bound_slicedTargetReal (Q : ℕ)
    (hprimes : path.primes = boundedPrimes Q)
    (hexponent : path.exponent = fun p => Nat.log p Q)
    {q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    q ∣ path.referenceModulus := by
  rw [path.referenceModulus_eq_boundedPrimeProduct_slicedTargetReal Q hprimes hexponent]
  exact boundedPrimeProduct_captures hq hqQ

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

theorem boundedPrimes_log_prime_power_le (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p ^ Nat.log p Q ≤ Q := by
  intro p hp
  exact boundedPrimePower_le Q ⟨p, hp⟩

theorem boundedPrimes_prime (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p.Prime := by
  intro p hp
  exact ((mem_boundedPrimes Q p).mp hp).1

namespace VectorPolynomial

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
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceModulus_eq_boundedPrimeProduct (Q : ℕ)
    (hprimes : path.primes = boundedPrimes Q)
    (hexponent : path.exponent = fun p => Nat.log p Q) :
    path.referenceModulus = boundedPrimeProduct Q := by
  unfold referenceModulus
  rw [hexponent, hprimes]
  rfl

omit [Fintype Tsp] in

theorem dvd_referenceModulus_of_le_bound (Q : ℕ)
    (hprimes : path.primes = boundedPrimes Q)
    (hexponent : path.exponent = fun p => Nat.log p Q)
    {q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    q ∣ path.referenceModulus := by
  rw [path.referenceModulus_eq_boundedPrimeProduct Q hprimes hexponent]
  exact boundedPrimeProduct_captures hq hqQ

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def rawTarget (κ : ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ) : ℂ := by
  letI : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  exact (κ : ℂ) * forecastLawDensityPhysicalTarget B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceInputLaw)
    (fun y t j => integerLongPolynomialOutput slice.path.referencePolynomial
      (fun k => (y k.1 k.2 : ℤ)) slice.path.referenceModulus t j)
    slice.path.referenceModulus (∏ a, (basisAxisScale (b (selected a).1) (selected a).2 : ℝ))
    slice.path.base physicalN τ o hb bW poly hm u

theorem targetAt_eq_rawTarget
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j) (κ : ℝ) (u : X → ℤ) :
    slice.targetAt selected hB o bW hb poly hm κ u =
      slice.rawTarget selected hB o bW hb κ (slice.path.physicalPolynomial poly)
        (slice.path.physicalPolynomial_mem poly hm) u := by
  rfl

theorem rawTarget_universal_approx
    {Findex : Type} [Fintype Findex] {period cover : ℝ} {L : ℝ≥0}
    (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) period cover L)
    (c : Findex → ℂ) (κ δ : ℝ)
    (h : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.targetAt selected hB o bW hb poly hm κ u -
        ∑ i, c i * (F i).eval physicalN (slice.path.physicalPolynomial poly) u‖ ≤ δ) :
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.rawTarget selected hB o bW hb κ poly hm u -
        ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ := by
  apply slice.path.forall_physicalPolynomial_of_universal
    (fun poly hm => ∀ u, ‖slice.rawTarget selected hB o bW hb κ poly hm u -
      ∑ i, c i * (F i).eval physicalN poly u‖ ≤ δ)
  intro poly hm u
  simpa only [slice.targetAt_eq_rawTarget selected hB o bW hb poly hm κ u] using h poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

theorem rawTarget_actualForecastData_approx
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {Pnative massLog capLog E : ℝ}
    (data : ActualForecastData physicalN originalpoly Pnative massLog capLog E)
    (hc : data.centerConstant = fun j => (slice.path.center j).val)
    (κ : ℝ)
    (h : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.targetAt selected hB o bW hb poly hm κ u -
        ∑ i, data.coefficient i * (data.twists i).eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-E)) :
    ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
      ‖slice.rawTarget selected hB o bW hb κ poly hm u -
        ∑ i, data.coefficient i * (data.twists i).eval physicalN poly u‖ ≤ Real.exp (-E) := by
  apply slice.rawTarget_universal_approx selected hB o bW hb data.twists data.coefficient
    κ (Real.exp (-E))
  intro poly hm u
  change ‖slice.targetAt selected hB o bW hb poly hm κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (slice.path.center j).val (poly j)) u‖ ≤ Real.exp (-E)
  simpa only [hc] using h poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable (κ : ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem rawTarget_real (u : X → ℤ) :
    ((slice.rawTarget selected hB o bW hb κ poly hm u).re : ℂ) =
      slice.rawTarget selected hB o bW hb κ poly hm u := by
  let : NeZero slice.path.referenceModulus := ⟨slice.path.referenceModulus_pos.ne'⟩
  unfold rawTarget
  apply forecastLawDensityPhysicalTarget_scaled_real

theorem rawTarget_star (u : X → ℤ) :
    star (slice.rawTarget selected hB o bW hb κ poly hm u) =
      slice.rawTarget selected hB o bW hb κ poly hm u := by
  rw [← slice.rawTarget_real selected hB o bW hb κ poly hm u]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem targetAt_real (u : X → ℤ) :
    ((slice.targetAt selected hB o bW hb poly hm κ u).re : ℂ) =
      slice.targetAt selected hB o bW hb poly hm κ u := by
  rw [slice.targetAt_eq_rawTarget selected hB o bW hb poly hm κ u]
  exact slice.rawTarget_real selected hB o bW hb κ _ _ u

theorem targetAt_star (u : X → ℤ) :
    star (slice.targetAt selected hB o bW hb poly hm κ u) =
      slice.targetAt selected hB o bW hb poly hm κ u := by
  rw [← slice.targetAt_real selected hB o bW hb κ poly hm u]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem target_real (u : integerBox physicalN) :
    ((slice.target selected hB o bW hb poly hm κ u).re : ℂ) =
      slice.target selected hB o bW hb poly hm κ u := by
  exact slice.targetAt_real selected hB o bW hb κ poly hm u.val

theorem target_star (u : integerBox physicalN) :
    star (slice.target selected hB o bW hb poly hm κ u) =
      slice.target selected hB o bW hb poly hm κ u := by
  exact slice.targetAt_star selected hB o bW hb κ poly hm u.val

variable {Pnative massLog capLog E : ℝ}
variable (data : ActualForecastData physicalN poly Pnative massLog capLog E)
variable (htarget : data.target = slice.target selected hB o bW hb poly hm κ)

include htarget in
theorem actualForecastData_target_real (u : integerBox physicalN) :
    ((data.target u).re : ℂ) = data.target u := by
  rw [htarget]
  exact slice.target_real selected hB o bW hb κ poly hm u

include htarget in
theorem actualForecastData_target_star (u : integerBox physicalN) :
    star (data.target u) = data.target u := by
  rw [htarget]
  exact slice.target_star selected hB o bW hb κ poly hm u

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
