import OAI.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison

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

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

theorem targetAt_mul_bufferedScalarScore
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) (u : X → ℤ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (slice.targetAt selected hB o bW hb poly hm κ u).re *
        bufferedScalarScore χ coords T f lam u =
      (f u - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords u i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => (u i : ℝ) / physicalN i)
            (fun i => (u i : ZMod slice.path.referenceModulus)) β
            (fun i => coords u i - (β i : ℝ))) * T u β := by
  intro coords
  let β := nearestIntegerLift (coords u)
  let y := fun i => coords u i - (β i : ℝ)
  have hsum := χ.buffered_sum_eq_nearest (coords u) (fun β =>
    (κ * slice.recoveredG selected hB o bW hb e
      (fun i => (u i : ℝ) / physicalN i)
      (fun i => (u i : ZMod slice.path.referenceModulus)) β
      (fun i => coords u i - (β i : ℝ))) * T u β)
  simp only [mul_assoc] at hsum ⊢
  rw [hsum]
  change (slice.targetAt selected hB o bW hb poly hm κ u).re *
    ((f u - lam) * χ.value y * T u β) =
    (f u - lam) * (χ.value y * (κ * (slice.recoveredG selected hB o bW hb e
      (fun i => (u i : ℝ) / physicalN i)
      (fun i => (u i : ZMod slice.path.referenceModulus)) β y * T u β)))
  by_cases hχ : χ.value y = 0
  · simp only [hχ, mul_zero, zero_mul]
  · have ht := slice.targetAt_eq_recoveredG selected hB o bW hb e poly hm κ u β y
      (fun i => by dsimp only [y]; ring) (χ.support y hχ)
    have hre := congrArg Complex.re ht
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
    rw [hre]
    ring

theorem targetAt_mean_mul_bufferedScalarScore
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (𝔼 u : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ u.val).re *
        bufferedScalarScore χ coords T f lam u.val) =
      (𝔼 u : ↥(integerBox physicalN), (f u.val - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords u.val i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => (u.val i : ℝ) / physicalN i)
            (fun i => (u.val i : ZMod slice.path.referenceModulus)) β
            (fun i => coords u.val i - (β i : ℝ))) * T u.val β) := by
  intro coords
  apply Finset.expect_congr rfl
  intro u _
  exact slice.targetAt_mul_bufferedScalarScore selected hB o bW hb e poly hm κ χ T f lam u.val

theorem targetAt_mean_mul_bufferedScalarScore_eq_fin
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (κ : ℝ) (χ : PatchKernel d)
    (T : (X → ℤ) → (Fin d → ℤ) → ℝ) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val)
    (𝔼 u : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ u.val).re *
        bufferedScalarScore χ coords T f lam u.val) =
      (𝔼 u : (∀ i, Fin (physicalN i)),
        (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords (fun j => ((u j).val : ℤ)) i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => ((u i).val : ℝ) / physicalN i)
            (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
            (fun i => coords (fun j => ((u j).val : ℤ)) i - (β i : ℝ))) *
          T (fun i => ((u i).val : ℤ)) β) := by
  intro coords
  rw [slice.targetAt_mean_mul_bufferedScalarScore selected hB o bW hb e poly hm κ χ T f lam]
  simpa only [Int.cast_natCast] using
    (integerBox_subtype_mean_eq_fin physicalN (fun u : X → ℤ =>
      (f u - lam) * ∑' β : Fin d → ℤ,
        χ.value (fun i => coords u i - (β i : ℝ)) *
          (κ * slice.recoveredG selected hB o bW hb e
            (fun i => (u i : ℝ) / physicalN i)
            (fun i => (u i : ZMod slice.path.referenceModulus)) β
            (fun i => coords u i - (β i : ℝ))) * T u β))

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
