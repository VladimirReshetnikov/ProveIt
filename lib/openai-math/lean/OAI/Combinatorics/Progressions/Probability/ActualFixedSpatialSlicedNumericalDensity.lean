import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedNumericalGridCap

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem SlicedProductBlock.pairDensity_nonneg {ι : Type*} [Fintype ι]
    (A B : SlicedProductBlock ι) (x : ℝ) : 0 ≤ SlicedProductBlock.pairDensity A B x := by
  unfold pairDensity affinePairDensity randomIntervalDensity densityMixture
  apply integral_nonneg
  intro p
  unfold normalizedIntervalWindow affinePairWidth
  exact div_nonneg (intervalWindow_mem_Icc _ _ _).1
    (le_max_of_le_left (abs_nonneg _))

theorem SlicedProductBlock.fourDensity_nonneg {ι : Type*} [Fintype ι]
    (A B C D : SlicedProductBlock ι) (x : ℝ) :
    0 ≤ SlicedProductBlock.fourDensity A B C D x := by
  unfold fourDensity scalarDensityConvolution
  exact integral_nonneg (fun t =>
    mul_nonneg (pairDensity_nonneg A B _) (pairDensity_nonneg C D _))

theorem principalFourRemainderDensity_nonneg {J ι : Type*}
    [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]
    (c : Fin 4 ⊕ J → ℝ) (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) (x : ℝ) :
    0 ≤ principalFourRemainderDensity c lower width x := by
  unfold principalFourRemainderDensity independentShiftDensity densityMixture
  exact integral_nonneg (fun t => SlicedProductBlock.fourDensity_nonneg _ _ _ _ _)

theorem canonicalSlicedPrincipalDensity_nonneg {B F : Type*}
    [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ)
    (lower width : B × F → ℝ) (x : ℝ) :
    0 ≤ canonicalSlicedPrincipalDensity hB i c lower width x :=
  principalFourRemainderDensity_nonneg _ _ _ _

theorem jointSlicedPrincipalDensity_nonneg {D : Type*} [Fintype D]
    {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (hB : ∀ d, 4 ≤ Fintype.card (B d)) (i : ∀ d, F d)
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (shift : D → ℝ) (y : (Σ _d : D, Unit) → ℝ) :
    0 ≤ jointSlicedPrincipalDensity hB i c lower width shift y := by
  exact sigmaAxisWeight_nonneg _
    (fun d v => canonicalSlicedPrincipalDensity_nonneg (hB d) (i d)
      (c d) (lower d) (width d) _) y

end Erdos3

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
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

theorem density_nonneg
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    0 ≤ slice.density hBactive y := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  classical
  unfold density fixedSpatialKernelSliceOriginalForecastDensity
    fixedSpatialKernelOriginalForecastDensity binaryDensity allocatedFixedPathLiftDensity
  apply mul_nonneg
  · exact (fixedSpatialKernelDensity_probability_density _ _ _ _ _ _).1 _
  · exact jointSlicedPrincipalDensity_nonneg _ _ _ _ _ _ _

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
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
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice : ℝ}
variable {A : Type} [Fintype A] {selected : A → Σ j : Fin m, Fin (n j)}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)
variable (qnum : ActualFixedSpatialSlicedForecastNumerics s)

namespace ActualFixedSpatialSlicedAdmissiblePath

variable (member : ActualFixedSpatialSlicedAdmissiblePath
  (hR := hR) (hσ := hσ) (spatial := spatial) (kernel := kernel) (block := block)
  (spatialEquiv := spatialEquiv) (Wsp := Wsp) (Lsp := Lsp) (physicalN := physicalN) s qnum)

theorem density_mem_Icc
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ))) :
    member.slice.density s.hBactive y ∈
      Set.Icc (0 : ℝ) (actualSlicedForecastDensityBudget s qnum.v) := by
  have hbound := (member.slice.density_uniform_budget s.hBactive s.hP s.hδslice
    s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks qnum.hv member.kernelWidth).2.2.1 y
  have hn := member.slice.density_nonneg s.hBactive y
  rw [Real.norm_eq_abs, abs_of_nonneg hn] at hbound
  exact ⟨hn, hbound⟩

theorem density_lipschitz :
    LipschitzWith (Real.toNNReal (actualSlicedForecastDensityBudget s qnum.v))
      (member.slice.density s.hBactive) :=
  (member.slice.density_uniform_budget s.hBactive s.hP s.hδslice
    s.hδsliceInv s.hX (s.haxes.trans s.hDP) s.hblocks qnum.hv member.kernelWidth).2.2.2

theorem density_lipschitz_nnreal :
    LipschitzWith
      (⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩ : ℝ≥0)
      (member.slice.density s.hBactive) := by
  have hbudget : Real.toNNReal (actualSlicedForecastDensityBudget s qnum.v) =
      (⟨actualSlicedForecastDensityBudget s qnum.v, Real.exp_nonneg _⟩ : ℝ≥0) := by
    apply Subtype.ext
    exact Real.coe_toNNReal _ (Real.exp_nonneg _)
  rw [← hbudget]
  exact member.density_lipschitz s qnum

end ActualFixedSpatialSlicedAdmissiblePath
end Erdos3.VectorPolynomial

end

end OAI
