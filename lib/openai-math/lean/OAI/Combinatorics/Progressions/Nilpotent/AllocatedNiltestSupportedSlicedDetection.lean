import OAI.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSourceSelection

namespace OAI

section

namespace Erdos3

noncomputable def sampledSupportedSlicedDetectionConstant (s : ℕ) (P : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_sampled_niltest_cube_detection_with_sides.{0,0,0,0,0,0} s P)

theorem sampledSupportedSlicedDetectionConstant_two_le (s : ℕ) (P : Polynomial ℕ) :
    2 ≤ sampledSupportedSlicedDetectionConstant s P :=
  (Classical.choose_spec (exists_sampled_niltest_cube_detection_with_sides.{0,0,0,0,0,0} s P)).1

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_niltest_sliced_detection_with_sides
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f) :
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      IsDenseCommonStrideBox sides (p + 1) (commonStrideBox c₀ step₀ H₀) ∧
      commonStrideBox c₀ step₀ H₀ ⊆ Finset.univ.image e ∧
      (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1)) ≤
        (allocatedSlicedCubeSource (dim := s + 1) B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases H₀ hH₀ c₀ step₀ f).re := by
  obtain ⟨z, _⟩ := (pathLaw).exists_weight_pos
  let : Nonempty Path := ⟨z⟩
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, hdense₀, hcover₀, hcube⟩ :=
    (Classical.choose_spec (exists_sampled_niltest_cube_detection_with_sides.{0,0,0,0,0,0} s P)).2
      D V (pathLaw) (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
      slices e he c step H hstep hslices p q sides hp hq hdense hdimension hcomplexity hcap
      f α hf hα hαone hmesh hthreshold hdetected
  have hcover' (t) (ht : t ∈ integerBox H₀) : ∃ u, e u = commonStridePoint c₀ step₀ t := by
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (hcover₀ (commonStridePoint_mem c₀ step₀ H₀ ht))
    exact ⟨u, hu⟩
  have hext (z : Path) :
      normalizedSupportedCubeSum (s + 1) (integerBox H₀)
        (fun _ t => finiteSiteExtension e
          (fun u => f (jointIntegerPhysicalSite (e u) (z.1.val, z.2.val))) (commonStridePoint c₀ step₀ t)) =
      normalizedSupportedCubeSum (s + 1) (integerBox H₀)
        (fun _ t => f (jointIntegerPhysicalSite (commonStridePoint c₀ step₀ t) (z.1.val, z.2.val))) := by
    exact normalizedSupportedCubeSum_finiteSiteExtension_on_map (s + 1) (integerBox H₀)
      e he (commonStridePoint c₀ step₀) hcover'
      (fun t => f (jointIntegerPhysicalSite t (z.1.val, z.2.val)))
  simp only [hext] at hcube
  rw [allocatedOriginalPathLaw_sliced_cube_source B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H₀ hH₀ c₀ step₀ f] at hcube
  exact ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, hdense₀, hcover₀, hcube⟩

end Erdos3.VectorPolynomial

end

end OAI
