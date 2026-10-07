import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
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
  (fun _ : G => integerScalarCubeWeights (Fin dim) S.value S.positive)

theorem allocatedOriginalPathLaw_finite_self_cube_selection
    {T : Type*} [Nonempty T] (e : T → LayerSamplerVariables G I n B → ℤ)
    (he : Function.Injective e)
    (hcover : ∀ t ∈ integerBox sides, ∃ u, e u = t) (f : (X → ℤ) → ℂ)
    (Good : (G → IntegerScalarCubeBox (Fin dim) S.value) → Prop)
    (genuine : ∀ x, Good x → (X → ℤ) → ℂ)
    {δ ε : ℝ} (hδ : 0 < δ)
    (hcomparison :
      ‖(allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
          stride cells hmass bases hbases htotal).complexMean (fun z =>
            𝔼 cube : SupportedCube dim (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
              physicalCubeSiteTest (integerSelfSiteTest dim f)
                (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
        (kernelLaw).goodPartBaseMean bases Good genuine‖ ≤ ε)
    (hdetected : δ + ε ≤
      ((allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem N hN hW hτ hξ
        stride cells hmass bases hbases htotal).complexMean (fun z =>
          normalizedSupportedCubeSum dim (integerBox sides)
            (fun _ t => finiteSiteExtension e
              (fun u => f (jointIntegerPhysicalSite (e u) (z.1.val, z.2.val))) t))).re) :
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value) (hx : Good x) (base : X → ℤ),
      0 < (kernelLaw).weight x ∧ base ∈ bases ∧ δ ≤ (genuine x hx base).re := by
  have hfinite := allocatedOriginalPathLaw_finite_self_cube_source (dim := dim) B U b hb o hR hσ
    S X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal e he hcover f
  have hphysical := allocatedOriginalPathLaw_cube_source (dim := dim) B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal
      (physicalCubeSiteTest (integerSelfSiteTest dim f))
  rw [hfinite, ← hphysical] at hdetected
  exact (kernelLaw).exists_good_base_of_comparison bases hbases Good genuine hδ hcomparison hdetected

end Erdos3.VectorPolynomial

end

end OAI
