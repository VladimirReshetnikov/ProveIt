import OAI.Combinatorics.Progressions.Linear.PhysicalSiteProjection

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule VectorPolynomial
open scoped Classical

variable {X : Type*} {m dim : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

theorem physicalRowChart_base_matching
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (z : MixedCoveredJetSource I O E n d)
    (hz : mixedCoveredJetChart U o b hb bW d z =
      physicalCubeRowSample U d (fun _ => Subtype.val) p hm v)
    (s : Finset (Fin dim)) (j : Fin m) :
    (QuotientAddGroup.mk (physicalEuclideanSitePoint U p hm
      (fun x => (physicalCubeVertexValue v s x : ℝ)) j) : euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j)
          (mixedCoveredJetCoordinates U o d (mixedCoveredRowsSiteValue rowSets d z s) j ()).1 := by
  have hs : mixedCoveredJetChart U o b hb bW d (mixedCoveredRowsSiteValue rowSets d z s) =
      physicalSingleSiteValue U d p hm (fun x => (physicalCubeVertexValue v s x : ℝ)) := by
    rw [mixedCoveredRowsSiteValue_chart, hz]
    exact coveredRowsSiteValue_physical U d p hm hp v s
  have h := congrArg (fun y : EuclideanJetLayers U (fun _ => Unit) =>
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d
      (y j ())) hs
  rw [physicalSingleSiteValue_projection] at h
  change quotientIntegerCover _ d (normalizedCoveredChart (euclideanSubspace (U j))
    (b j) (hb j) (bW j) d (mixedCoveredJetCoordinates U o d
      (mixedCoveredRowsSiteValue rowSets d z s) j ())) = _ at h
  rw [normalizedCoveredChart_projection] at h
  exact h.symm

end Erdos3.BooleanCubeKernel

end

end OAI
