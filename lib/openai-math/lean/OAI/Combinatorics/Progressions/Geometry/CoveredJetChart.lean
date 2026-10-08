/- Modified for ProveIt: supply explicit intermediate topology instances
for nested finite products on Lean 4.32 / Mathlib v4.32.0.
The statements are unchanged; this port remains under Apache-2.0. -/
import OAI.Combinatorics.Progressions.Probability.NormalizedCoveredDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev CoveredJetChartSource (O B : Fin m → Type*) (n : Fin m → ℕ) (d : ℕ) :=
  ∀ j, O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)

instance coveredJetChartSource_borel [∀ j, Fintype (O j)] (d : ℕ) [NeZero d] :
    BorelSpace (CoveredJetChartSource U O B n d) := by
  let : ∀ j, SecondCountableTopology ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) := fun _ => inferInstance
  let : ∀ j, SecondCountableTopology (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) := fun _ => inferInstance
  let : ∀ j, BorelSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => inferInstance
  let : ∀ j, BorelSpace (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def coveredJetChart : CoveredJetChartSource U O B n d → EuclideanJetLayers U O :=
  fun x j t => normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d (x j t)

def coveredJetSourceRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (CoveredJetChartSource U O B n d) :=
  Set.univ.pi (fun j => Set.univ.pi (fun t =>
    (normalizedLatticePoint (euclideanSubspace (U j)) (b j) ⁻¹' Ω j t) ×ˢ Set.univ))

def coveredJetTargetRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (EuclideanJetLayers U O) :=
  Set.univ.pi (fun j => Set.univ.pi (fun t =>
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d ⁻¹'
        normalizedChartRegion (euclideanSubspace (U j)) (b j) (hb j) (Ω j t)))

theorem coveredJetChart_continuous : Continuous (coveredJetChart (O := O) U b hb bW d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).comp
    ((continuous_apply t).comp (continuous_apply j))

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

theorem coveredJetChart_image (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω =
      coveredJetTargetRegion U b hb d Ω := by
  unfold coveredJetChart coveredJetSourceRegion coveredJetTargetRegion
  change Pi.map (fun j => Pi.map (fun _ : O j =>
    normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) d)) '' _ = _
  rw [Set.piMap_image_univ_pi]
  simp_rw [Set.piMap_image_univ_pi, normalizedCoveredChart_image]

variable [∀ j, Fintype (O j)]

omit [∀ j, Fintype (B j)] [NeZero d] in
theorem coveredJetSourceRegion_measurable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t)) :
    MeasurableSet (coveredJetSourceRegion (B := B) U b d Ω) := by
  apply MeasurableSet.univ_pi
  intro j
  apply MeasurableSet.univ_pi
  intro t
  exact ((hΩm j t).preimage (normalizedLatticePoint_continuous _ (b j)).measurable).prod
    MeasurableSet.univ

theorem coveredJetChart_embedding (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    MeasurableEmbedding (fun x : coveredJetSourceRegion (B := B) U b d Ω =>
      coveredJetChart U b hb bW d x.val) := by
  let : ∀ j, PolishSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => inferInstance
  let : ∀ j, SecondCountableTopology ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) := fun _ => inferInstance
  let : ∀ j, TopologicalSpace.IsCompletelyMetrizableSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) := fun _ => inferInstance
  let : ∀ j, SecondCountableTopology (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) := fun _ => inferInstance
  let : ∀ j, TopologicalSpace.IsCompletelyMetrizableSpace (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) := fun _ => inferInstance
  let : PolishSpace (CoveredJetChartSource U O B n d) := inferInstance
  exact ContinuousOn.measurableEmbedding (coveredJetSourceRegion_measurable U b d Ω hΩm)
    (coveredJetChart_continuous U b hb bW d).continuousOn
    (coveredJetChart_injOn U b hb bW d Ω hΩ)

end Erdos3.VectorPolynomial

end

end OAI
