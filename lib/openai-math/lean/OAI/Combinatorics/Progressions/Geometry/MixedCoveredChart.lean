import OAI.Combinatorics.Progressions.Sampling.CoveredJetSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

abbrev MixedCoveredJetSource {m : ℕ} (I O E : Fin m → Type*) (n : Fin m → ℕ) (d : ℕ) :=
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) × (∀ j, O j → E j → ZMod d)

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def mixedCoveredJetCoordinatesEquiv (d : ℕ) :
    MixedCoveredJetSource I O E n d ≃ CoveredJetChartSource U O E n d where
  toFun := mixedCoveredJetCoordinates U o d
  invFun z := (fun j => (mixedArrayRegroup (I j) (Fin (n j)) (O j)).symm
    (fun t => (orthonormalMixedChart (o j)).symm (z j t).1), fun j t => (z j t).2)
  left_inv z := by
    apply Prod.ext
    · funext j
      simp only [mixedCoveredJetCoordinates, MeasurableEquiv.symm_apply_apply]
    · rfl
  right_inv z := by
    funext j t
    simp only [mixedCoveredJetCoordinates, MeasurableEquiv.apply_symm_apply]

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

noncomputable def mixedCoveredJetChart : MixedCoveredJetSource I O E n d → EuclideanJetLayers U O :=
  fun z => coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d z)

def mixedCoveredJetRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (MixedCoveredJetSource I O E n d) :=
  mixedCoveredJetCoordinates U o d ⁻¹' coveredJetSourceRegion U b d Ω

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

theorem mixedCoveredJetChart_image (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    mixedCoveredJetChart U o b hb bW d '' mixedCoveredJetRegion U o b d Ω =
      coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨mixedCoveredJetCoordinates U o d z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := (mixedCoveredJetCoordinatesEquiv (O := O) (E := E) (n := n) U o d).surjective z
    refine ⟨w, ?_, ?_⟩
    · change mixedCoveredJetCoordinates U o d w ∈ coveredJetSourceRegion U b d Ω
      change mixedCoveredJetCoordinates U o d w = z at hw
      rwa [hw]
    · change coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d w) = _
      exact congrArg (coveredJetChart U b hb bW d) hw

omit [∀ j, Fintype (E j)] [NeZero d] in
theorem mixedCoveredJetRegion_mono
    {Ω Ω' : ∀ j, O j → Set (EuclideanSpace ℝ (J j))}
    (hΩ : ∀ j t, Ω j t ⊆ Ω' j t) :
    mixedCoveredJetRegion (E := E) U o b d Ω ⊆ mixedCoveredJetRegion U o b d Ω' := by
  intro z hz j hj t ht
  exact ⟨hΩ j t (hz j hj t ht).1, (hz j hj t ht).2⟩

end Erdos3.VectorPolynomial

end

end OAI
