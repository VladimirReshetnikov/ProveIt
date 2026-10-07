import Mathlib.Topology.Algebra.GroupWithZero
import OAI.Combinatorics.Progressions.Probability.MixedCoveredDensityMass

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

theorem normalizedLatticePoint_isClosedEmbedding {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) :
    Topology.IsClosedEmbedding (normalizedLatticePoint W b) := by
  have hi (i : Fin n) : Topology.IsClosedEmbedding (fun z : ℤ => (z : ℝ) / basisAxisScale b i) := by
    have hbi : (basisAxisScale b i : ℝ) ≠ 0 := by exact_mod_cast (basisAxisScale_pos b i).ne'
    simpa only [Function.comp_def, Homeomorph.coe_mulRight₀, div_eq_mul_inv] using
      (Homeomorph.mulRight₀ (basisAxisScale b i : ℝ)⁻¹ (inv_ne_zero hbi)).isClosedEmbedding.comp
        Real.isClosedEmbedding_intCast
  have hp := Topology.IsClosedEmbedding.prodMap (Homeomorph.refl W).isClosedEmbedding
    (Topology.IsClosedEmbedding.piMap hi)
  exact (normalizedOrthogonalChart W b).symm.toHomeomorph.isClosedEmbedding.comp hp

theorem normalizedLatticePoint_preimage_compact {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    {S : Set (EuclideanSpace ℝ D)} (hS : IsCompact S) :
    IsCompact (normalizedLatticePoint W b ⁻¹' S) :=
  (normalizedLatticePoint_isClosedEmbedding W b).isCompact_preimage hS

namespace VectorPolynomial

variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coveredJetSourceRegion_isCompact (d : ℕ) [NeZero d]
    (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) (hΩ : ∀ j t, IsCompact (Ω j t)) :
    IsCompact (coveredJetSourceRegion (B := B) U b d Ω) :=
  isCompact_univ_pi (fun j => isCompact_univ_pi (fun t =>
    (normalizedLatticePoint_preimage_compact _ (b j) (hΩ j t)).prod isCompact_univ))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

 theorem mixedCoveredJetCoordinatesEquiv_symm_continuous (d : ℕ) :
    Continuous (mixedCoveredJetCoordinatesEquiv (O := O) (E := E) (n := n) U o d).symm := by
  change Continuous (fun z : CoveredJetChartSource U O E n d =>
    (fun j => (fun i t => (orthonormalChart (o j)).symm (z j t).1.1 i,
      fun i t => (z j t).1.2 i), fun j t => (z j t).2))
  fun_prop

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

 theorem mixedCoveredJetRegion_isCompact (d : ℕ) [NeZero d]
    (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, IsCompact (Ω j t)) :
    IsCompact (mixedCoveredJetRegion (E := E) U o b d Ω) := by
  have h := (coveredJetSourceRegion_isCompact (B := E) U b d Ω hΩ).image
    (mixedCoveredJetCoordinatesEquiv_symm_continuous U o d)
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨mixedCoveredJetCoordinates U o d z, hz,
      (mixedCoveredJetCoordinatesEquiv U o d).symm_apply_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    change mixedCoveredJetCoordinates U o d
      ((mixedCoveredJetCoordinatesEquiv U o d).symm w) ∈ coveredJetSourceRegion U b d Ω
    change (mixedCoveredJetCoordinatesEquiv U o d)
      ((mixedCoveredJetCoordinatesEquiv U o d).symm w) ∈ coveredJetSourceRegion U b d Ω
    rwa [Equiv.apply_symm_apply]

variable [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]

instance mixedCoveredJetRawReference_isFiniteMeasureOnCompacts (d : ℕ) [NeZero d] :
    IsFiniteMeasureOnCompacts
      (mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d) := by
  let hc : ∀ j, IsFiniteMeasureOnCompacts
      (Measure.count : Measure (Fin (n j) → O j → ℤ)) := fun j => by
    constructor
    intro K hK
    exact Measure.count_apply_lt_top.mpr hK.finite_of_discrete
  let hm : ∀ j, IsFiniteMeasureOnCompacts
      (mixedArrayReference (I j) (Fin (n j)) (O j)) := fun j => by
    unfold mixedArrayReference
    infer_instance
  unfold mixedCoveredJetRawReference
  infer_instance

 theorem mixedCoveredJetRawReference_integrable_of_continuous_of_support
    (d : ℕ) [NeZero d]
    (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, IsCompact (Ω j t))
    (f : MixedCoveredJetSource I O E n d → ℂ) (hf : Continuous f)
    (hs : Function.support f ⊆ mixedCoveredJetRegion U o b d Ω) :
    Integrable f (mixedCoveredJetRawReference d) := by
  let : ∀ j, BorelSpace (O j → ℝ) := fun j => Pi.borelSpace
  let : ∀ j, BorelSpace (I j → O j → ℝ) := fun j => Pi.borelSpace
  let : ∀ j, BorelSpace (O j → ℤ) := fun j => Pi.borelSpace
  let : ∀ j, BorelSpace (Fin (n j) → O j → ℤ) := fun j => Pi.borelSpace
  let : ∀ j, BorelSpace ((I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :=
    fun j => Prod.borelSpace
  let : ∀ j, BorelSpace (E j → ZMod d) := fun j => Pi.borelSpace
  let : ∀ j, BorelSpace (O j → E j → ZMod d) := fun j => Pi.borelSpace
  let : BorelSpace (∀ j, O j → E j → ZMod d) := Pi.borelSpace
  let : BorelSpace (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) := Pi.borelSpace
  let : BorelSpace (MixedCoveredJetSource I O E n d) := Prod.borelSpace
  apply hf.integrable_of_hasCompactSupport
  exact (mixedCoveredJetRegion_isCompact U o b d Ω hΩ).of_isClosed_subset
    isClosed_closure (closure_minimal hs
      (mixedCoveredJetRegion_isCompact U o b d Ω hΩ).isClosed)

end Erdos3.VectorPolynomial

end

end OAI
