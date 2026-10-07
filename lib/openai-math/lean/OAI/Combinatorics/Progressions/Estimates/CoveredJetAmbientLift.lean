import OAI.Combinatorics.Progressions.Fourier.StandardJetFourier

namespace OAI

section

namespace Erdos3

open Module Submodule Set
open scoped Classical

theorem smallBoxTorusKernel_recover {D : Type*} [Fintype D]
    (H : (D → ℝ) → ℝ) (y : D → UnitAddCircle) (hy : smallBoxTorusKernel H y ≠ 0) :
    ∃ z : D → ℝ, (∀ i, (z i : UnitAddCircle) = y i) ∧ H z ≠ 0 := by
  let a : D → ℝ := fun i => (AddCircle.equivIoc 1 0 (y i)).val
  have hn : ∃ n : D → ℤ, H (fun i => a i + (n i : ℝ)) ≠ 0 := by
    by_contra h
    have hz : ∀ n : D → ℤ, H (fun i => a i + (n i : ℝ)) = 0 := by
      simpa only [not_exists, not_not] using h
    apply hy
    change (∑' n : D → ℤ, H (fun i => a i + (n i : ℝ))) = 0
    simp only [hz, tsum_zero]
  obtain ⟨n, hn⟩ := hn
  refine ⟨fun i => a i + (n i : ℝ), ?_, hn⟩
  intro i
  have hz : ((n i : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n i, by simp⟩
  simpa only [AddCircle.coe_add, hz, add_zero, a] using (AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := 0) (y := y i))

namespace VectorPolynomial

variable {m : ℕ} {O J I Q : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (Q j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetAmbientTorus_smallBox_mem_chart (y : EuclideanJetLayers U O)
    (v : JetAmbientIndex O J → ℝ)
    (hv : ∀ a, (v a : UnitAddCircle) = coveredJetAmbientTorus U d y a)
    (hsmall : ∀ a, |v a| < 1 / 2) :
    y ∈ mixedCoveredJetChart U o b hb bW d ''
      mixedCoveredJetRegion (O := O) (E := Q) U o b d (fun j _ => standardLatticeSmallBox (J j)) := by
  rw [mixedCoveredJetChart_image, coveredJetChart_image]
  intro j _ t _
  let Γ := (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk'_surjective Γ (quotientIntegerCover Γ d (y j t))
  have hphase (i : J j) : (w.val i : UnitAddCircle) = (v ⟨j, t, i⟩ : UnitAddCircle) := by
    have h := hv ⟨j, t, i⟩
    change (v ⟨j, t, i⟩ : UnitAddCircle) = subspaceAmbientTorus (U j)
      (euclideanSubspaceTorusEquiv (U j) (quotientIntegerCover Γ d (y j t))) i at h
    rw [← hw, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply] at h
    exact h.symm
  let p := (EuclideanSpace.equiv (J j) ℝ).symm (fun i => v ⟨j, t, i⟩)
  have hp : w.val - p ∈ standardEuclideanLattice (J j) := by
    apply (mem_standardEuclideanLattice (J j) _).mpr
    intro i
    have hz : ((w.val i - v ⟨j, t, i⟩ : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hphase, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    refine ⟨k, ?_⟩
    change (k : ℝ) = w.val i - v ⟨j, t, i⟩
    simpa only [zsmul_eq_mul, mul_one] using hk
  obtain ⟨z, hz, hq⟩ := exists_normalized_chart_lift (euclideanSubspace (U j)) (b j) (hb j) w p hp
  refine ⟨z, ?_, hq.trans hw⟩
  change normalizedLatticePoint (euclideanSubspace (U j)) (b j) z ∈ standardLatticeSmallBox (J j)
  rw [hz]
  exact fun i => hsmall ⟨j, t, i⟩

end VectorPolynomial
end Erdos3

end

end OAI
