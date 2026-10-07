import OAI.Combinatorics.Progressions.Probability.EmptyCoefficientDensity

namespace OAI

section

namespace Erdos3

open Module Submodule

theorem normalizedLatticePoint_sub_mem_of_mk_eq {D : Type*} [Fintype D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (u : W) (x : W × (Fin n → ℤ))
    (hx : QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u =
      normalizedLatticeQuotient W b hb x) :
    u.val - normalizedLatticePoint W b x ∈ standardEuclideanLattice D := by
  let z := latticeBasisEquiv (projectedIntegerLattice W) b hb x.2
  have hm : (u - (x.1 - projectedLatticeShift (standardEuclideanLattice D) W z)).val ∈
      standardEuclideanLattice D := QuotientAddGroup.eq_iff_sub_mem.mp hx
  rw [normalizedLatticePoint_eq_sheet W b hb]
  change u.val - latticeSheetPoint W z.val x.1 ∈ standardEuclideanLattice D
  rw [latticeSheetPoint_reconstruction (standardEuclideanLattice D) W z x.1]
  convert (standardEuclideanLattice D).sub_mem hm
    (projectedLatticeLift (standardEuclideanLattice D) W z).property using 1
  simp only [Submodule.coe_sub]
  abel

namespace VectorPolynomial

theorem euclideanCoefficientEquiv_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (c : CoefficientArray (K := K) U) (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (QuotientAddGroup.mk' (coefficientIntegerLattice U) c) j d =
      QuotientAddGroup.mk' _ ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, d⟩)) := by
  apply (euclideanSubspaceTorusEquiv (U j)).injective
  rw [euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    euclideanSubspaceTorusEquiv_mk, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem canonicalCoefficientSample_integer_remainder {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (a : CoefficientSamplerArrays (K := K) I n) (c : CoefficientArray (K := K) U)
    (hc : canonicalCoefficientSample U b hb o a = QuotientAddGroup.mk' (coefficientIntegerLattice U) c)
    (j : Fin m) (d : BoundedCoefficientExponent K (j.val + 1)) (i : J j) :
    ∃ z : ℤ, (c ⟨j, d⟩).val i - normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (mixedArrayRegroup (I j) (Fin (n j)) _ (a j) d)) i = z := by
  have he := congrArg (fun y => euclideanCoefficientEquiv U y j d) hc
  simp only [canonicalCoefficientSample, AddEquiv.apply_symm_apply, euclideanCoefficientEquiv_mk] at he
  have hm := normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace (U j)) (b j) (hb j)
    ((euclideanSubspaceArrayEquiv (U j)).symm (fun _ => c ⟨j, d⟩)) _ he.symm
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice (J j) _).mp hm i
  exact ⟨z, hz.symm⟩

end VectorPolynomial
end Erdos3

end

end OAI
