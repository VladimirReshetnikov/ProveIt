import OAI.Combinatorics.Progressions.Estimates.CoefficientDeckImageCongruence

namespace OAI

section

namespace Erdos3

open Module Submodule

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def latticeDeckInteger (z : Fin n → ℤ) (w : I → ℤ) : D → ℤ :=
  (standardLatticeCoordinates W bW b hb).symm (Sum.elim z w)

theorem latticeDeckInteger_coordinates (z : Fin n → ℤ) (w : I → ℤ) :
    standardLatticeCoordinates W bW b hb (latticeDeckInteger W bW b hb z w) =
      Sum.elim z w := LinearEquiv.apply_symm_apply _ _

theorem latticeDeckInteger_reconstruction (z : Fin n → ℤ) (w : I → ℤ) :
    (standardEuclideanPoint D (latticeDeckInteger W bW b hb z w)).val +
        (standardLatticeIntegerLift W b hb z).val =
      (bW.equivFun.symm w).val.val := by
  have h := standardLatticeCoordinates_reconstruction W bW b hb
    (latticeDeckInteger W bW b hb z w)
  simpa only [latticeDeckInteger_coordinates, Sum.elim_inl, Sum.elim_inr] using h

theorem latticeDeckInteger_sum_zsmul {S : Type*} (s : Finset S) (a : S → ℤ)
    (z : S → Fin n → ℤ) (w : S → I → ℤ) :
    latticeDeckInteger W bW b hb (∑ i ∈ s, a i • z i) (∑ i ∈ s, a i • w i) =
      ∑ i ∈ s, a i • latticeDeckInteger W bW b hb (z i) (w i) := by
  apply (standardLatticeCoordinates W bW b hb).injective
  simp only [latticeDeckInteger_coordinates, map_sum, map_zsmul]
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply]

theorem normalizedLatticePoint_linear_lift (x : W × (Fin n → ℤ)) :
    normalizedLatticePoint W b x = x.1.val +
      (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val := by
  rw [normalizedLatticePoint_eq_sheet W b hb, standardLatticeIntegerLift_projection]
  unfold latticeSheetPoint
  rw [latticeBasisEquiv_synthesis]

theorem normalizedDeckPoint_identity (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val =
      normalizedLatticePoint W b x +
        (standardEuclideanPoint D (latticeDeckInteger W bW b hb x.2 w)).val := by
  have hβ := latticeDeckInteger_reconstruction W bW b hb x.2 w
  have hs := W.starProjection_add_starProjection_orthogonal
    (standardLatticeIntegerLift W b hb x.2).val
  change (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (Wᗮ.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val = _ at hs
  rw [normalizedLatticePoint_linear_lift W b hb]
  change x.1.val - (W.orthogonalProjectionOnto (standardLatticeIntegerLift W b hb x.2).val).val +
    (bW.equivFun.symm w).val.val = _
  rw [← hs] at hβ
  rw [← hβ]
  abel

theorem normalizedCoverLift_add_deck (d : ℕ) (hd : 0 < d)
    (x : W × (Fin n → ℤ)) (w : I → ℤ) :
    normalizedCoverLift W b hb d x +
        (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
          bW d hd (integerResidueMap I d w)).val =
      QuotientAddGroup.mk' _ ((d : ℝ)⁻¹ •
        (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val)) := by
  have hr : integerResidueMap I d w =
      latticeBasisResidue (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (bW.equivFun.symm w) := by
    change integerResidueMap I d w = integerResidueMap I d (bW.equivFun (bW.equivFun.symm w))
    rw [LinearEquiv.apply_symm_apply]
  rw [hr, coverKernelBasisEquiv_residue, coverLatticePoint_val, smul_add, map_add]
  rfl

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def coefficientSamplerAmbientPoint
    (x : CoefficientSamplerArrays (K := K) I n) : CoefficientAmbientIndex K J → ℝ :=
  fun a => normalizedLatticePoint (euclideanSubspace (U a.1.1)) (b a.1.1)
    (orthonormalMixedChart (o a.1.1) (mixedArrayRegroup _ _ _ (x a.1.1) a.1.2)) a.2

noncomputable def coefficientSamplerDeckInteger
    (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    CoefficientAmbientIndex K J → ℤ :=
  fun a => latticeDeckInteger (euclideanSubspace (U a.1.1)) (bW a.1.1) (b a.1.1) (hb a.1.1)
    (fun i => (x a.1.1).2 i a.1.2) (w a.1.1 a.1.2) a.2

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_ambient_integer_chart
    (q : ℕ) (hq : 0 < q) (x : CoefficientSamplerArrays (K := K) I n)
    (w : ∀ j, BoundedCoefficientExponent K (j.val + 1) → E j → ℤ) :
    coefficientAmbientTorus U (canonicalCoefficientDeckSample U bW b hb o q hq x
      (fun j e => integerResidueMap (E j) q (w j e))) =
    fun a => (((coefficientSamplerAmbientPoint U b o x a +
      (coefficientSamplerDeckInteger U bW b hb x w a : ℝ)) / q : ℝ) : UnitAddCircle) := by
  funext a
  have he := canonicalCoefficientDeckSample_coordinate U bW b hb o q hq x
    (fun j e => integerResidueMap (E j) q (w j e)) a.1.1 a.1.2
  rw [normalizedCoverLift_add_deck] at he
  have he' := congrArg (euclideanSubspaceTorusEquiv (U a.1.1)) he
  rw [euclideanCoefficientEquiv_apply, AddEquiv.apply_symm_apply,
    euclideanSubspaceTorusEquiv_mk] at he'
  change subspaceAmbientTorus (U a.1.1) _ a.2 = _
  rw [he', subspaceAmbientTorus_mk]
  change (((q : ℝ)⁻¹ * _ : ℝ) : UnitAddCircle) = _
  apply congrArg (fun r : ℝ => (r : UnitAddCircle))
  rw [div_eq_inv_mul]
  congr 1
  exact congrArg (fun v : EuclideanSpace ℝ (J a.1.1) => v a.2)
    (normalizedDeckPoint_identity (euclideanSubspace (U a.1.1)) (bW a.1.1)
      (b a.1.1) (hb a.1.1) _ (w a.1.1 a.1.2))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_residue_injective (q : ℕ) (hq : 0 < q)
    (x : CoefficientSamplerArrays (K := K) I n) :
    Function.Injective (canonicalCoefficientDeckSample U bW b hb o q hq x) := by
  intro r s h
  apply (coefficientDeckKernelEquiv U bW q hq).injective
  apply Subtype.ext
  exact add_left_cancel h

theorem canonicalCoefficientDeckSample_existsUnique_residue (q : ℕ) (hq : 0 < q)
    (x : CoefficientSamplerArrays (K := K) I n) (y : CoefficientTorus (K := K) U)
    (hy : quotientIntegerCover (coefficientIntegerLattice (K := K) U) q y =
      canonicalCoefficientSample U b hb o x) :
    ∃! r : CoefficientDeckResidues (K := K) E q,
      canonicalCoefficientDeckSample U bW b hb o q hq x r = y := by
  let z : (quotientIntegerCover (coefficientIntegerLattice (K := K) U) q).ker :=
    ⟨y - canonicalCoefficientCoverLift U b hb o q x, by
      change quotientIntegerCover (coefficientIntegerLattice (K := K) U) q
        (y - canonicalCoefficientCoverLift U b hb o q x) = 0
      rw [map_sub, hy, canonicalCoefficientCoverLift_projection U b hb o q hq, sub_self]⟩
  let r := (coefficientDeckKernelEquiv U bW q hq).symm z
  have hr : canonicalCoefficientDeckSample U bW b hb o q hq x r = y := by
    unfold canonicalCoefficientDeckSample
    change canonicalCoefficientCoverLift U b hb o q x +
      (coefficientDeckKernelEquiv U bW q hq ((coefficientDeckKernelEquiv U bW q hq).symm z)).val = y
    rw [AddEquiv.apply_symm_apply]
    change canonicalCoefficientCoverLift U b hb o q x +
      (y - canonicalCoefficientCoverLift U b hb o q x) = y
    abel
  exact ⟨r, hr, fun s hs => canonicalCoefficientDeckSample_residue_injective
    U bW b hb o q hq x (hs.trans hr.symm)⟩

theorem canonicalCoefficientSample_injOn_chart :
    Set.InjOn (canonicalCoefficientSample (K := K) U b hb o)
      {x | ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (x j)} := by
  intro x hx y hy h
  have h' := congrArg (euclideanCoefficientEquiv U) h
  simp only [canonicalCoefficientSample, AddEquiv.apply_symm_apply] at h'
  funext j
  exact mixedArrayQuotient_injOn_chart (euclideanSubspace (U j)) (b j) (hb j) (o j)
    (hx j) (hy j) (congrFun h' j)

theorem canonicalCoefficientDeckSample_injOn_chart (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q =>
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2)
      {z | ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (z.1 j)} := by
  rintro ⟨x, r⟩ hx ⟨y, s⟩ hy h
  have hp := congrArg (quotientIntegerCover (coefficientIntegerLattice (K := K) U) q) h
  simp only [canonicalCoefficientDeckSample_projection] at hp
  have hxy := canonicalCoefficientSample_injOn_chart U b hb o hx hy hp
  change x = y at hxy
  subst y
  have hrs := canonicalCoefficientDeckSample_residue_injective U bW b hb o q hq x h
  change r = s at hrs
  subst s
  rfl

theorem canonicalCoefficientDeckSample_injOn_smallAmbient (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q =>
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2)
      {z | ∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2} := by
  intro x hx y hy h
  apply canonicalCoefficientDeckSample_injOn_chart U bW b hb o q hq _ _ h
  · intro j e i
    exact hx ⟨⟨j, e⟩, i⟩
  · intro j e i
    exact hy ⟨⟨j, e⟩, i⟩

variable [Fintype K]

theorem canonicalCoefficientDeckSample_recover_nonzero
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (q : ℕ) (hq : 0 < q) (y : CoefficientTorus (K := K) U)
    (hy : canonicalCoefficientDensity U b hb o c w p
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) q y) ≠ 0) :
    ∃! z : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q,
      canonicalCoefficientDeckSample U bW b hb o q hq z.1 z.2 = y ∧
      ∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (z.1 j) ∧
        mixedArraySupported (c j) (w j) (p j) (z.1 j) := by
  obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o c w p hy
  obtain ⟨r, hr, _⟩ := canonicalCoefficientDeckSample_existsUnique_residue U bW b hb o q hq x y hx.1.symm
  refine ⟨⟨x, r⟩, ⟨hr, hx.2⟩, ?_⟩
  intro z hz
  exact canonicalCoefficientDeckSample_injOn_chart U bW b hb o q hq
    (fun j => (hz.2 j).1) (fun j => (hx.2 j).1) (hz.1.trans hr.symm)

end Erdos3.VectorPolynomial

end

end OAI
