import OAI.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r)
  (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedShiftPolynomialGenerator (t d k l : ℕ)
    (p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l) :
    markedShiftSubalgebra F v w marked t :=
  markedShiftLayerPolynomialMap F v w marked hw hv t d k l
    (markedPolynomialGeneratorFamily (s := s) v w marked t d k l p)

theorem markedShiftPolynomialGenerator_span (t d k l : ℕ) :
    Submodule.span ℚ (Set.range (markedShiftPolynomialGenerator F v w marked hw hv t d k l)) =
      markedShiftPolynomialSubmodule F v w marked t d k l := by
  change Submodule.span ℚ (Set.range
    (markedShiftLayerPolynomialMap F v w marked hw hv t d k l ∘
      markedPolynomialGeneratorFamily (s := s) v w marked t d k l)) = _
  rw [Set.range_comp, ← Submodule.map_span,
    markedPolynomialGeneratorFamily_span F v w marked hw hv,
    Submodule.map_top]
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rfl, p.property⟩
  · intro hx
    refine ⟨⟨x.val.left.val, hx.2⟩, ?_⟩
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact hx.1.symm

theorem markedShiftPolynomialGenerator_coordinate_height (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)
    (t d k l : ℕ) (p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftPolynomialGenerator F v w marked hw hv t d k l p).val j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  rcases j with j | j
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
    exact finiteMarkedPolynomialValues_coefficient_height b v w marked hH hc hgen
      s d k l p.property j.val.1 j.val.2
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
    exact rationalHeightLE_zero (hH.trans (lieTreeHeight_ge_input _ _ _))

omit hw hv in
theorem finiteMarkedPolynomialValues_functional_height (b : Basis ι ℚ L)
    (η : L →ₗ[ℚ] ℚ) {H K A : ℕ} (hA : 1 ≤ A)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)
    (hη : ∀ i, RationalHeightLE (η (b i)) K) (t d k l : ℕ)
    (a : Fin t → ℚ) (ha : ∀ i, RationalHeightLE (a i) A)
    {p : VectorPolynomial (Fin t) ℚ L}
    (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l) :
    RationalHeightLE (η (eval a p))
      (A ^ s * ((Fintype.card ι + 1) *
        (lieTreeHeight (Fintype.card ι) H s * K) ^ Fintype.card ι)) := by
  classical
  obtain ⟨α, hα, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  have hxH := linearFunctional_coordinate_height b η hη x
    (fun j => finiteMarkedLieValues_coordinate_height b v w marked hc hgen s d _ l hx j)
  have hprod := rationalHeightLE_prod α.support (fun i => a i ^ α i)
    (fun i => A ^ α i) (fun i _ => (ha i).pow (α i))
  have hαs : ∑ i ∈ α.support, α i ≤ s := by
    simpa only [mem_markedParameterExponents, Finsupp.weight_apply, Finsupp.sum,
      smul_eq_mul, mul_one] using hα
  have hprod' : RationalHeightLE (α.prod (fun i n => a i ^ n)) (A ^ s) := by
    apply hprod.mono
    rw [Finset.prod_pow_eq_pow_sum]
    exact pow_le_pow_right₀ hA hαs
  rw [eval_monomial, map_smul, smul_eq_mul]
  exact hprod'.mul hxH

end Erdos3

end

end OAI
