import OAI.Combinatorics.Progressions.Estimates.GradedUnitEvaluation

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem quotientTopGradedMap_coordinate (x : F.AssociatedGraded) (i : QuotientTopBasisIndex s ω) :
    (bQ).repr (F.quotientTopGradedMap x) i = (F.associatedGradedBasis e ω hF).repr x i.val := by
  classical
  have he : ((bQ).coord i).comp F.quotientTopGradedMap.toLinearMap =
      (F.associatedGradedBasis e ω hF).coord i.val := by
    apply (F.associatedGradedBasis e ω hF).ext
    intro j
    change (bQ).repr (F.associatedGradedMap F.quotientTop (lieQuotientMap (F.layerIdeal (s + 1)))
      (fun _ _ hx => F.quotientLie_mem _ le_rfl hx) (F.associatedGradedBasis e ω hF j)) i =
      (F.associatedGradedBasis e ω hF).repr (F.associatedGradedBasis e ω hF j) i.val
    rw [F.associatedGradedMap_basis_repr F.quotientTop e ω hF
      (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
      (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx),
      F.quotientTopBasis_repr_mk, Basis.repr_self, Basis.repr_self]
    by_cases hj : j = i.val <;> simp [hj]
  exact DFunLike.congr_fun he x

noncomputable def quotientTopGradedSection : F.quotientTop.AssociatedGraded →ₗ[ℚ] F.AssociatedGraded :=
  (bQ).constr ℚ (fun i => F.associatedGradedBasis e ω hF i.val)

@[simp] theorem quotientTopGradedSection_basis (i : QuotientTopBasisIndex s ω) :
    F.quotientTopGradedSection e ω hF ((bQ) i) = F.associatedGradedBasis e ω hF i.val :=
  Basis.constr_basis _ _ _ i

theorem quotientTopGradedSection_coordinate (x : F.quotientTop.AssociatedGraded)
    (i : QuotientTopBasisIndex s ω) :
    (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF x) i.val = (bQ).repr x i := by
  classical
  have he : ((F.associatedGradedBasis e ω hF).coord i.val).comp (F.quotientTopGradedSection e ω hF) =
      (bQ).coord i := by
    apply (bQ).ext
    intro j
    change (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF ((bQ) j)) i.val =
      (bQ).repr ((bQ) j) i
    rw [F.quotientTopGradedSection_basis, Basis.repr_self, Basis.repr_self]
    simp [Finsupp.single_apply, Subtype.ext_iff]
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_coordinate_zero (x : F.quotientTop.AssociatedGraded)
    (i : ι) (hi : s + 1 ≤ ω i) :
    (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF x) i = 0 := by
  classical
  have he : ((F.associatedGradedBasis e ω hF).coord i).comp (F.quotientTopGradedSection e ω hF) = 0 := by
    apply (bQ).ext
    intro j
    change (F.associatedGradedBasis e ω hF).repr (F.quotientTopGradedSection e ω hF ((bQ) j)) i = 0
    rw [F.quotientTopGradedSection_basis, Basis.repr_self]
    apply Finsupp.single_eq_of_ne
    exact fun hij => j.property (hij ▸ hi)
  exact DFunLike.congr_fun he x

theorem quotientTopGradedSection_rightInverse (x : F.quotientTop.AssociatedGraded) :
    F.quotientTopGradedMap (F.quotientTopGradedSection e ω hF x) = x := by
  apply (bQ).repr.injective
  ext i
  rw [F.quotientTopGradedMap_coordinate, F.quotientTopGradedSection_coordinate]

theorem quotientTopGradedMap_kernel :
    LinearMap.ker F.quotientTopGradedMap.toLinearMap =
      Submodule.span ℚ (F.associatedGradedBasis e ω hF '' {i | s + 1 ≤ ω i}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx i hi
    have he := congrArg (fun y => (bQ).repr y ⟨i, hi⟩) (show F.quotientTopGradedMap x = 0 from hx)
    simpa only [F.quotientTopGradedMap_coordinate, map_zero, Finsupp.zero_apply] using he
  · intro hx
    change F.quotientTopGradedMap x = 0
    apply (bQ).repr.injective
    ext i
    rw [F.quotientTopGradedMap_coordinate, map_zero, Finsupp.zero_apply]
    exact hx i.val i.property

theorem reducedSquareGradedSndMap_coordinate (x : F.squareFiltration.quotientTop.AssociatedGraded)
    (i : QuotientTopBasisIndex s ω) :
    (bQ).repr (F.reducedSquareGradedSndMap x) i = (bW).repr x (reducedSquareDiagonalIndex s ω i) := by
  rw [F.quotientTop.associatedGradedBasis_repr, F.squareFiltration.quotientTop.associatedGradedBasis_repr]
  exact F.reducedSquareSndSymbolMap_repr e ω hF (fun _ : Unit => 1) x
    ⟨(unitMonomial (ω i.val), i), weight_unitMonomial (ω i.val)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
