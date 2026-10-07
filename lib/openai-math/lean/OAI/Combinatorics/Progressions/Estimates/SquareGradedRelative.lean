/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

noncomputable def unitMonomial (n : ℕ) : Unit →₀ ℕ := Finsupp.single () n

@[simp] theorem weight_unitMonomial (n : ℕ) :
    Finsupp.weight (fun _ : Unit => 1) (unitMonomial n) = n := by
  simp [unitMonomial, Finsupp.weight_single]

@[simp] theorem unitMonomial_weight (α : Unit →₀ ℕ) :
    unitMonomial (Finsupp.weight (fun _ : Unit => 1) α) = α := by
  have h : α = Finsupp.single () (α ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [h]
  simp [unitMonomial, Finsupp.weight_single]

theorem unitMonomial_injective : Function.Injective unitMonomial := by
  intro m n h
  have hh := congrArg (Finsupp.weight (fun _ : Unit => 1)) h
  simpa only [weight_unitMonomial] using hh

@[simp] theorem unitMonomial_add (m n : ℕ) :
    unitMonomial (m + n) = unitMonomial m + unitMonomial n :=
  Finsupp.single_add _ _ _

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev AssociatedGraded (F : NilpotentLieFiltration L s) :=
  F.PolynomialSymbol (fun _ : Unit => 1)

noncomputable def associatedGradedIndexEquiv (ω : ι → ℕ) :
    SymbolBasisIndex (fun _ : Unit => 1) ω ≃ ι where
  toFun z := z.val.2
  invFun i := ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg unitMonomial z.property.symm).trans (unitMonomial_weight z.val.1)
    · rfl
  right_inv _ := rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def associatedGradedBasis : Basis ι ℚ F.AssociatedGraded :=
  (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).reindex (associatedGradedIndexEquiv ω)

@[simp] theorem associatedGradedBasis_apply (i : ι) :
    F.associatedGradedBasis b ω hlayers i =
      F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.reindex_apply]
  rfl

theorem associatedGradedBasis_repr (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr x i =
      (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).repr x
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.repr_reindex_apply]
  rfl

theorem associatedGradedBasis_bracket (i j k : ι) :
    (F.associatedGradedBasis b ω hlayers).repr
      ⁅F.associatedGradedBasis b ω hlayers i, F.associatedGradedBasis b ω hlayers j⁆ k =
      if ω i + ω j = ω k then b.repr ⁅b i, b j⁆ k else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedBasis_apply,
    F.associatedGradedBasis_apply, F.polynomialSymbolBasis_bracket]
  simp only [← unitMonomial_add, unitMonomial_injective.eq_iff]

noncomputable def associatedGradedFiltration : NilpotentLieFiltration F.AssociatedGraded s :=
  F.polynomialSymbolFiltration (fun _ : Unit => 1)

theorem associatedGradedFiltration_layer (j : ℕ) :
    F.associatedGradedFiltration.layer j =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | j ≤ ω i}) := by
  rw [associatedGradedFiltration, F.polynomialSymbolFiltration_layer b ω hlayers]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.val.2, hz, ?_⟩
    rw [F.associatedGradedBasis_apply]
    congr 1
    exact (associatedGradedIndexEquiv ω).left_inv z
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩, hi, ?_⟩
    exact (F.associatedGradedBasis_apply b ω hlayers i).symm

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def gradedMonomialLinear (j : ℕ) :
    F.layer j →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : Unit => 1) where
  toFun v := ⟨monomial (unitMonomial j) (v : L),
    F.monomial_mem_adaptedSubmodule (fun _ : Unit => 1) (unitMonomial j)
      (by simpa only [weight_unitMonomial] using v.property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _

@[simp] theorem gradedMonomialLinear_coe (j : ℕ) (v : F.layer j) :
    (F.gradedMonomialLinear j v : VectorPolynomial Unit ℚ L) = monomial (unitMonomial j) (v : L) := rfl

noncomputable def associatedGradedPieceMap (j : ℕ) : F.layer j →ₗ[ℚ] F.AssociatedGraded :=
  (F.polynomialSymbolMap (fun _ : Unit => 1)).toLinearMap.comp (F.gradedMonomialLinear j)

@[simp] theorem associatedGradedPieceMap_apply (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v =
      F.polynomialSymbolMap (fun _ : Unit => 1) (F.gradedMonomialLinear j v) := rfl

theorem associatedGradedPieceMap_eq_zero_iff (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v = 0 ↔ (v : L) ∈ F.layer (j + 1) := by
  rw [F.associatedGradedPieceMap_apply, F.polynomialSymbolMap_eq_zero_iff]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  constructor
  · intro h
    simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h (unitMonomial j)
  · intro h α
    by_cases hα : unitMonomial j = α
    · subst α
      simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h
    · rw [Finsupp.single_eq_of_ne (Ne.symm hα)]
      exact Submodule.zero_mem _

theorem associatedGradedPieceMap_ker (j : ℕ) :
    LinearMap.ker (F.associatedGradedPieceMap j) =
      (F.layer (j + 1)).comap (F.layer j).subtype := by
  ext v
  exact F.associatedGradedPieceMap_eq_zero_iff j v

theorem associatedGradedPieceMap_lie (i j : ℕ) (u : F.layer i) (v : F.layer j) :
    ⁅F.associatedGradedPieceMap i u, F.associatedGradedPieceMap j v⁆ =
      F.associatedGradedPieceMap (i + j) ⟨⁅(u : L), (v : L)⁆, F.lie_mem u.property v.property⟩ := by
  simp only [F.associatedGradedPieceMap_apply]
  rw [← LieHom.map_lie]
  apply congrArg (F.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  change ⁅monomial (unitMonomial i) (u : L), monomial (unitMonomial j) (v : L)⁆ = _
  rw [lie_monomial, ← unitMonomial_add]
  rfl

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_coordinate (j : ℕ) (v : F.layer j) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.associatedGradedPieceMap j v) i =
      if j = ω i then b.repr (v : L) i else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedPieceMap_apply,
    F.polynomialSymbolBasis_repr_map]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  by_cases h : j = ω i
  · simp [h]
  · have h' : unitMonomial j ≠ unitMonomial (ω i) := fun he => h (unitMonomial_injective he)
    simp [h, h']

theorem associatedGradedPieceMap_basis (j : ℕ) (i : ι) (hi : j ≤ ω i) (he : j = ω i) :
    F.associatedGradedPieceMap j
      ⟨b i, by rw [hlayers]; exact Submodule.subset_span ⟨i, hi, rfl⟩⟩ =
        F.associatedGradedBasis b ω hlayers i := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext k
  rw [F.associatedGradedPieceMap_coordinate]
  simp only [Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = k
  · subst k
    simp only [he, ite_true]
  · simp only [h, ite_false, ite_self]

theorem associatedGradedPieceMap_range (j : ℕ) :
    LinearMap.range (F.associatedGradedPieceMap j) =
      Submodule.span ℚ (F.associatedGradedBasis b ω hlayers '' {i | ω i = j}) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [basis_mem_span_image_iff]
    intro i hi
    rw [F.associatedGradedPieceMap_coordinate]
    exact ite_eq_right (Ne.symm hi)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨⟨b i, ?_⟩, ?_⟩
    · rw [hlayers]
      exact Submodule.subset_span ⟨i, hi.symm.le, rfl⟩
    · exact F.associatedGradedPieceMap_basis b ω hlayers j i hi.symm.le hi.symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def gradedRefiltrationLayer (j : ℕ) : Submodule ℚ L :=
  (U.toSubmodule.comap (F.associatedGradedPieceMap j)).map (F.layer j).subtype

theorem mem_gradedRefiltrationLayer (j : ℕ) (v : L) :
    v ∈ F.gradedRefiltrationLayer U j ↔
      ∃ hv : v ∈ F.layer j, F.associatedGradedPieceMap j ⟨v, hv⟩ ∈ U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hv, hU⟩
    exact ⟨⟨v, hv⟩, hU, rfl⟩

theorem mem_gradedRefiltrationLayer_iff (j : ℕ) (v : F.layer j) :
    (v : L) ∈ F.gradedRefiltrationLayer U j ↔ F.associatedGradedPieceMap j v ∈ U := by
  rw [F.mem_gradedRefiltrationLayer]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.property, h⟩⟩

theorem gradedRefiltrationLayer_le (j : ℕ) : F.gradedRefiltrationLayer U j ≤ F.layer j := by
  intro v hv
  exact ((F.mem_gradedRefiltrationLayer U j v).mp hv).choose

theorem layer_succ_le_gradedRefiltrationLayer (j : ℕ) :
    F.layer (j + 1) ≤ F.gradedRefiltrationLayer U j := by
  intro v hv
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.antitone (Nat.le_succ j) hv, ?_⟩
  rw [(F.associatedGradedPieceMap_eq_zero_iff j _).mpr hv]
  exact U.zero_mem

theorem gradedRefiltrationLayer_antitone : Antitone (F.gradedRefiltrationLayer U) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (F.gradedRefiltrationLayer_le U j).trans
      ((F.antitone hlt).trans (F.layer_succ_le_gradedRefiltrationLayer U i))
  · exact le_rfl

theorem gradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : L}
    (hv : v ∈ F.gradedRefiltrationLayer U i) (hz : z ∈ F.gradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.gradedRefiltrationLayer U (i + j) := by
  obtain ⟨hv, hUv⟩ := (F.mem_gradedRefiltrationLayer U i v).mp hv
  obtain ⟨hz, hUz⟩ := (F.mem_gradedRefiltrationLayer U j z).mp hz
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.lie_mem hv hz, ?_⟩
  rw [← F.associatedGradedPieceMap_lie i j ⟨v, hv⟩ ⟨z, hz⟩]
  exact U.lie_mem hUv hUz

theorem gradedRefiltrationLayer_terminal : F.gradedRefiltrationLayer U (s + 1) = ⊥ :=
  bot_unique ((F.gradedRefiltrationLayer_le U (s + 1)).trans F.terminal.le)

noncomputable def gradedRefiltrationSubalgebra : LieSubalgebra ℚ L :=
  { F.gradedRefiltrationLayer U 1 with
    lie_mem' := fun hv hz => F.gradedRefiltrationLayer_antitone U (by decide : 1 ≤ 1 + 1)
      (F.gradedRefiltrationLayer_lie_mem U hv hz) }

noncomputable def gradedRefiltration :
    NilpotentLieFiltration (F.gradedRefiltrationSubalgebra U) s where
  layer j := (F.gradedRefiltrationLayer U j).comap (F.gradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.gradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.gradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℚ).mp ((F.gradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_gradedRefiltration_layer (j : ℕ) (v : F.gradedRefiltrationSubalgebra U) :
    v ∈ (F.gradedRefiltration U).layer j ↔ (v : L) ∈ F.gradedRefiltrationLayer U j := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareDiagonalLayer (j : ℕ) : F.layer j →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩,
    x.property, x.property, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def squareRelativeLayer (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, 0), (F.mem_squareLieSubalgebra _).mpr (by
    simpa only [sub_zero] using F.antitone (Nat.add_le_add_right hj 1) x.property)⟩,
    F.antitone (Nat.le_succ j) x.property, (F.layer j).zero_mem, by
      change (x : L) - 0 ∈ F.layer (j + 1)
      simpa only [sub_zero] using x.property⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

noncomputable def squareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareDiagonalLayer j)

noncomputable def squareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareRelativeLayer j hj)

theorem squareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (x : F.layer j) :
    F.squareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x) = 0 ↔ _
  rw [F.squareFiltration.associatedGradedPieceMap_eq_zero_iff]
  change ((x : L) ∈ F.layer (j + 1) ∧ (x : L) ∈ F.layer (j + 1) ∧
    (x : L) - x ∈ F.layer (j + 1 + 1)) ↔ _
  simp only [sub_self, Submodule.zero_mem, and_true, and_self]

theorem squareGradedRelativePiece_eq_zero_iff (j : ℕ) (hj : 1 ≤ j) (x : F.layer (j + 1)) :
    F.squareGradedRelativePiece j hj x = 0 ↔ (x : L) ∈ F.layer (j + 2) := by
  change F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj x) = 0 ↔ _
  rw [F.squareFiltration.associatedGradedPieceMap_eq_zero_iff]
  change ((x : L) ∈ F.layer (j + 1) ∧ (0 : L) ∈ F.layer (j + 1) ∧
    (x : L) - 0 ∈ F.layer (j + 1 + 1)) ↔ _
  simp only [x.property, Submodule.zero_mem, sub_zero, true_and, Nat.add_assoc]

theorem squareGradedDiagonalPiece_lie (i j : ℕ) (x : F.layer i) (y : F.layer j) :
    ⁅F.squareGradedDiagonalPiece i x, F.squareGradedDiagonalPiece j y⁆ =
      F.squareGradedDiagonalPiece (i + j) ⟨⁅(x : L), (y : L)⁆, F.lie_mem x.property y.property⟩ := by
  change ⁅F.squareFiltration.associatedGradedPieceMap i _,
    F.squareFiltration.associatedGradedPieceMap j _⁆ = _
  rw [F.squareFiltration.associatedGradedPieceMap_lie]
  rfl

theorem squareGradedDiagonal_relative_lie (i j : ℕ) (hj : 1 ≤ j)
    (x : F.layer i) (y : F.layer (j + 1)) :
    ⁅F.squareGradedDiagonalPiece i x, F.squareGradedRelativePiece j hj y⁆ =
      F.squareGradedRelativePiece (i + j) (by omega)
        ⟨⁅(x : L), (y : L)⁆, by simpa only [Nat.add_assoc] using F.lie_mem x.property y.property⟩ := by
  change ⁅F.squareFiltration.associatedGradedPieceMap i _,
    F.squareFiltration.associatedGradedPieceMap j _⁆ = _
  rw [F.squareFiltration.associatedGradedPieceMap_lie]
  apply congrArg (F.squareFiltration.associatedGradedPieceMap (i + j))
  apply Subtype.ext
  apply Subtype.ext
  change (⁅(x : L), (y : L)⁆, ⁅(x : L), (0 : L)⁆) = (⁅(x : L), (y : L)⁆, 0)
  rw [lie_zero]

theorem squareGradedRelativePiece_lie_eq_zero (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (x : F.layer (i + 1)) (y : F.layer (j + 1)) :
    ⁅F.squareGradedRelativePiece i hi x, F.squareGradedRelativePiece j hj y⁆ = 0 := by
  change ⁅F.squareFiltration.associatedGradedPieceMap i _,
    F.squareFiltration.associatedGradedPieceMap j _⁆ = 0
  rw [F.squareFiltration.associatedGradedPieceMap_lie,
    F.squareFiltration.associatedGradedPieceMap_eq_zero_iff]
  have hxy : ⁅(x : L), (y : L)⁆ ∈ F.layer (i + j + 2) := by
    convert F.lie_mem x.property y.property using 1; congr 1; omega
  change ⁅(x : L), (y : L)⁆ ∈ F.layer (i + j + 1) ∧
    ⁅(0 : L), (0 : L)⁆ ∈ F.layer (i + j + 1) ∧
    ⁅(x : L), (y : L)⁆ - ⁅(0 : L), (0 : L)⁆ ∈ F.layer (i + j + 1 + 1)
  rw [lie_zero, sub_zero]
  exact ⟨F.antitone (by omega) hxy, (F.layer _).zero_mem, hxy⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareGradedRelativeGenerators : Set F.squareFiltration.AssociatedGraded :=
  {z | ∃ (j : ℕ) (hj : 1 ≤ j) (x : F.layer (j + 1)), z = F.squareGradedRelativePiece j hj x}

noncomputable def squareGradedRelativeSubmodule : Submodule ℚ F.squareFiltration.AssociatedGraded :=
  Submodule.span ℚ F.squareGradedRelativeGenerators

theorem squareGradedRelative_lie_eq_zero {x y : F.squareFiltration.AssociatedGraded}
    (hx : x ∈ F.squareGradedRelativeSubmodule) (hy : y ∈ F.squareGradedRelativeSubmodule) :
    ⁅x, y⁆ = 0 := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, hi, a, rfl⟩ := hx
    obtain ⟨j, hj, b, rfl⟩ := hy
    exact F.squareGradedRelativePiece_lie_eq_zero i j hi hj a b
  | zero_left y _ => exact zero_lie y
  | zero_right x _ => exact lie_zero x
  | add_left x y z _ _ _ hx hy => rw [add_lie, hx, hy, add_zero]
  | add_right x y z _ _ _ hx hy => rw [lie_add, hx, hy, add_zero]
  | smul_left r x y _ _ h => rw [smul_lie, h, smul_zero]
  | smul_right r x y _ _ h => rw [lie_smul, h, smul_zero]

noncomputable def squareGradedRelativeSubalgebra : LieSubalgebra ℚ F.squareFiltration.AssociatedGraded :=
  { F.squareGradedRelativeSubmodule with
    lie_mem' := fun hx hy => by
      rw [F.squareGradedRelative_lie_eq_zero hx hy]
      exact F.squareGradedRelativeSubmodule.zero_mem }

theorem squareGradedRelative_diagonal_lie_mem (i : ℕ) (x : F.layer i)
    {y : F.squareFiltration.AssociatedGraded} (hy : y ∈ F.squareGradedRelativeSubmodule) :
    ⁅F.squareGradedDiagonalPiece i x, y⁆ ∈ F.squareGradedRelativeSubmodule := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, b, rfl⟩ := hy
    rw [F.squareGradedDiagonal_relative_lie]
    exact Submodule.subset_span ⟨i + j, by omega, _, rfl⟩
  | zero => rw [lie_zero]; exact F.squareGradedRelativeSubmodule.zero_mem
  | add y z _ _ hy hz =>
    rw [lie_add]
    exact F.squareGradedRelativeSubmodule.add_mem hy hz
  | smul r y _ hy =>
    rw [lie_smul]
    exact F.squareGradedRelativeSubmodule.smul_mem r hy

theorem squareGradedPiece_decomposition (j : ℕ) (hj : 1 ≤ j)
    (x : F.squareFiltration.layer j) :
    F.squareFiltration.associatedGradedPieceMap j x =
      F.squareGradedDiagonalPiece j ⟨x.val.val.2, x.property.2.1⟩ +
      F.squareGradedRelativePiece j hj ⟨x.val.val.1 - x.val.val.2, x.property.2.2⟩ := by
  change F.squareFiltration.associatedGradedPieceMap j x =
    F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j _) +
      F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hj _)
  rw [← map_add]
  apply congrArg (F.squareFiltration.associatedGradedPieceMap j)
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val = (x.val.val.2, x.val.val.2) + (x.val.val.1 - x.val.val.2, 0)
  apply Prod.ext
  · change x.val.val.1 = x.val.val.2 + (x.val.val.1 - x.val.val.2)
    abel
  · exact (add_zero _).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
