import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Estimates.QuotientTopSymbol
import OAI.Combinatorics.Progressions.Estimates.ReducedSquareSymbol
import OAI.Combinatorics.Progressions.Estimates.SquareSymbolRelative
import OAI.Combinatorics.Progressions.Geometry.FilteredSymbolMapCoordinates
import OAI.Combinatorics.Progressions.Geometry.SupportedLieQuotient

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareCoordinates : F.squareLieSubalgebra ≃ₗ[ℚ] L × F.layer 2 where
  toFun x := (x.val.2, ⟨x.val.1 - x.val.2, (F.mem_squareLieSubalgebra x.val).mp x.property⟩)
  invFun x := ⟨(x.1 + x.2, x.1), (F.mem_squareLieSubalgebra _).mpr (by
    change x.1 + (x.2 : L) - x.1 ∈ F.layer 2
    rw [add_sub_cancel_left]
    exact x.2.property)⟩
  left_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; dsimp; abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext; exact (smul_sub r _ _).symm

noncomputable def squareBasis (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) :
    Basis (ι ⊕ κ) ℚ F.squareLieSubalgebra :=
  (b.prod c).map F.squareCoordinates.symm

@[simp] theorem squareBasis_inl (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) (i : ι) :
    (F.squareBasis b c (Sum.inl i)).val = (b i, b i) := by
  simp [squareBasis, Basis.map_apply, squareCoordinates]

@[simp] theorem squareBasis_inr (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2)) (i : κ) :
    (F.squareBasis b c (Sum.inr i)).val = ((c i : L), 0) := by
  simp [squareBasis, Basis.map_apply, squareCoordinates]

theorem squareBasis_repr_inl (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2))
    (x : F.squareLieSubalgebra) (i : ι) :
    (F.squareBasis b c).repr x (Sum.inl i) = b.repr x.val.2 i := by
  simp [squareBasis, Basis.map_repr, squareCoordinates]

theorem squareBasis_repr_inr (b : Basis ι ℚ L) (c : Basis κ ℚ (F.layer 2))
    (x : F.squareLieSubalgebra) (i : κ) :
    (F.squareBasis b c).repr x (Sum.inr i) =
      c.repr ⟨x.val.1 - x.val.2, (F.mem_squareLieSubalgebra x.val).mp x.property⟩ i := by
  simp [squareBasis, Basis.map_repr, squareCoordinates]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem mem_squareLayer_iff_second_and_difference (j : ℕ) (x : L × L) :
    x ∈ F.squareLayer j ↔ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1) := by
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h.1, h.2⟩
    have hx := (F.layer j).add_mem (F.antitone (Nat.le_succ j) h.2) h.1
    simpa only [sub_add_cancel] using hx

noncomputable def adaptedSquareBasis (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) :
    Basis (ι ⊕ {i // 2 ≤ w i}) ℚ F.squareLieSubalgebra :=
  F.squareBasis b (supportedSubmoduleBasis b (F.layer 2) {i | 2 ≤ w i} h)

@[simp] theorem adaptedSquareBasis_inl (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) (i : ι) :
    (F.adaptedSquareBasis b w h (Sum.inl i)).val = (b i, b i) :=
  F.squareBasis_inl b _ i

@[simp] theorem adaptedSquareBasis_inr (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i})) (i : {i // 2 ≤ w i}) :
    (F.adaptedSquareBasis b w h (Sum.inr i)).val = (b i, 0) := by
  simp only [adaptedSquareBasis, F.squareBasis_inr]
  apply Prod.ext
  · exact supportedSubmoduleBasis_coe b (F.layer 2) {i | 2 ≤ w i} h i
  · rfl

def squareBasisWeight (w : ι → ℕ) : (ι ⊕ {i // 2 ≤ w i}) → ℕ :=
  Sum.elim w (fun i => w i - 1)

theorem adaptedSquareBasis_layers (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (j : ℕ) :
    F.squareFiltration.layer j = Submodule.span ℚ
      (F.adaptedSquareBasis b w (hlayers 2) '' {i | j ≤ squareBasisWeight w i}) := by
  have hmem (k : ℕ) (x : L) : x ∈ F.layer k ↔ ∀ i, ¬ k ≤ w i → b.repr x i = 0 := by
    rw [hlayers k, basis_mem_span_image_iff]
    rfl
  ext x
  rw [F.mem_squareFiltration_layer, F.mem_squareLayer_iff_second_and_difference,
    basis_mem_span_image_iff, hmem, hmem]
  constructor
  · rintro ⟨hy, hz⟩ i hi
    cases i with
    | inl i =>
      change (F.squareBasis b _).repr x (Sum.inl i) = 0
      rw [F.squareBasis_repr_inl]
      exact hy i hi
    | inr i =>
      change (F.squareBasis b _).repr x (Sum.inr i) = 0
      rw [F.squareBasis_repr_inr, supportedSubmoduleBasis_repr]
      exact hz i (by change ¬ j ≤ w i - 1 at hi; have := i.property; omega)
  · intro hx
    constructor
    · intro i hi
      have hh := hx (Sum.inl i) hi
      change (F.squareBasis b _).repr x (Sum.inl i) = 0 at hh
      simpa only [F.squareBasis_repr_inl] using hh
    · intro i hi
      by_cases h2 : 2 ≤ w i
      · have hsmall : ¬ j ≤ squareBasisWeight w (Sum.inr (⟨i, h2⟩ : {i // 2 ≤ w i})) := by
          change ¬ j ≤ w i - 1
          omega
        have hh := hx (Sum.inr ⟨i, h2⟩) hsmall
        change (F.squareBasis b _).repr x
          (Sum.inr (⟨i, h2⟩ : {i // 2 ≤ w i})) = 0 at hh
        rw [F.squareBasis_repr_inr] at hh
        exact (supportedSubmoduleBasis_repr b (F.layer 2) {i | 2 ≤ w i}
          (hlayers 2) _ (⟨i, h2⟩ : {i // 2 ≤ w i})).symm.trans hh
      · exact (hmem 2 (x.val.1 - x.val.2)).mp
          ((F.mem_squareLieSubalgebra x.val).mp x.property) i h2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev QuotientTopBasisIndex (s : ℕ) (ω : ι → ℕ) := {i : ι // ¬ s + 1 ≤ ω i}

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def quotientTopBasis :
    Basis (QuotientTopBasisIndex s ω) ℚ (L ⧸ F.layerIdeal (s + 1)) :=
  supportedQuotientBasis e (F.layerIdeal (s + 1)).toSubmodule {i | s + 1 ≤ ω i} (hF (s + 1))

@[simp] theorem quotientTopBasis_apply (i : QuotientTopBasisIndex s ω) :
    F.quotientTopBasis e ω hF i = lieQuotientMap (F.layerIdeal (s + 1)) (e i.val) :=
  supportedQuotientBasis_apply e _ _ _ i

theorem quotientTopBasis_repr_mk (x : L) (i : QuotientTopBasisIndex s ω) :
    (F.quotientTopBasis e ω hF).repr (lieQuotientMap (F.layerIdeal (s + 1)) x) i = e.repr x i.val :=
  supportedQuotientBasis_repr_mk e _ _ _ x i

theorem quotientTopBasis_layers (j : ℕ) :
    F.quotientTop.layer j = Submodule.span ℚ
      (F.quotientTopBasis e ω hF '' {i | j ≤ ω i.val}) :=
  F.supportedQuotientBasis_layers e ω hF (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ ω i} (hF (s + 1)) j

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareSnd :
    (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (L ⧸ F.layerIdeal (s + 1)) :=
  lieQuotientDescend (F.squareFiltration.layerIdeal (s + 1))
    ((lieQuotientMap (F.layerIdeal (s + 1))).comp F.squareSnd) (by
      intro x hx
      exact (lieQuotientMap_eq_zero _ _).mpr hx.2.1)

noncomputable def reducedSquareDiagonal :
    (L ⧸ F.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :=
  lieQuotientDescend (F.layerIdeal (s + 1))
    ((lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).comp F.squareDiagonalLie) (by
      intro x hx
      apply (lieQuotientMap_eq_zero _ _).mpr
      exact ⟨hx, hx, by change x - x ∈ F.layer (s + 1 + 1); simp⟩)

@[simp] theorem reducedSquareSnd_mk (x : F.squareLieSubalgebra) :
    F.reducedSquareSnd (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) x) =
      lieQuotientMap (F.layerIdeal (s + 1)) (F.squareSnd x) := rfl

@[simp] theorem reducedSquareDiagonal_mk (x : L) :
    F.reducedSquareDiagonal (lieQuotientMap (F.layerIdeal (s + 1)) x) =
      lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)) (F.squareDiagonalLie x) := rfl

@[simp] theorem reducedSquareSnd_diagonal (x : L ⧸ F.layerIdeal (s + 1)) :
    F.reducedSquareSnd (F.reducedSquareDiagonal x) = x := by
  obtain ⟨a, rfl⟩ := lieQuotientMap_surjective (F.layerIdeal (s + 1)) x
  rfl

theorem reducedSquareSnd_mem (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1))
    (hx : x ∈ F.squareFiltration.quotientTop.layer j) :
    F.reducedSquareSnd x ∈ F.quotientTop.layer j := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact F.quotientLie_mem _ le_rfl ha.2.1

theorem reducedSquareDiagonal_mem (j : ℕ) (x : L ⧸ F.layerIdeal (s + 1))
    (hx : x ∈ F.quotientTop.layer j) :
    F.reducedSquareDiagonal x ∈ F.squareFiltration.quotientTop.layer j := by
  obtain ⟨a, ha, rfl⟩ := hx
  apply F.squareFiltration.quotientLie_mem _ le_rfl
  exact ⟨ha, ha, by change a - a ∈ F.layer (j + 1); simp⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squarePairMap : F.squareLieSubalgebra →ₗ⁅ℚ⁆ (Bool → L) :=
  liePiMap (fun i : Bool => cond i F.squareFst F.squareSnd)

@[simp] theorem squarePairMap_false (x : F.squareLieSubalgebra) : F.squarePairMap x false = x.val.2 := rfl
@[simp] theorem squarePairMap_true (x : F.squareLieSubalgebra) : F.squarePairMap x true = x.val.1 := rfl

theorem squarePairMap_injective : Function.Injective F.squarePairMap := by
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrFun h true) (congrFun h false)

theorem squareLattice_eq_pair_comap (Γ : Subgroup F.Group) :
    F.squareLattice Γ =
      (piBCHSubgroup (fun _ : Bool => F) (fun _ => Γ)).comap
        (map (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Bool => F)).lowerCentralSeries_eq_bot) F.squarePairMap) := by
  ext g
  rw [F.mem_squareLattice, Subgroup.mem_comap, mem_piBCHSubgroup]
  constructor
  · intro h i
    cases i
    · exact h.2
    · exact h.1
  · intro h
    exact ⟨h true, h false⟩

variable [Fintype ι]

theorem card_squareBasis_index_le (w : ι → ℕ) :
    Fintype.card (ι ⊕ {i // 2 ≤ w i}) ≤ 2 * Fintype.card ι := by
  rw [Fintype.card_sum]
  have h := Fintype.card_subtype_le (fun i => 2 ≤ w i)
  omega

omit [Fintype ι] in

theorem adaptedSquareBasis_pairMap_height (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    (k : Σ _ : Bool, ι) (j : ι ⊕ {i // 2 ≤ w i}) :
    RationalHeightLE ((Pi.basis (fun _ : Bool => b)).repr
      (F.squarePairMap (F.adaptedSquareBasis b w h j)) k) 1 := by
  rcases k with ⟨flag, i⟩
  rw [Pi.basis_repr]
  cases j with
  | inl j =>
    cases flag <;>
      simpa only [squarePairMap_false, squarePairMap_true, adaptedSquareBasis_inl] using
        basis_repr_height_one b j i
  | inr j =>
    cases flag
    · simp only [squarePairMap_false, adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero le_rfl
    · simpa only [squarePairMap_true, adaptedSquareBasis_inr] using basis_repr_height_one b j i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquareSndPolynomialMap :
    F.squareFiltration.quotientTop.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.quotientTop.filteredPolynomialMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem w

noncomputable def reducedSquareDiagonalPolynomialMap :
    F.quotientTop.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.quotientTop.filteredPolynomialMap F.squareFiltration.quotientTop
    F.reducedSquareDiagonal F.reducedSquareDiagonal_mem w

noncomputable def reducedSquareSndSymbolMap :
    F.squareFiltration.quotientTop.PolynomialSymbol w →ₗ⁅ℚ⁆ F.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.quotientTop.filteredPolynomialSymbolMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem w

noncomputable def reducedSquareDiagonalSymbolMap :
    F.quotientTop.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.quotientTop.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    F.reducedSquareDiagonal F.reducedSquareDiagonal_mem w

@[simp] theorem reducedSquareSndSymbolMap_symbol
    (r : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareSndSymbolMap w (F.squareFiltration.quotientTop.polynomialSymbolMap w r) =
      F.quotientTop.polynomialSymbolMap w (F.reducedSquareSndPolynomialMap w r) := rfl

@[simp] theorem reducedSquareDiagonalSymbolMap_symbol (p : F.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareDiagonalSymbolMap w (F.quotientTop.polynomialSymbolMap w p) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquareDiagonalPolynomialMap w p) := rfl

@[simp] theorem reducedSquareSndPolynomialMap_diagonal (p : F.quotientTop.adaptedLieSubalgebra w) :
    F.reducedSquareSndPolynomialMap w (F.reducedSquareDiagonalPolynomialMap w p) = p := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  simp only [reducedSquareSndPolynomialMap, reducedSquareDiagonalPolynomialMap,
    filteredPolynomialMap_coefficient, F.reducedSquareSnd_diagonal]

@[simp] theorem reducedSquareSndSymbolMap_diagonal (x : F.quotientTop.PolynomialSymbol w) :
    F.reducedSquareSndSymbolMap w (F.reducedSquareDiagonalSymbolMap w x) = x := by
  obtain ⟨p, rfl⟩ := F.quotientTop.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareDiagonalSymbolMap_symbol, F.reducedSquareSndSymbolMap_symbol,
    F.reducedSquareSndPolynomialMap_diagonal]

theorem reducedSquareSndPolynomialMap_quotient (p : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSndPolynomialMap w (F.reducedSquarePolynomialMap w p) =
      F.quotientTopPolynomialMap w (F.squareSndPolynomialMap w p) := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  change coefficients (VectorPolynomial.map F.reducedSquareSnd.toLinearMap
      (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap p.val)) α =
    coefficients (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap
      (VectorPolynomial.map F.squareSnd.toLinearMap p.val)) α
  simp only [coefficients_map]
  rfl

theorem reducedSquareDiagonalPolynomialMap_quotient (p : F.adaptedLieSubalgebra w) :
    F.reducedSquareDiagonalPolynomialMap w (F.quotientTopPolynomialMap w p) =
      F.reducedSquarePolynomialMap w (F.squareDiagonalPolynomialMap w p) := by
  apply Subtype.ext
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  change coefficients (VectorPolynomial.map F.reducedSquareDiagonal.toLinearMap
      (VectorPolynomial.map (lieQuotientMap (F.layerIdeal (s + 1))).toLinearMap p.val)) α =
    coefficients (VectorPolynomial.map (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))).toLinearMap
      (VectorPolynomial.map F.squareDiagonalLie.toLinearMap p.val)) α
  simp only [coefficients_map]
  rfl

theorem reducedSquareSndSymbolMap_quotient (x : F.squareFiltration.PolynomialSymbol w) :
    F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolMap w x) =
      F.quotientTopSymbolMap w (F.squareSndSymbolMap w x) := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.polynomialSymbolMap_surjective w x
  rw [F.reducedSquareSymbolMap_symbol, F.reducedSquareSndSymbolMap_symbol,
    F.squareSndSymbolMap_symbol, F.quotientTopSymbolMap_symbol,
    F.reducedSquareSndPolynomialMap_quotient]

theorem reducedSquareDiagonalSymbolMap_quotient (x : F.PolynomialSymbol w) :
    F.reducedSquareDiagonalSymbolMap w (F.quotientTopSymbolMap w x) =
      F.reducedSquareSymbolMap w (F.squareDiagonalSymbolMap w x) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.quotientTopSymbolMap_symbol, F.reducedSquareDiagonalSymbolMap_symbol,
    F.squareDiagonalSymbolMap_symbol, F.reducedSquareSymbolMap_symbol,
    F.reducedSquareDiagonalPolynomialMap_quotient]

theorem reducedSquareSymbolMap_surjective : Function.Surjective (F.reducedSquareSymbolMap w) :=
  F.squareFiltration.quotientTopSymbolMap_surjective w

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev ReducedSquareBasisIndex (s : ℕ) (ω : ι → ℕ) :=
  QuotientTopBasisIndex s (squareBasisWeight ω)

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def reducedSquareBasis :
    Basis (ReducedSquareBasisIndex s ω) ℚ
      (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :=
  F.squareFiltration.quotientTopBasis (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF)

theorem reducedSquareBasis_layers (j : ℕ) :
    F.squareFiltration.quotientTop.layer j = Submodule.span ℚ
      (F.reducedSquareBasis e ω hF '' {i | j ≤ squareBasisWeight ω i.val}) :=
  F.squareFiltration.quotientTopBasis_layers (F.adaptedSquareBasis e ω (hF 2))
    (squareBasisWeight ω) (F.adaptedSquareBasis_layers e ω hF) j

theorem reducedSquareSnd_basis_height
    (a : ReducedSquareBasisIndex s ω) (b : QuotientTopBasisIndex s ω) :
    RationalHeightLE ((F.quotientTopBasis e ω hF).repr
      (F.reducedSquareSnd (F.reducedSquareBasis e ω hF a)) b) 1 := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareSnd_mk, F.quotientTopBasis_repr_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i =>
    change RationalHeightLE (e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inl i)).val.2) b.val) 1
    rw [F.adaptedSquareBasis_inl]
    exact basis_repr_height_one e i b.val
  | inr i =>
    change RationalHeightLE (e.repr ((F.adaptedSquareBasis e ω (hF 2) (Sum.inr i)).val.2) b.val) 1
    rw [F.adaptedSquareBasis_inr, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev QuotientTopSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :=
  SymbolBasisIndex w (fun i : QuotientTopBasisIndex s ω => ω i.val)

abbrev ReducedSquareSymbolIndex (s : ℕ) (w : σ → ℕ) (ω : ι → ℕ) :=
  SymbolBasisIndex w (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val)

variable (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def quotientTopSymbolBasis :
    Basis (QuotientTopSymbolIndex s w ω) ℚ (F.quotientTop.PolynomialSymbol w) :=
  F.quotientTop.polynomialSymbolBasis (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w

noncomputable def reducedSquareSymbolBasis :
    Basis (ReducedSquareSymbolIndex s w ω) ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  F.squareFiltration.quotientTop.polynomialSymbolBasis (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w

theorem reducedSquareSndSymbolMap_basis_height
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω) :
    RationalHeightLE ((F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b) 1 :=
  filteredPolynomialSymbolMap_basis_height F.squareFiltration.quotientTop F.quotientTop
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w le_rfl
    (fun i j => F.reducedSquareSnd_basis_height e ω hF j i) a b

theorem reducedSquareSndSymbolMap_monomial_blocks
    (a : ReducedSquareSymbolIndex s w ω) (b : QuotientTopSymbolIndex s w ω)
    (hab : b.val.1 ≠ a.val.1) :
    (F.quotientTopSymbolBasis e ω hF w).repr
      (F.reducedSquareSndSymbolMap w (F.reducedSquareSymbolBasis e ω hF w a)) b = 0 :=
  filteredPolynomialSymbolMap_monomial_blocks F.squareFiltration.quotientTop F.quotientTop
    (F.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
    (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w a b hab

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adaptedSquareBasis_structure_bound (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (i j k : ι ⊕ {i // 2 ≤ w i}) :
    rationalLogHeight (lieStructureConstants (F.adaptedSquareBasis b w h) i j k) ≤
      (p + 2) ^ 11 := by
  classical
  have hB (i j) : RationalHeightLE
      (LinearMap.toMatrix (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
        F.squarePairMap.toLinearMap i j) H := by
    rw [LinearMap.toMatrix_apply]
    exact (F.adaptedSquareBasis_pairMap_height b w h i j).mono hH
  obtain ⟨_, _, _, hbr⟩ := exists_bounded_lie_embedding_retraction
    (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
    F.squarePairMap F.squarePairMap_injective hH
    (lie_pi_structure_height (fun _ : Bool => b) hH (fun _ => hc))
    hB
  apply rationalLogHeight_le_of_height (hbr i j k)
  apply rationalLieStructureHeight_inverse_budget _ _ _ hp
  · simpa only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_bool, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hd
  · exact (Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
  · exact hHp

theorem exists_adaptedSquareBasis_grid (b : Basis ι ℚ L) (w : ι → ℕ)
    (h : F.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    (Γ : Subgroup F.Group) {l : ℕ} (hl : 0 < l)
    (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : 2 * (Fintype.card ι : ℝ) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (F.adaptedSquareBasis b w h) (F.squareLattice Γ) ∧
      bchSubgroupCoordinates (F.adaptedSquareBasis b w h) (F.squareLattice Γ) ⊆
        denominatorGrid N := by
  classical
  have hB (i j) : RationalHeightLE
      (LinearMap.toMatrix (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
        F.squarePairMap.toLinearMap i j) 1 := by
    rw [LinearMap.toMatrix_apply]
    exact F.adaptedSquareBasis_pairMap_height b w h i j
  rw [F.squareLattice_eq_pair_comap]
  apply exists_bchSubgroup_comap_grid_exp_bound
    (F.adaptedSquareBasis b w h) (Pi.basis (fun _ : Bool => b))
    F.squarePairMap F.squarePairMap_injective _ (H := 1) le_rfl hl
    hB
    (piBCHSubgroup_inner_grid (fun _ : Bool => F) (fun _ => b) (fun _ => Γ) l
      (fun _ => hin))
    (piBCHSubgroup_outer_grid (fun _ : Bool => F) (fun _ => b) (fun _ => Γ) l
      (fun _ => hout)) hp
  · simpa only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_bool, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hd
  · exact (Nat.cast_le.mpr (card_squareBasis_index_le w)).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · exact hlp

end Erdos3.NilpotentLieFiltration

end

end OAI
