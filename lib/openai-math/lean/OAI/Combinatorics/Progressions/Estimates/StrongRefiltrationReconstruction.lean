import OAI.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
import OAI.Combinatorics.Progressions.Estimates.RealifiedTopQuotient

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

theorem symbolPointwiseSubalgebra_mono {U V : LieSubalgebra ℚ F.AssociatedGraded} (hUV : U ≤ V) :
    F.symbolPointwiseSubalgebra e ω hF w U ≤ F.symbolPointwiseSubalgebra e ω hF w V := by
  intro x hx
  exact fun α => hUV ((F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α)

theorem symbolPointwiseSubalgebra_map_le (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.symbolPointwiseSubalgebra e ω hF w U).map (F.filteredPolynomialSymbolMap G φ hφ w) ≤
      G.symbolPointwiseSubalgebra f ν hG w (U.map (F.associatedGradedMap G φ hφ)) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (G.mem_symbolPointwiseSubalgebra_iff f ν hG w _ _).mpr
  intro α
  simp only [LieHom.coe_toLinearMap]
  have hm : F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) ∈
      U.map (F.associatedGradedMap G φ hφ) :=
    ⟨_, (F.mem_symbolPointwiseSubalgebra_iff e ω hF w U x).mp hx α, rfl⟩
  rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α]
  exact hm

theorem symbolPointwiseSubalgebra_comap (U : LieSubalgebra ℚ G.AssociatedGraded) :
    (G.symbolPointwiseSubalgebra f ν hG w U).comap (F.filteredPolynomialSymbolMap G φ hφ w) =
      F.symbolPointwiseSubalgebra e ω hF w (U.comap (F.associatedGradedMap G φ hφ)) := by
  ext x
  constructor
  · intro hx
    simp only [LieSubalgebra.mem_comap] at hx
    apply (F.mem_symbolPointwiseSubalgebra_iff e ω hF w _ x).mpr
    intro α
    have hm := (G.mem_symbolPointwiseSubalgebra_iff f ν hG w U
      (F.filteredPolynomialSymbolMap G φ hφ w x)).mp hx α
    rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α] at hm
    exact hm
  · intro hx
    simp only [LieSubalgebra.mem_comap]
    apply (G.mem_symbolPointwiseSubalgebra_iff f ν hG w U _).mpr
    intro α
    have hm : F.associatedGradedMap G φ hφ (coefficients (F.gradedSymbolPolynomial e ω hF w x) α) ∈ U :=
      (F.mem_symbolPointwiseSubalgebra_iff e ω hF w _ x).mp hx α
    rw [F.gradedSymbolPolynomial_filteredMap_coefficient G e ω hF f ν hG φ hφ w x α]
    exact hm

theorem symbolPointwiseSubalgebra_map [Fintype (SymbolBasisIndex w ν)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    (F.symbolPointwiseSubalgebra e ω hF w U).map (F.filteredPolynomialSymbolMap G φ hφ w) =
      G.symbolPointwiseSubalgebra f ν hG w (U.map (F.associatedGradedMap G φ hφ)) := by
  classical
  apply le_antisymm (F.symbolPointwiseSubalgebra_map_le G e ω hF f ν hG φ hφ w U)
  intro x hx
  change x ∈ ((F.symbolPointwiseSubalgebra e ω hF w U).map
    (F.filteredPolynomialSymbolMap G φ hφ w)).toSubmodule
  rw [← sum_basisBlockProjection (G.polynomialSymbolBasis f ν hG w) (fun z => z.val.1) x]
  apply Submodule.sum_mem
  intro α _
  obtain ⟨v, hv, he⟩ := (G.mem_symbolPointwiseSubalgebra_iff f ν hG w _ x).mp hx α
  refine ⟨F.homogeneousSymbolLift e ω hF w α v,
    F.homogeneousSymbolLift_mem_pointwise e ω hF w U hU α v hv, ?_⟩
  change F.filteredPolynomialSymbolMap G φ hφ w (F.homogeneousSymbolLift e ω hF w α v) = _
  change F.associatedGradedMap G φ hφ v = _ at he
  rw [F.homogeneousSymbolLift_filteredMap G e ω hF f ν hG φ hφ w, he,
    G.homogeneousSymbolLift_coefficient]

theorem associatedGradedMap_image_graded (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    BasisGradedSubmodule (G.associatedGradedBasis f ν hG) ν
      (U.map (F.associatedGradedMap G φ hφ)).toSubmodule := by
  rintro j _ ⟨x, hx, rfl⟩
  exact ⟨basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x, hU j x hx,
    F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ j x⟩

theorem associatedGradedMap_comap_graded (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hU : BasisGradedSubmodule (G.associatedGradedBasis f ν hG) ν U.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω
      (U.comap (F.associatedGradedMap G φ hφ)).toSubmodule := by
  intro j x hx
  change F.associatedGradedMap G φ hφ
    (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x) ∈ U
  rw [F.associatedGradedMap_gradeProjection G e ω hF f ν hG φ hφ]
  exact hU j _ hx

end Erdos3.NilpotentLieFiltration

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} {H : Type u} {L : ι → Type u}
  [LieRing H] [LieAlgebra ℚ H] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem quotient_markedDiagram_injective {s : ℕ}
    (E : NilpotentLieFiltration H (s + 1)) (ψ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (hker : ∀ x : H, x ∈ E.layer (s + 1) → (∀ i, ψ i x = 0) → x = 0) :
    Function.Injective (optionProductMap (lieQuotientMap (E.layerIdeal (s + 1))) ψ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker (x - y)
  · have hq : lieQuotientMap (E.layerIdeal (s + 1)) x =
        lieQuotientMap (E.layerIdeal (s + 1)) y := congrFun hxy none
    apply (E.mem_layerIdeal (s + 1) (x - y)).mp
    apply (lieQuotientMap_eq_zero (E.layerIdeal (s + 1)) (x - y)).mp
    rw [map_sub, hq, sub_self]
  · intro i
    have hi : ψ i x = ψ i y := congrFun hxy (some i)
    rw [map_sub, hi, sub_self]

theorem refiltered_markedDiagram_injective
    {A : Type u} [LieRing A] [LieAlgebra ℚ A] {s d e : ℕ}
    (D : RationalFilteredNilmanifold A (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W)
      (s + 1) e)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (χ : ∀ i, A →ₗ⁅ℚ⁆ L i)
    (hker : ∀ x : A, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) →
      (∀ i, χ i x = 0) → x = 0) :
    Function.Injective (optionProductMap
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
      (fun i => (χ i).comp (D.filtration.gradedRefiltrationSubalgebra W).incl)) := by
  apply quotient_markedDiagram_injective
  intro x hx hχ
  apply Subtype.ext
  apply hker (x : A)
  · rw [hEF] at hx
    exact (D.filtration.mem_gradedRefiltration_layer W (s + 1) x).mp hx
  · exact hχ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration
open Module
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j) (w : σ → ℕ)

 theorem real_symbolPointwiseSubalgebra_map_mem
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x ∈
      realificationLieSubalgebra
        (G.symbolPointwiseSubalgebra c ν hG w (U.map (F.associatedGradedMap G φ hφ))) := by
  have hmap : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x ∈
      realificationLieSubalgebra ((F.symbolPointwiseSubalgebra b ω hF w U).map
        (F.filteredPolynomialSymbolMap G φ hφ w)) := by
    rw [realificationLieSubalgebra_map]
    exact ⟨x, hx, rfl⟩
  exact Submodule.baseChange_mono ℝ
    (F.symbolPointwiseSubalgebra_map_le G b ω hF c ν hG φ hφ w U) hmap

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

theorem homogeneousGradedProjection_image_eq
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (W.map (F.associatedGradedMap G φ hφ)).map
      (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLieHom =
      W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem projected_realSymbolRepresentative_mem_homogeneous_image
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (u : σ → ℝ) :
    eval₂ u (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) ∈
      realificationLieSubalgebra (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)) := by
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W x hx
  have hvalue := (G.mem_real_symbolPointwiseSubalgebra_iff_values c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)).mp hmap u
  rw [G.realSymbolRepresentative_eval₂,
    ← F.homogeneousGradedProjection_image_eq G c ν hG hc φ hφ W,
    realificationLieSubalgebra_map]
  exact ⟨_, hvalue, rfl⟩

theorem projected_realSymbolRepresentative_coefficients_mem_homogeneous_image
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (α : σ →₀ ℕ) :
    coefficients (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α ∈
      realificationLieSubalgebra (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)) := by
  have hmap := F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ w W x hx
  have hcoeff := (G.mem_real_symbolPointwiseSubalgebra_iff_coefficients c ν hG w
    (W.map (F.associatedGradedMap G φ hφ))
    (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)).mp hmap α
  rw [G.realSymbolRepresentative_coefficient_splitting,
    ← F.homogeneousGradedProjection_image_eq G c ν hG hc φ hφ W,
    realificationLieSubalgebra_map]
  exact ⟨_, hcoeff, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (b : Basis κ ℚ M) (ν : κ → ℕ)
  (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

include b ν hG in

theorem gradedRefiltrationLayer_map (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) (j : ℕ) :
    (F.gradedRefiltrationLayer U j).map φ.toLinearMap =
      G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) j := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U j x).mp hx
    apply (G.mem_gradedRefiltrationLayer _ j (φ x)).mpr
    refine ⟨hφ j x hxF, F.associatedGradedPieceMap j ⟨x, hxF⟩, hxU, ?_⟩
    exact F.associatedGradedMap_piece G φ hφ j ⟨x, hxF⟩
  · intro y hy
    obtain ⟨hyG, hyU⟩ := (G.mem_gradedRefiltrationLayer _ j y).mp hy
    obtain ⟨a, ha, haeq⟩ := hyU
    change F.associatedGradedMap G φ hφ a = G.associatedGradedPieceMap j ⟨y, hyG⟩ at haeq
    let a' := basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a
    have ha'U : a' ∈ U := hU j a ha
    have ha'pure : basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a' = a' := by
      apply (F.associatedGradedBasis e ω hF).repr.injective
      ext i
      simp only [a', basisGradeProjection_repr]
      split_ifs <;> rfl
    obtain ⟨x, hx⟩ := F.exists_associatedGradedPieceMap_of_pure e ω hF j a' ha'pure
    have hgraded : F.associatedGradedMap G φ hφ (F.associatedGradedPieceMap j x) =
        G.associatedGradedPieceMap j ⟨y, hyG⟩ := by
      rw [hx]
      change F.associatedGradedMap G φ hφ
        (basisGradeProjection (F.associatedGradedBasis e ω hF) ω j a) = _
      rw [F.associatedGradedMap_gradeProjection G e ω hF b ν hG φ hφ, haeq]
      exact G.associatedGradedPieceMap_grade_fixed b ν hG j ⟨y, hyG⟩
    have hδ : y - φ x ∈ G.layer (j + 1) := by
      apply (G.associatedGradedPieceMap_eq_zero_iff j
        ⟨y - φ x, (G.layer j).sub_mem hyG (hφ j x x.property)⟩).mp
      change G.associatedGradedPieceMap j
        (⟨y, hyG⟩ - ⟨φ x, hφ j x x.property⟩) = 0
      rw [map_sub, ← F.associatedGradedMap_piece G φ hφ j x, hgraded, sub_self]
    obtain ⟨z, hz, hzeq⟩ := hsurj (j + 1) (y - φ x) hδ
    refine ⟨(x : L) + z, (F.gradedRefiltrationLayer U j).add_mem ?_
      (F.layer_succ_le_gradedRefiltrationLayer U j hz), ?_⟩
    · exact (F.mem_gradedRefiltrationLayer U j x).mpr ⟨x.property, hx.symm ▸ ha'U⟩
    · change φ ((x : L) + z) = y
      rw [map_add, hzeq]
      abel

theorem gradedRefiltrationLayer_top_kernel_eq_zero
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)
    (x : L) (hx : x ∈ F.gradedRefiltrationLayer U s) (hzero : φ x = 0) : x = 0 := by
  obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U s x).mp hx
  have hpiece : F.associatedGradedPieceMap s ⟨x, hxF⟩ = 0 := by
    apply htop _ hxU (F.associatedGradedPieceMap_grade_fixed e ω hF s ⟨x, hxF⟩)
    rw [F.associatedGradedMap_piece]
    have he : (⟨φ x, hφ s x hxF⟩ : G.layer s) = 0 := Subtype.ext hzero
    rw [he, map_zero]
  have hmem := (F.associatedGradedPieceMap_eq_zero_iff s ⟨x, hxF⟩).mp hpiece
  rw [F.terminal] at hmem
  exact hmem

theorem gradedRefiltrationLayer_map_mem (U : LieSubalgebra ℚ F.AssociatedGraded)
    (j : ℕ) (x : L) (hx : x ∈ F.gradedRefiltrationLayer U j) :
    φ x ∈ G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) j := by
  obtain ⟨hxF, hxU⟩ := (F.mem_gradedRefiltrationLayer U j x).mp hx
  apply (G.mem_gradedRefiltrationLayer _ j (φ x)).mpr
  exact ⟨hφ j x hxF, F.associatedGradedPieceMap j ⟨x, hxF⟩, hxU,
    F.associatedGradedMap_piece G φ hφ j ⟨x, hxF⟩⟩

noncomputable def gradedRefiltrationMap (U : LieSubalgebra ℚ F.AssociatedGraded) :
    F.gradedRefiltrationSubalgebra U →ₗ⁅ℚ⁆
      G.gradedRefiltrationSubalgebra (U.map (F.associatedGradedMap G φ hφ)) where
  toLinearMap :=
    { toFun x := ⟨φ x, F.gradedRefiltrationLayer_map_mem G φ hφ U 1 x x.property⟩
      map_add' x y := Subtype.ext (map_add φ (x : L) (y : L))
      map_smul' a x := Subtype.ext (map_smul φ a (x : L)) }
  map_lie' {x y} := Subtype.ext (LieHom.map_lie φ x y)

@[simp] theorem gradedRefiltrationMap_apply (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.gradedRefiltrationSubalgebra U) :
    (F.gradedRefiltrationMap G φ hφ U x : M) = φ x := rfl

theorem gradedRefiltrationMap_mem_layer (U : LieSubalgebra ℚ F.AssociatedGraded)
    (j : ℕ) (x : F.gradedRefiltrationSubalgebra U)
    (hx : x ∈ (F.gradedRefiltration U).layer j) :
    F.gradedRefiltrationMap G φ hφ U x ∈
      (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j :=
  F.gradedRefiltrationLayer_map_mem G φ hφ U j x hx

include e ω hF b ν hG in

theorem gradedRefiltrationMap_layer_surjective (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (j : ℕ) (y : G.gradedRefiltrationSubalgebra (U.map (F.associatedGradedMap G φ hφ)))
    (hy : y ∈ (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j) :
    ∃ x ∈ (F.gradedRefiltration U).layer j, F.gradedRefiltrationMap G φ hφ U x = y := by
  have lift (i : ℕ) (hi : 1 ≤ i)
      (hy' : (y : M) ∈ G.gradedRefiltrationLayer (U.map (F.associatedGradedMap G φ hφ)) i) :
      ∃ x ∈ (F.gradedRefiltration U).layer i, F.gradedRefiltrationMap G φ hφ U x = y := by
    rw [← F.gradedRefiltrationLayer_map G e ω hF b ν hG φ hφ U hU hsurj] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    let x' : F.gradedRefiltrationSubalgebra U :=
      ⟨x, F.gradedRefiltrationLayer_antitone U hi hx⟩
    exact ⟨x', hx, Subtype.ext hxy⟩
  by_cases hj : 1 ≤ j
  · exact lift j hj hy
  · have hj0 : j = 0 := by omega
    subst j
    obtain ⟨x, hx, hxy⟩ := lift 1 le_rfl y.property
    exact ⟨x, (F.gradedRefiltration U).antitone (by omega : 0 ≤ 1) hx, hxy⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

universe u

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)

theorem allocatedMarkedDiagram_injective_of_top_kernel
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (hker : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) →
      φ x = 0 → x = 0) :
    Function.Injective (optionProductMap
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (fun _ : Unit => D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)) := by
  apply quotient_markedDiagram_injective
  intro x hx hzero
  apply Subtype.ext
  apply hker (x : L)
  · rw [hDref] at hx
    exact (D.filtration.mem_gradedRefiltration_layer W (s + 1) x).mp hx
  · exact congrArg Subtype.val (hzero ())

theorem allocatedMarkedDiagram_injective_of_graded_top
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    {ι : Type*} (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (htop : ∀ a ∈ W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hD) ω (s + 1) a = a →
      D.filtration.associatedGradedMap Fmark.filtration φ hφ a = 0 → a = 0) :
    Function.Injective (optionProductMap
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (fun _ : Unit => D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)) :=
  D.allocatedMarkedDiagram_injective_of_top_kernel Fmark φ hφ W Dref hDref
    (D.filtration.gradedRefiltrationLayer_top_kernel_eq_zero
      Fmark.filtration b ω hD φ hφ W htop)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.quotientLie
    (D.filtration.pivotAnnihilatorIdeal π eta js)
    (by rw [D.filtration.terminal]; exact bot_le))

include hQ

theorem optionNativePivotQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option J, optionLieSpace L M i)
    (hx : x ∈ (optionProduct D E).filtration.layer k) :
    optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)) x ∈
        (optionProduct Q E).filtration.layer k := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mp hx
  apply (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k _).mpr
  intro i
  cases i with
  | none =>
    change lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) (x none) ∈
      Q.filtration.layer k
    rw [hQ]
    exact ⟨x none, hcoord none, rfl⟩
  | some j => exact hcoord (some j)

theorem optionNativePivotQuotientMap_layer_surjective (k : ℕ)
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.layer k) :
    ∃ x ∈ (optionProduct D E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)) x = y := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k y).mp hy
  have hy₀ : y none ∈ Q.filtration.layer k := hcoord none
  rw [hQ] at hy₀
  obtain ⟨x₀, hx₀, hxy₀⟩ := hy₀
  let x : ∀ i : Option J, optionLieSpace L M i
    | none => x₀
    | some j => y (some j)
  refine ⟨x, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mpr
    intro i
    cases i with
    | none => exact hx₀
    | some j => exact hcoord (some j)
  · funext i
    cases i with
    | none => exact hxy₀
    | some j => rfl

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

noncomputable def optionNativeCommonPivotQuotientFast :
    LieSubalgebra ℚ (optionProduct Q E).filtration.AssociatedGraded :=
  U.map ((optionProduct D E).filtration.associatedGradedMap
    (optionProduct Q E).filtration
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ))

variable {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hSource : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (c : Basis κQ ℚ (∀ i : Option J,
    optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i))
  (ν : κQ → ℕ)
  (hTarget : ∀ k, (optionProduct Q E).filtration.layer k =
    Submodule.span ℚ (c '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule
    ((optionProduct D E).filtration.associatedGradedBasis e μ hSource) μ U.toSubmodule)

include e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_layer_eq (k : ℕ) :
    (optionProduct Q E).filtration.gradedRefiltrationLayer
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U) k =
    ((optionProduct D E).filtration.gradedRefiltrationLayer U k).map
      (optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js))).toLinearMap := by
  symm
  exact (optionProduct D E).filtration.gradedRefiltrationLayer_map
    (optionProduct Q E).filtration e μ hSource c ν hTarget
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ) U hU
    (optionNativePivotQuotientMap_layer_surjective D E π eta js Q hQ) k

include e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_graded :
    BasisGradedSubmodule
      ((optionProduct Q E).filtration.associatedGradedBasis c ν hTarget) ν
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U).toSubmodule :=
  (optionProduct D E).filtration.associatedGradedMap_image_graded
    (optionProduct Q E).filtration e μ hSource c ν hTarget
    (optionMarkedLieMap (L := M)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)))
    (optionNativePivotQuotientMap_mem_layer D E π eta js Q hQ) U hU

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable abbrev refilteredProjectionFiberProduct :=
  lieQuotientFiberProduct ((F.gradedRefiltration U).layerIdeal s)
    ((G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layerIdeal s)
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U s)

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω s a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)

noncomputable def refilteredProjectionFiberEquiv :
    F.gradedRefiltrationSubalgebra U ≃ₗ⁅ℚ⁆ F.refilteredProjectionFiberProduct G φ hφ U :=
  (F.gradedRefiltration U).quotientFiberEquiv
    (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ)))
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U)
    (fun x hx hz => Subtype.ext
      (F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop x hx
        (congrArg Subtype.val hz)))
    (F.gradedRefiltrationMap_layer_surjective G e ω hF b ν hG φ hφ U hU hsurj s)

@[simp] theorem refilteredProjectionFiberEquiv_apply
    (x : F.gradedRefiltrationSubalgebra U) :
    (F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop x).val =
      (lieQuotientMap ((F.gradedRefiltration U).layerIdeal s) x,
        F.gradedRefiltrationMap G φ hφ U x) := rfl

theorem refilteredProjectionFiberEquiv_symm_components
    (z : F.refilteredProjectionFiberProduct G φ hφ U) :
    let x := (F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop).symm z
    lieQuotientMap ((F.gradedRefiltration U).layerIdeal s) x = z.val.1 ∧
      F.gradedRefiltrationMap G φ hφ U x = z.val.2 := by
  intro x
  have hz := congrArg Subtype.val
    ((F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop).apply_symm_apply z)
  exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩

theorem refilteredProjectionFiberEquiv_layer_surjective
    (j : ℕ) (z : F.refilteredProjectionFiberProduct G φ hφ U)
    (hq : z.val.1 ∈ ((F.gradedRefiltration U).layer j).map
      (lieQuotientMap ((F.gradedRefiltration U).layerIdeal s)).toLinearMap)
    (hp : z.val.2 ∈
      (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j) :
    ∃ x ∈ (F.gradedRefiltration U).layer j,
      F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop x = z := by
  exact (F.gradedRefiltration U).quotientFiberEquiv_layer_surjective
    (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ)))
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U)
    (fun x hx hz => Subtype.ext
      (F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop x hx
        (congrArg Subtype.val hz)))
    (F.gradedRefiltrationMap_layer_surjective G e ω hF b ν hG φ hφ U hU hsurj s) j z hq hp

theorem refilteredProjectionFiberEquiv_mem_layer_iff
    (j : ℕ) (x : F.gradedRefiltrationSubalgebra U) :
    x ∈ (F.gradedRefiltration U).layer j ↔
      (F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop x).val.1 ∈
        ((F.gradedRefiltration U).layer j).map
          (lieQuotientMap ((F.gradedRefiltration U).layerIdeal s)).toLinearMap ∧
      (F.refilteredProjectionFiberEquiv G φ hφ U e ω hF b ν hG hU hsurj htop x).val.2 ∈
        (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layer j := by
  exact (F.gradedRefiltration U).mem_layer_iff_quotient_and_projection
    (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ)))
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U)
    (fun y hy hz => Subtype.ext
      (F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop y hy
        (congrArg Subtype.val hz))) j x

end Erdos3.NilpotentLieFiltration

end

end OAI
