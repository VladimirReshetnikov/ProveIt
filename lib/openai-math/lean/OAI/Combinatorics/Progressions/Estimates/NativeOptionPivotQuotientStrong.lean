import OAI.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
import OAI.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget

namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

noncomputable def optionPivotProductQuotientMap :
    (∀ i : Option J, optionLieSpace L M i) →ₗ⁅ℚ⁆
      (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j) :=
  ((lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js)).comp
    (liePiEval none)).prod (liePiMap (fun j => liePiEval (some j)))

@[simp] theorem optionPivotProductQuotientMap_fst
    (x : ∀ i : Option J, optionLieSpace L M i) :
    (optionPivotProductQuotientMap D π eta js x).1 =
      lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) (x none) := rfl

@[simp] theorem optionPivotProductQuotientMap_snd
    (x : ∀ i : Option J, optionLieSpace L M i) (j : J) :
    (optionPivotProductQuotientMap D π eta js x).2 j = x (some j) := rfl

variable [Fintype J]

theorem optionPivotProductQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option J, optionLieSpace L M i)
    (hx : x ∈ (optionProduct D E).filtration.layer k) :
    optionPivotProductQuotientMap D π eta js x ∈
      (D.filtration.pivotProductQuotientFiltration π eta js
        (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mp hx
  refine ⟨⟨x none, hcoord none, rfl⟩, ?_⟩
  exact (mem_pi_layer (fun j => (E j).filtration) k _).mpr (fun j => hcoord (some j))

theorem optionPivotProductQuotientMap_layer_surjective (k : ℕ)
    (y : (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j))
    (hy : y ∈ (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k) :
    ∃ x ∈ (optionProduct D E).filtration.layer k,
      optionPivotProductQuotientMap D π eta js x = y := by
  obtain ⟨x₀, hx₀, hxy₀⟩ := hy.1
  let x : ∀ i : Option J, optionLieSpace L M i
    | none => x₀
    | some j => y.2 j
  refine ⟨x, ?_, Prod.ext hxy₀ rfl⟩
  apply (mem_pi_layer (fun i => (optionFactors D E i).filtration) k x).mpr
  intro i
  cases i with
  | none => exact hx₀
  | some j => exact (mem_pi_layer (fun j => (E j).filtration) k y.2).mp hy.2 j

variable (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)

noncomputable def optionCommonPivotQuotientFast :
    LieSubalgebra ℚ (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))).AssociatedGraded :=
  U.map ((optionProduct D E).filtration.associatedGradedMap
    (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration)))
    (optionPivotProductQuotientMap D π eta js)
    (optionPivotProductQuotientMap_mem_layer D E π eta js))

variable (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (hzero : ∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer U s →
    realifyFunctional ((pairFrequency (eta j) (theta j)).comp
      (optionPairProjection j).toLinearMap) x = 0)

include hzero in

theorem optionCommonFastTop_quotient_le :
    ((optionProduct D E).filtration.gradedRefiltrationLayer U s).map
      (optionPivotProductQuotientMap D π eta js).toLinearMap ≤
      D.filtration.joinedFrequencyQuotientTop π eta js
        (fun j => (theta j).comp (LinearMap.proj j)) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(x none, fun j => x (some j)), ?_, rfl⟩
  apply (D.filtration.mem_joinedFrequencyTop eta js _ _).mpr
  refine ⟨?_, ?_⟩
  · exact (mem_pi_layer (fun i => (optionFactors D E i).filtration) s x).mp
      ((optionProduct D E).filtration.gradedRefiltrationLayer_le U s hx) none
  · intro j _
    change eta j (x none) + theta j (x (some j)) = 0
    have hz := (optionProduct D E).filtration.frequency_zero_on_refilteredLayer_of_real
      U ((pairFrequency (eta j) (theta j)).comp (optionPairProjection j).toLinearMap)
      s (hzero j) x hx
    simpa only [LinearMap.comp_apply, LieHom.coe_toLinearMap, pairFrequency_apply,
      optionPairProjection_true, optionPairProjection_false, LinearMap.proj_apply] using hz

variable {κ κQ : Type*}
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hH : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (q : Basis κQ ℚ ((L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j)))
  (ν : κQ → ℕ)
  (hQ : ∀ k, (D.filtration.pivotProductQuotientFiltration π eta js
    (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k =
      Submodule.span ℚ (q '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e μ hH)
    μ U.toSubmodule)

include e μ hH q ν hQ hU in

theorem optionCommonPivotQuotientFast_layer_eq (k : ℕ) :
    (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))).gradedRefiltrationLayer
        (optionCommonPivotQuotientFast D E π eta js U) k =
    ((optionProduct D E).filtration.gradedRefiltrationLayer U k).map
      (optionPivotProductQuotientMap D π eta js).toLinearMap := by
  symm
  exact (optionProduct D E).filtration.gradedRefiltrationLayer_map
    (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))) e μ hH q ν hQ
    (optionPivotProductQuotientMap D π eta js)
    (optionPivotProductQuotientMap_mem_layer D E π eta js)
    U hU (optionPivotProductQuotientMap_layer_surjective D E π eta js) k

include e μ hH q ν hQ hU in
theorem optionCommonPivotQuotientFast_graded :
    BasisGradedSubmodule
      ((D.filtration.pivotProductQuotientFiltration π eta js
        (NilpotentLieFiltration.pi (fun j => (E j).filtration))).associatedGradedBasis q ν hQ) ν
      (optionCommonPivotQuotientFast D E π eta js U).toSubmodule :=
  (optionProduct D E).filtration.associatedGradedMap_image_graded
    (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))) e μ hH q ν hQ
    (optionPivotProductQuotientMap D π eta js)
    (optionPivotProductQuotientMap_mem_layer D E π eta js) U hU

include hzero e μ hH q ν hQ hU in
theorem optionCommonPivotQuotientFast_top_le :
    (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))).gradedRefiltrationLayer
        (optionCommonPivotQuotientFast D E π eta js U) s ≤
      D.filtration.joinedFrequencyQuotientTop π eta js
        (fun j => (theta j).comp (LinearMap.proj j)) := by
  rw [optionCommonPivotQuotientFast_layer_eq D E π eta js U e μ hH q ν hQ hU s]
  exact optionCommonFastTop_quotient_le D E π eta js U theta hzero

include hzero e μ hH q ν hQ hU in

theorem optionCommonPivotQuotientFast_top_kernel_eq_zero
    (x : (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j))
    (hx : x ∈ (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))).gradedRefiltrationLayer
        (optionCommonPivotQuotientFast D E π eta js U) s)
    (hkernel : D.filtration.pivotProductMarkedMap π eta js x = 0) : x = 0 :=
  D.filtration.joinedFrequencyQuotientTop_kernel_eq_zero π eta js
    (fun j => (theta j).comp (LinearMap.proj j)) x
    (optionCommonPivotQuotientFast_top_le D E π eta js U theta hzero e μ hH q ν hQ hU hx)
    hkernel

include hzero e μ hH q ν hQ hU in

theorem optionCommonPivotQuotientFast_graded_top_kernel
    (G : NilpotentLieFiltration (Y × (∀ j, M j)) s)
    (hmarked : ∀ k, ∀ x ∈ (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k,
      D.filtration.pivotProductMarkedMap π eta js x ∈ G.layer k) :
    ∀ a ∈ optionCommonPivotQuotientFast D E π eta js U,
      basisGradeProjection
        ((D.filtration.pivotProductQuotientFiltration π eta js
          (NilpotentLieFiltration.pi (fun j => (E j).filtration))).associatedGradedBasis q ν hQ)
        ν s a = a →
      (D.filtration.pivotProductQuotientFiltration π eta js
        (NilpotentLieFiltration.pi (fun j => (E j).filtration))).associatedGradedMap G
        (D.filtration.pivotProductMarkedMap π eta js) hmarked a = 0 → a = 0 :=
  D.filtration.joinedFrequency_graded_refiltered_top_kernel π eta js
    (fun j => (theta j).comp (LinearMap.proj j))
    (D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))) G q ν hQ hmarked
    (optionCommonPivotQuotientFast D E π eta js U)
    (optionCommonPivotQuotientFast_top_le D E π eta js U theta hzero e μ hH q ν hQ hU)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L : Type u} {M : J → Type u} {Y : Type*}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  {σ κ κQ : Type*} [Fintype σ] [Fintype κ] [Fintype κQ]
  (e : Basis κ ℚ (∀ i : Option J, optionLieSpace L M i)) (μ : κ → ℕ)
  (hF : ∀ k, (optionProduct D E).filtration.layer k =
    Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (q : Basis κQ ℚ ((L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) × (∀ j, M j)))
  (ν : κQ → ℕ)
  (hQ : ∀ k, (D.filtration.pivotProductQuotientFiltration π eta js
    (NilpotentLieFiltration.pi (fun j => (E j).filtration))).layer k =
      Submodule.span ℚ (q '' {i | k ≤ ν i}))

theorem exists_optionCommonPivotQuotient_family_symbol_factors
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) μ)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    {height l : ℕ} (hheight : 1 ≤ height) (hl : 0 < l)
    (hentries : ∀ i j,
      RationalHeightLE (q.repr (optionPivotProductQuotientMap D π eta js (e j)) i) height)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) μ) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hheightp : (height : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
    (hU : BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e μ hF)
      μ U.toSubmodule)
    (theta : ∀ j, M j →ₗ[ℚ] ℚ)
    (hzero : ∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer U s →
      realifyFunctional ((pairFrequency (eta j) (theta j)).comp
        (optionPairProjection j).toLinearMap) x = 0)
    {Ω : Type*} (H : Finset Ω) (side : σ → ℝ) (hside : ∀ i, 0 < side i) (r : ℝ)
    (g : Ω → ((optionProduct D E).filtration.realification.adaptedPolynomialFiltration
      (fun _ : σ => 1)).Group)
    (hfactor : ∀ a ∈ H, (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
      e μ hF side r l U (g a)) :
    let Q := D.filtration.pivotProductQuotientFiltration π eta js
      (NilpotentLieFiltration.pi (fun j => (E j).filtration))
    let W := optionCommonPivotQuotientFast D E π eta js U
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      (∀ a ∈ H, ∃ El Pl Rl : Q.RealPolynomialSymbolGroup (fun _ : σ => 1),
        El * Pl * Rl = Q.realPolynomialSymbolHom q ν hQ (fun _ => 1)
          ((optionProduct D E).filtration.realPolynomialGroupMap Q
            (optionPivotProductQuotientMap D π eta js)
            (optionPivotProductQuotientMap_mem_layer D E π eta js)
            (fun _ => 1) (g a)) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (Q.symbolPointwiseSubalgebra q ν hQ (fun _ => 1) W) ∧
        Q.SymbolSlowBound q ν hQ (fun _ => 1) side (Real.exp ((p + 2) ^ 3 + r)) El ∧
        Q.SymbolRationalGrid q ν hQ (fun _ => 1) m Rl) ∧
      BasisGradedSubmodule (Q.associatedGradedBasis q ν hQ) ν W.toSubmodule ∧
      (∀ x ∈ Q.gradedRefiltrationLayer W s,
        D.filtration.pivotProductMarkedMap π eta js x = 0 → x = 0) ∧
      (∀ (G : NilpotentLieFiltration (Y × (∀ j, M j)) s)
        (hmarked : ∀ k, ∀ x ∈ Q.layer k,
          D.filtration.pivotProductMarkedMap π eta js x ∈ G.layer k),
        ∀ a ∈ W, basisGradeProjection (Q.associatedGradedBasis q ν hQ) ν s a = a →
          Q.associatedGradedMap G (D.filtration.pivotProductMarkedMap π eta js) hmarked a = 0 →
          a = 0) := by
  dsimp only
  obtain ⟨m, hm, hmp, hlm, hproject⟩ :=
    (optionProduct D E).filtration.exists_common_refiltered_marked_symbol_factors
      (D.filtration.pivotProductQuotientFiltration π eta js
        (NilpotentLieFiltration.pi (fun j => (E j).filtration)))
      e μ hF q ν hQ (optionPivotProductQuotientMap D π eta js)
      (optionPivotProductQuotientMap_mem_layer D E π eta js)
      hheight hl hentries hp hsource htarget hheightp hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact hproject side hside r U (g a) (hfactor a ha)
  · exact optionCommonPivotQuotientFast_graded D E π eta js U e μ hF q ν hQ hU
  · exact optionCommonPivotQuotientFast_top_kernel_eq_zero
      D E π eta js U theta hzero e μ hF q ν hQ hU
  · intro G hmarked
    exact optionCommonPivotQuotientFast_graded_top_kernel
      D E π eta js U theta hzero e μ hF q ν hQ hU G hmarked

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {J : Type v} [Fintype J] {L Y : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal π eta js, π x = 0)
  (U : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
  (theta : ∀ j, M j →ₗ[ℚ] ℚ)
  (hzero : ∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer U s →
    realifyFunctional ((pairFrequency (eta j) (theta j)).comp
      (optionPairProjection j).toLinearMap) x = 0)

include hzero in

theorem optionNativeCommonFastTop_quotient_kernel_eq_zero
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ ((optionProduct D E).filtration.gradedRefiltrationLayer U s).map
      (optionMarkedLieMap (L := M)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js))).toLinearMap)
    (hmark : optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y = 0) :
    y = 0 := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hπ : π (x none) = 0 := congrFun hmark none
  have hpartner (j : J) : x (some j) = 0 := congrFun hmark (some j)
  have hmem : x none ∈ D.filtration.pivotAnnihilatorIdeal π eta js := by
    apply (D.filtration.mem_pivotAnnihilatorIdeal π eta js (x none)).mpr
    refine ⟨?_, hπ, ?_⟩
    · exact (mem_pi_layer (fun i => (optionFactors D E i).filtration) s x).mp
        ((optionProduct D E).filtration.gradedRefiltrationLayer_le U s hx) none
    · intro j _
      have hz := (optionProduct D E).filtration.frequency_zero_on_refilteredLayer_of_real
        U ((pairFrequency (eta j) (theta j)).comp (optionPairProjection j).toLinearMap)
        s (hzero j) x hx
      simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, pairFrequency_apply,
        optionPairProjection_true, optionPairProjection_false] at hz
      have hp : (x (some j) : M j) = (0 : M j) := hpartner j
      rw [hp, map_zero, add_zero] at hz
      exact hz
  funext i
  cases i with
  | none => exact (lieQuotientMap_eq_zero
      (D.filtration.pivotAnnihilatorIdeal π eta js) (x none)).mpr hmem
  | some j => exact hpartner j

variable {dQ : ℕ}
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.pivotQuotientFiltration π eta js)
  {κ κQ : Type*}
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

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
    (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.gradedRefiltrationLayer
      (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U) s)
    (hmark : optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y = 0) :
    y = 0 := by
  rw [optionNativeCommonPivotQuotientFast_layer_eq
    D E π eta js Q hQ U e μ hSource c ν hTarget hU s] at hy
  exact optionNativeCommonFastTop_quotient_kernel_eq_zero
    D E π eta js hker U theta hzero y hy hmark

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_graded_top_kernel
    (G : NilpotentLieFiltration (∀ i : Option J, optionLieSpace Y M i) s)
    (hmarked : ∀ k, ∀ y ∈ (optionProduct Q E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y ∈
          G.layer k) :
    ∀ a ∈ optionNativeCommonPivotQuotientFast D E π eta js Q hQ U,
      basisGradeProjection
        ((optionProduct Q E).filtration.associatedGradedBasis c ν hTarget) ν s a = a →
      (optionProduct Q E).filtration.associatedGradedMap G
        (optionMarkedLieMap (L := M)
          (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
        hmarked a = 0 → a = 0 := by
  apply ((optionProduct Q E).filtration.graded_top_kernel_iff_refiltered_top_kernel
    G c ν hTarget
    (optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
    hmarked (optionNativeCommonPivotQuotientFast D E π eta js Q hQ U)).mpr
  exact optionNativeCommonPivotQuotientFast_top_kernel_eq_zero
    D E π eta js hker U theta hzero Q hQ e μ hSource c ν hTarget hU

include hQ in

theorem optionNativePivotQuotientMarkedMap_mem_layer
    (G₀ : NilpotentLieFiltration Y s)
    (hπ : ∀ k, ∀ x ∈ D.filtration.layer k, π x ∈ G₀.layer k)
    (k : ℕ) (y : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i)
    (hy : y ∈ (optionProduct Q E).filtration.layer k) :
    optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) y ∈
      (NilpotentLieFiltration.pi (optionFiltrations G₀ (fun j => (E j).filtration))).layer k := by
  have hcoord := (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k y).mp hy
  apply (mem_pi_layer (optionFiltrations G₀ (fun j => (E j).filtration)) k _).mpr
  intro i
  cases i with
  | none =>
    have hy₀ : y none ∈ Q.filtration.layer k := hcoord none
    rw [hQ] at hy₀
    obtain ⟨x, hx, hxy⟩ := hy₀
    change quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker
      (y none) ∈ G₀.layer k
    rw [← hxy]
    exact hπ k x hx
  | some j => exact hcoord (some j)

include hzero e μ hSource c ν hTarget hU in

theorem optionNativeCommonPivotQuotientFast_graded_top_kernel_option
    (G₀ : NilpotentLieFiltration Y s)
    (hπ : ∀ k, ∀ x ∈ D.filtration.layer k, π x ∈ G₀.layer k) :
    ∀ a ∈ optionNativeCommonPivotQuotientFast D E π eta js Q hQ U,
      basisGradeProjection
        ((optionProduct Q E).filtration.associatedGradedBasis c ν hTarget) ν s a = a →
      (optionProduct Q E).filtration.associatedGradedMap
        (NilpotentLieFiltration.pi (optionFiltrations G₀ (fun j => (E j).filtration)))
        (optionMarkedLieMap (L := M)
          (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
        (optionNativePivotQuotientMarkedMap_mem_layer D E π eta js hker Q hQ G₀ hπ)
        a = 0 → a = 0 :=
  optionNativeCommonPivotQuotientFast_graded_top_kernel
    D E π eta js hker U theta hzero Q hQ e μ hSource c ν hTarget hU
    (NilpotentLieFiltration.pi (optionFiltrations G₀ (fun j => (E j).filtration)))
    (optionNativePivotQuotientMarkedMap_mem_layer D E π eta js hker Q hQ G₀ hπ)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration
open scoped TensorProduct

variable {J : Type v} [Fintype J] {L Y : Type u} {M : J → Type u}
  [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
  [LieRing Y] [LieAlgebra ℚ Y] {s d₀ dQ : ℕ} {d : J → ℕ}
  (D : RationalFilteredNilmanifold L s d₀)
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal π eta js, π x = 0)
  (Q : RationalFilteredNilmanifold
    (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) s dQ)
  (hQ : Q.filtration = D.filtration.pivotQuotientFiltration π eta js)
  (Fmark : NilpotentLieFiltration Y s)
  (hstrong : ∀ k, ∀ y ∈ Fmark.layer k, ∃ x ∈ D.filtration.layer k, π x = y)

include hQ hstrong in

theorem optionNativePivotQuotientMarkedMap_layer_surjective
    (k : ℕ) (y : ∀ i : Option J, optionLieSpace Y M i)
    (hy : y ∈ (NilpotentLieFiltration.pi
      (optionFiltrations Fmark (fun j => (E j).filtration))).layer k) :
    ∃ x ∈ (optionProduct Q E).filtration.layer k,
      optionMarkedLieMap (L := M)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker) x = y := by
  have hcoord := (mem_pi_layer (optionFiltrations Fmark (fun j => (E j).filtration)) k y).mp hy
  obtain ⟨x₀, hx₀, hxy₀⟩ := hstrong k (y none) (hcoord none)
  let x : ∀ i : Option J,
      optionLieSpace (L ⧸ D.filtration.pivotAnnihilatorIdeal π eta js) M i
    | none => lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) x₀
    | some j => y (some j)
  refine ⟨x, ?_, ?_⟩
  · apply (mem_pi_layer (fun i => (optionFactors Q E i).filtration) k x).mpr
    intro i
    cases i with
    | none =>
      change lieQuotientMap (D.filtration.pivotAnnihilatorIdeal π eta js) x₀ ∈
        Q.filtration.layer k
      rw [hQ]
      exact ⟨x₀, hx₀, rfl⟩
    | some j => exact hcoord (some j)
  · funext i
    cases i with
    | none => exact hxy₀
    | some j => rfl

include E hQ hstrong in

theorem optionNativePivotQuotientMarkedMap_surjective :
    Function.Surjective (optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker)) := by
  intro y
  obtain ⟨x, _, hxy⟩ := optionNativePivotQuotientMarkedMap_layer_surjective
    D E π eta js hker Q hQ Fmark hstrong 1 y (by
      rw [(NilpotentLieFiltration.pi
        (optionFiltrations Fmark (fun j => (E j).filtration))).one_eq_top]
      exact Submodule.mem_top)
  exact ⟨x, hxy⟩

include hQ hstrong in

theorem optionNativePivotQuotientMarkedMap_layer_map
    (hπ : ∀ k, ∀ x ∈ D.filtration.layer k, π x ∈ Fmark.layer k) (k : ℕ) :
    ((optionProduct Q E).filtration.layer k).map
      (optionMarkedLieMap (L := M)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker)).toLinearMap =
      (NilpotentLieFiltration.pi
        (optionFiltrations Fmark (fun j => (E j).filtration))).layer k := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact optionNativePivotQuotientMarkedMap_mem_layer D E π eta js hker Q hQ Fmark hπ k x hx
  · intro y hy
    exact optionNativePivotQuotientMarkedMap_layer_surjective
      D E π eta js hker Q hQ Fmark hstrong k y hy

include hQ hstrong in

theorem optionNativePivotQuotientMarkedMap_real_layer_surjective
    (hπ : ∀ k, ∀ x ∈ D.filtration.layer k, π x ∈ Fmark.layer k)
    (k : ℕ) (y : ℝ ⊗[ℚ] (∀ i : Option J, optionLieSpace Y M i))
    (hy : y ∈ (NilpotentLieFiltration.pi
      (optionFiltrations Fmark (fun j => (E j).filtration))).realification.layer k) :
    ∃ x ∈ (optionProduct Q E).filtration.realification.layer k,
      realificationLieHom (optionMarkedLieMap (L := M)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker)) x = y :=
  (optionProduct Q E).filtration.realificationLieHom_layer_surjective
    (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => (E j).filtration)))
    (optionMarkedLieMap (L := M)
      (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal π eta js) π hker))
    (optionNativePivotQuotientMarkedMap_mem_layer D E π eta js hker Q hQ Fmark hπ)
    (optionNativePivotQuotientMarkedMap_layer_surjective D E π eta js hker Q hQ Fmark hstrong)
    k y hy

end Erdos3.RationalFilteredNilmanifold

end

end OAI
