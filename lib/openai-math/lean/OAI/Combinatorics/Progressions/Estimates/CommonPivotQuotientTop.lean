import OAI.Combinatorics.Progressions.Fourier.JoinedFrequencyRefilteredTop

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

section Product

variable {L W : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing W] [LieAlgebra ℚ W] {s : ℕ}

def prod (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration W s) :
    NilpotentLieFiltration (L × W) s where
  layer j := (F.layer j).prod (P.layer j)
  antitone := by
    intro i j hij x hx
    exact ⟨F.antitone hij hx.1, P.antitone hij hx.2⟩
  one_eq_top := by rw [F.one_eq_top, P.one_eq_top, Submodule.prod_top]
  lie_mem := by
    intro i j x y hx hy
    exact ⟨F.lie_mem hx.1 hy.1, P.lie_mem hx.2 hy.2⟩
  terminal := by rw [F.terminal, P.terminal, Submodule.prod_bot]

@[simp] theorem prod_layer (F : NilpotentLieFiltration L s)
    (P : NilpotentLieFiltration W s) (j : ℕ) :
    (F.prod P).layer j = (F.layer j).prod (P.layer j) := rfl

@[simp] theorem mem_prod_layer (F : NilpotentLieFiltration L s)
    (P : NilpotentLieFiltration W s) (j : ℕ) (x : L × W) :
    x ∈ (F.prod P).layer j ↔ x.1 ∈ F.layer j ∧ x.2 ∈ P.layer j := Iff.rfl

end Product

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

noncomputable def pivotQuotientFiltration :
    NilpotentLieFiltration (L ⧸ F.pivotAnnihilatorIdeal π eta js) s :=
  F.quotientLie (F.pivotAnnihilatorIdeal π eta js) (by rw [F.terminal]; exact bot_le)

@[simp] theorem pivotQuotientFiltration_layer (j : ℕ) :
    (F.pivotQuotientFiltration π eta js).layer j =
      (F.layer j).map (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js)).toLinearMap := rfl

noncomputable def pivotProductQuotientFiltration (P : NilpotentLieFiltration W s) :
    NilpotentLieFiltration ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) s :=
  (F.pivotQuotientFiltration π eta js).prod P

theorem pivotProductQuotientMap_mem_layer (P : NilpotentLieFiltration W s)
    (j : ℕ) (x : L × W) (hx : x ∈ (F.prod P).layer j) :
    F.pivotProductQuotientMap π eta js x ∈
      (F.pivotProductQuotientFiltration π eta js P).layer j := by
  exact ⟨⟨x.1, hx.1, rfl⟩, hx.2⟩

theorem pivotProductQuotientMap_layer_surjective (P : NilpotentLieFiltration W s)
    (j : ℕ) (y : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × W)
    (hy : y ∈ (F.pivotProductQuotientFiltration π eta js P).layer j) :
    ∃ x ∈ (F.prod P).layer j, F.pivotProductQuotientMap π eta js x = y := by
  obtain ⟨x, hx, hxy⟩ := hy.1
  exact ⟨(x, y.2), ⟨hx, hy.2⟩, Prod.ext hxy rfl⟩

theorem pivotProductQuotientMap_layer_map (P : NilpotentLieFiltration W s) (j : ℕ) :
    ((F.prod P).layer j).map (F.pivotProductQuotientMap π eta js).toLinearMap =
      (F.pivotProductQuotientFiltration π eta js P).layer j := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact F.pivotProductQuotientMap_mem_layer π eta js P j x hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := F.pivotProductQuotientMap_layer_surjective π eta js P j y hy
    exact ⟨x, hx, hxy⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem frequency_zero_on_refilteredLayer_of_real
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s : ℕ}
    (H : NilpotentLieFiltration V s) (U : LieSubalgebra ℚ H.AssociatedGraded)
    (η : V →ₗ[ℚ] ℚ) (k : ℕ)
    (hzero : ∀ x ∈ H.realGradedRefiltrationLayer U k, realifyFunctional η x = 0)
    (x : V) (hx : x ∈ H.gradedRefiltrationLayer U k) : η x = 0 := by
  have hz := hzero ((1 : ℝ) ⊗ₜ[ℚ] x) (Submodule.tmul_mem_baseChange_of_mem 1 hx)
  simp only [realifyFunctional_tmul, one_mul] at hz
  exact_mod_cast hz

variable {L V Y J κ κQ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing V] [LieAlgebra ℚ V] [LieRing Y] [LieAlgebra ℚ Y] {s : ℕ}
  (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration V s)
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (partner : J → V →ₗ[ℚ] ℚ)
  (U : LieSubalgebra ℚ (F.prod P).AssociatedGraded)

noncomputable def commonPivotQuotientFast :
    LieSubalgebra ℚ (F.pivotProductQuotientFiltration π eta js P).AssociatedGraded :=
  U.map ((F.prod P).associatedGradedMap (F.pivotProductQuotientFiltration π eta js P)
    (F.pivotProductQuotientMap π eta js)
    (F.pivotProductQuotientMap_mem_layer π eta js P))

variable
  (hzero : ∀ j ∈ js, ∀ x ∈ (F.prod P).realGradedRefiltrationLayer U s,
    realifyFunctional ((eta j).comp (LinearMap.fst ℚ L V) +
      (partner j).comp (LinearMap.snd ℚ L V)) x = 0)

include hzero in

theorem commonFastTop_le_joinedFrequencyTop :
    (F.prod P).gradedRefiltrationLayer U s ≤ F.joinedFrequencyTop eta js partner := by
  intro x hx
  apply (F.mem_joinedFrequencyTop eta js partner x).mpr
  refine ⟨((F.prod P).gradedRefiltrationLayer_le U s hx).1, ?_⟩
  intro j hj
  exact (F.prod P).frequency_zero_on_refilteredLayer_of_real U _ s (hzero j hj) x hx

include hzero in

theorem commonFastTop_quotient_le_joinedFrequencyQuotientTop :
    ((F.prod P).gradedRefiltrationLayer U s).map
      (F.pivotProductQuotientMap π eta js).toLinearMap ≤
      F.joinedFrequencyQuotientTop π eta js partner :=
  Submodule.map_mono (F.commonFastTop_le_joinedFrequencyTop P eta js partner U hzero)

include hzero in

theorem commonFastTop_quotient_kernel_eq_zero
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × V)
    (hx : x ∈ ((F.prod P).gradedRefiltrationLayer U s).map
      (F.pivotProductQuotientMap π eta js).toLinearMap)
    (hkernel : F.pivotProductMarkedMap π eta js x = 0) : x = 0 :=
  F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js partner x
    (F.commonFastTop_quotient_le_joinedFrequencyQuotientTop P π eta js partner U hzero hx)
    hkernel

variable (e : Basis κ ℚ (L × V)) (μ : κ → ℕ)
  (hH : ∀ k, (F.prod P).layer k = Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (q : Basis κQ ℚ ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × V)) (ν : κQ → ℕ)
  (hQ : ∀ k, (F.pivotProductQuotientFiltration π eta js P).layer k =
    Submodule.span ℚ (q '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule ((F.prod P).associatedGradedBasis e μ hH) μ U.toSubmodule)

include e μ hH q ν hQ hU in

theorem commonPivotQuotientFast_layer_eq (k : ℕ) :
    (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationLayer
      (F.commonPivotQuotientFast P π eta js U) k =
    ((F.prod P).gradedRefiltrationLayer U k).map
      (F.pivotProductQuotientMap π eta js).toLinearMap := by
  symm
  exact (F.prod P).gradedRefiltrationLayer_map
    (F.pivotProductQuotientFiltration π eta js P) e μ hH q ν hQ
    (F.pivotProductQuotientMap π eta js) (F.pivotProductQuotientMap_mem_layer π eta js P)
    U hU (F.pivotProductQuotientMap_layer_surjective π eta js P) k

include e μ hH q ν hQ hU in
theorem commonPivotQuotientFast_graded :
    BasisGradedSubmodule
      ((F.pivotProductQuotientFiltration π eta js P).associatedGradedBasis q ν hQ) ν
      (F.commonPivotQuotientFast P π eta js U).toSubmodule :=
  (F.prod P).associatedGradedMap_image_graded
    (F.pivotProductQuotientFiltration π eta js P) e μ hH q ν hQ
    (F.pivotProductQuotientMap π eta js) (F.pivotProductQuotientMap_mem_layer π eta js P)
    U hU

include hzero e μ hH q ν hQ hU in

theorem commonPivotQuotientFast_top_le :
    (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationLayer
      (F.commonPivotQuotientFast P π eta js U) s ≤
      F.joinedFrequencyQuotientTop π eta js partner := by
  rw [F.commonPivotQuotientFast_layer_eq P π eta js U e μ hH q ν hQ hU s]
  exact F.commonFastTop_quotient_le_joinedFrequencyQuotientTop P π eta js partner U hzero

include hzero e μ hH q ν hQ hU in

theorem commonPivotQuotientFast_top_kernel_eq_zero
    (x : (L ⧸ F.pivotAnnihilatorIdeal π eta js) × V)
    (hx : x ∈ (F.pivotProductQuotientFiltration π eta js P).gradedRefiltrationLayer
      (F.commonPivotQuotientFast P π eta js U) s)
    (hkernel : F.pivotProductMarkedMap π eta js x = 0) : x = 0 :=
  F.joinedFrequencyQuotientTop_kernel_eq_zero π eta js partner x
    (F.commonPivotQuotientFast_top_le P π eta js partner U hzero e μ hH q ν hQ hU hx)
    hkernel

include hzero e μ hH q ν hQ hU in

theorem commonPivotQuotientFast_graded_top_kernel
    (G : NilpotentLieFiltration (Y × V) s)
    (hmarked : ∀ k, ∀ x ∈ (F.pivotProductQuotientFiltration π eta js P).layer k,
      F.pivotProductMarkedMap π eta js x ∈ G.layer k) :
    ∀ a ∈ F.commonPivotQuotientFast P π eta js U,
      basisGradeProjection
        ((F.pivotProductQuotientFiltration π eta js P).associatedGradedBasis q ν hQ) ν s a = a →
      (F.pivotProductQuotientFiltration π eta js P).associatedGradedMap G
        (F.pivotProductMarkedMap π eta js) hmarked a = 0 → a = 0 :=
  F.joinedFrequency_graded_refiltered_top_kernel π eta js partner
    (F.pivotProductQuotientFiltration π eta js P) G q ν hQ hmarked
    (F.commonPivotQuotientFast P π eta js U)
    (F.commonPivotQuotientFast_top_le P π eta js partner U hzero e μ hH q ν hQ hU)

end Erdos3.NilpotentLieFiltration

end

end OAI
