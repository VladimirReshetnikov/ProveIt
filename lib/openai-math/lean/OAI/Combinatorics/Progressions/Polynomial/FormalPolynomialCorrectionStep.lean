/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
import OAI.Combinatorics.Progressions.Nilpotent.PolynomialBCHRemoval

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace VectorPolynomial

theorem pderiv_map {σ V W : Type*} [LieRing V] [LieAlgebra ℚ V]
    [LieRing W] [LieAlgebra ℚ W] (i : σ) (f : V →ₗ[ℚ] W) (P : VectorPolynomial σ ℚ V) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor W (map f P) =
      map f ((MvPolynomial.pderiv i).toLinearMap.rTensor V P) := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  simp only [coefficients_pderiv, coefficients_map, map_smul]

theorem pderiv_mem_submodule {σ V : Type*} [LieRing V] [LieAlgebra ℚ V]
    (W : Submodule ℚ V) (P : VectorPolynomial σ ℚ V)
    (hP : ∀ α, coefficients P α ∈ W) (i : σ) (α : σ →₀ ℕ) :
    coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor V P) α ∈ W := by
  rw [coefficients_pderiv]
  exact W.smul_mem _ (hP _)

end VectorPolynomial

theorem basisGradeProjection_other {R L ι : Type*} [Field R] [AddCommGroup L] [Module R L]
    (b : Basis ι R L) (w : ι → ℕ) {i j : ℕ} (hij : i ≠ j) (x : L) :
    basisGradeProjection b w i (basisGradeProjection b w j x) = 0 := by
  apply b.repr.injective
  apply Finsupp.ext
  intro k
  simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  by_cases hi : w k = i
  · rw [ite_eq_left hi, ite_eq_right (fun hj => hij (hi.symm.trans hj))]
  · rw [ite_eq_right hi]

namespace NilpotentLieFiltration

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_sub_horizontal_mem_of_lower_grades (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    {j : ℕ} (hj : 2 ≤ j) (x : ℝ ⊗[ℚ] L)
    (hlower : ∀ d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d x ∈ V) :
    x - basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V ⊔ (F.realLayer j).toSubmodule := by
  classical
  have hzero : basisGradeProjection (b.baseChange ℝ) w 0 x = 0 :=
    F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers 0 x
      (by rw [show 0 + 1 = 1 from rfl, F.realification.one_eq_top]; trivial)
  have hlow : basisBelowProjection (b.baseChange ℝ) w j x -
      basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V := by
    rw [basisBelowProjection_eq_sum_grades,
      ← Finset.sum_erase_add (Finset.range j) (fun d => basisGradeProjection (b.baseChange ℝ) w d x)
        (by simp only [Finset.mem_range]; omega : 1 ∈ Finset.range j), add_sub_cancel_right]
    apply V.sum_mem
    intro d hd
    obtain ⟨hd1, hdj⟩ := Finset.mem_erase.mp hd
    by_cases hd0 : d = 0
    · subst d
      rw [hzero]
      exact V.zero_mem
    · exact hlower d (by omega) (Finset.mem_range.mp hdj)
  have hhigh := F.sub_realGradeTruncation_mem b w hlayers j x
  have h := (V ⊔ (F.realLayer j).toSubmodule).add_mem
    (Submodule.mem_sup_right hhigh) (Submodule.mem_sup_left hlow)
  convert h using 1
  abel

include hlayers in
theorem real_polynomial_derivative_lower_layers (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    {j : ℕ} (hj : 2 ≤ j) (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P α) ∈ V)
    (i : σ) (t : σ → ℝ) :
    let D := eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)
    D - basisGradeProjection (b.baseChange ℝ) w 1 D ∈ V ⊔ (F.realLayer j).toSubmodule ∧
      basisGradeProjection (b.baseChange ℝ) w 1 D ∈ K := by
  intro D
  let π := basisGradeProjection (b.baseChange ℝ) w 1
  let q := LinearMap.id - π
  let W := V ⊔ (F.realLayer j).toSubmodule
  have hq : ∀ α, coefficients (map (q.restrictScalars ℚ) P) α ∈ W := by
    intro α
    rw [coefficients_map]
    exact F.real_sub_horizontal_mem_of_lower_grades b w hlayers V hj _ (hlower α)
  have hπ : ∀ α, coefficients (map (π.restrictScalars ℚ) P) α ∈ K := by
    intro α
    rw [coefficients_map]
    exact hK α
  have hDq := (eval₂_mem_iff_coefficients W
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (map (q.restrictScalars ℚ) P))).mpr
      (pderiv_mem_submodule (W.restrictScalars ℚ) _ hq i) t
  have hDπ := (eval₂_mem_iff_coefficients K
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (map (π.restrictScalars ℚ) P))).mpr
      (pderiv_mem_submodule (K.restrictScalars ℚ) _ hπ i) t
  rw [pderiv_map, eval₂_map] at hDq hDπ
  exact ⟨hDq, hDπ⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_current_layer_polynomial_derivative_equation (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hU : ∀ t : σ → ℝ, eval₂ t P ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P α) ∈ V)
    (hbracket : ∀ (t : σ → ℝ) k, k ∈ K →
      ⁅eval₂ t P, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (extra : σ → (σ → ℝ) → ℝ ⊗[ℚ] L)
    (z : σ → (σ → ℝ) → DualGroup F.realification.lowerCentralSeries_eq_bot)
    (hbase : ∀ i t, dualBaseLinear (z i t).coord = eval₂ t P)
    (htangent : ∀ i t, dualTangentLinear (z i t).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P))
    (hextra : ∀ i t, extra i t - basisGradeProjection (b.baseChange ℝ) w 1
      (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)) ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : ∀ i t, dualLogDerivative (z i t) = eval₂ t (small i) +
      dualAdjoint (dualBaseHom (z i t)) (eval₂ t (rational i)) + extra i t) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) -
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔
        x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  intro i
  apply (eval₂_mem_iff_coefficients V _).mp
  intro t
  let D := eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P)
  let k := basisGradeProjection (b.baseChange ℝ) w 1 D
  have hlow := F.real_polynomial_derivative_lower_layers b w hlayers V K hj P hK hlower i t
  have hzU : dualBaseLinear (z i t).coord ∈ U := by rw [hbase]; exact hU t
  have hzlow : dualTangentLinear (z i t).coord - k ∈ V.restrictScalars ℚ ⊔ F.realification.layer j := by
    rw [htangent]
    exact (hW j _).mpr hlow.1
  have hzbracket : ⁅dualBaseLinear (z i t).coord, k⁆ ∈
      V.restrictScalars ℚ ⊔ F.realification.layer (j + 1) := by
    rw [hbase]
    exact (hW (j + 1) _).mpr (hbracket t k hlow.2)
  have hr : eval₂ t (rational i) ∈ V.restrictScalars ℚ ⊔ F.realification.layer j :=
    (hW j _).mpr ((eval₂_mem_iff_coefficients _ _).mpr (hrational i) t)
  have he := (hW (j + 1) _).mpr (hextra i t)
  have hcurrent := F.realification.current_layer_derivative_system hs U (V.restrictScalars ℚ)
    hUV j (z i t) hzU k (eval₂ t (small i)) (eval₂ t (rational i)) (extra i t)
    hzlow hzbracket hr he (hsystem i t)
  have hproj := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j _
    ((hW (j + 1) _).mp hcurrent)
  have hkzero : basisGradeProjection (b.baseChange ℝ) w j k = 0 :=
    basisGradeProjection_other (b.baseChange ℝ) w (by omega : j ≠ 1) D
  rw [htangent, map_sub, map_sub, map_add, hkzero, sub_zero] at hproj
  simp only [map_sub, pderiv_map, eval₂_map]
  convert hproj using 1
  change _ = (basisGradeProjection (b.baseChange ℝ) w j D -
    (basisGradeProjection (b.baseChange ℝ) w j (eval₂ t (small i)) +
      basisGradeProjection (b.baseChange ℝ) w j (eval₂ t (rational i))))
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficientSubmodule_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P Q : VectorPolynomial σ ℚ L)
    (hP : P ∈ coefficientLieSubalgebra U) (hQ : Q ∈ coefficientSubmodule V) :
    ⁅P, Q⁆ ∈ coefficientSubmodule V := by
  classical
  rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients P).support (coefficients Q).support
    (fun α => monomial (R := ℚ) α (coefficients P α))
    (fun β => monomial (R := ℚ) β (coefficients Q β))]
  apply (coefficientSubmodule V).sum_mem
  intro α _
  apply (coefficientSubmodule V).sum_mem
  intro β _
  rw [lie_monomial]
  exact monomial_mem_coefficientSubmodule V _ (hUV _ (hP α) _ (hQ β))

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem formalLogDerivative_mem_coefficientSubmodule
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPV : ∀ α, coefficients P.coord α ∈ V) :
    ∀ α, coefficients (formalLogDerivative i P) α ∈ V :=
  formalLogDerivative_mem_of_invariant (coefficientLieSubalgebra U) (coefficientSubmodule V)
    (fun A hA B hB => coefficientSubmodule_invariant U V hUV A B hA hB)
    i P hPU (pderiv_mem_submodule V P.coord hPV i)

theorem dualAdjoint_mem_coefficientSubmodule
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P : PolynomialGroup σ hnil) (Q : VectorPolynomial σ ℚ L)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hQV : ∀ α, coefficients Q α ∈ V) :
    ∀ α, coefficients (dualAdjoint P Q) α ∈ V :=
  dualAdjoint_mem_of_invariant (coefficientLieSubalgebra U) (coefficientSubmodule V)
    (fun A hA B hB => coefficientSubmodule_invariant U V hUV A B hA hB) P hPU Q hQV

theorem polynomial_derivative_removal_preserves_coefficients
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (A B : PolynomialGroup σ hnil) (small rational : VectorPolynomial σ ℚ L)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (hsmall : ∀ α, coefficients small α ∈ V)
    (hrational : ∀ α, coefficients rational α ∈ V) :
    (∀ α, coefficients (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) α ∈ V) ∧
      ∀ α, coefficients (dualAdjoint B rational - formalLogDerivative i B) α ∈ V := by
  have hYA := formalLogDerivative_mem_coefficientSubmodule U V hUV i A hAU hAV
  have hYB := formalLogDerivative_mem_coefficientSubmodule U V hUV i B hBU hBV
  have hAinv : ∀ α, coefficients A⁻¹.coord α ∈ U := by
    intro α
    change coefficients (-A.coord) α ∈ U
    rw [map_neg, Finsupp.neg_apply]
    exact U.neg_mem (hAU α)
  constructor
  · exact dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹ _ hAinv
      ((coefficientSubmodule V).sub_mem hsmall hYA)
  · exact (coefficientSubmodule V).sub_mem
      (dualAdjoint_mem_coefficientSubmodule U V hUV B rational hBU hrational) hYB

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

noncomputable def gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {P | ∀ α,
    (basisGradeProjection b w (Finsupp.weight v α)).restrictScalars ℚ (coefficients P α) = coefficients P α}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply]
  add_mem' := by
    intro P Q hP hQ α
    simp only [map_add, Finsupp.add_apply, hP α, hQ α]
  smul_mem' := by
    intro a P hP α
    simp only [map_smul, Finsupp.smul_apply, hP α]

theorem monomial_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ)
    (α : σ →₀ ℕ) (x : L) (hx : basisGradeProjection b w (Finsupp.weight v α) x = x) :
    monomial (R := ℚ) α x ∈ gradedPolynomialSubmodule b w v := by
  intro β
  rw [coefficients_monomial]
  by_cases h : α = β
  · subst β
    simpa only [Finsupp.single_eq_same, LinearMap.restrictScalars_apply] using hx
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

noncomputable def gradedPolynomialSubalgebra (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { gradedPolynomialSubmodule b w v with
    lie_mem' := by
      intro P Q hP hQ
      classical
      rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum (coefficients P).support (coefficients Q).support
        (fun α => monomial (R := ℚ) α (coefficients P α))
        (fun β => monomial (R := ℚ) β (coefficients Q β))]
      apply (gradedPolynomialSubmodule b w v).sum_mem
      intro α _
      apply (gradedPolynomialSubmodule b w v).sum_mem
      intro β _
      rw [lie_monomial]
      apply monomial_mem_gradedPolynomialSubmodule
      rw [map_add]
      exact hb.projection_lie b w (hP α) (hQ β) }

theorem homogeneous_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ) (v : σ → ℕ)
    (j : ℕ) (P : VectorPolynomial σ ℚ L)
    (hhom : ∀ α, Finsupp.weight v α ≠ j → coefficients P α = 0)
    (hgrade : ∀ α, basisGradeProjection b w j (coefficients P α) = coefficients P α) :
    P ∈ gradedPolynomialSubmodule b w v := by
  intro α
  by_cases hα : Finsupp.weight v α = j
  · simpa only [hα, LinearMap.restrictScalars_apply] using hgrade α
  · rw [hhom α hα, map_zero]

theorem gradedPolynomialSubmodule_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (P : VectorPolynomial σ ℚ L) (hP : P ∈ gradedPolynomialSubmodule b w v)
    (j : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight v α ≠ j) :
    coefficients (map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  rw [coefficients_map]
  change basisGradeProjection b w j (coefficients P α) = 0
  have he : basisGradeProjection b w (Finsupp.weight v α) (coefficients P α) = coefficients P α := hP α
  rw [← he]
  exact basisGradeProjection_other b w (Ne.symm hα) _

theorem bchRemove_mem_gradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (s : ℕ)
    (A P B : VectorPolynomial σ ℚ L)
    (hA : A ∈ gradedPolynomialSubmodule b w v) (hP : P ∈ gradedPolynomialSubmodule b w v)
    (hB : B ∈ gradedPolynomialSubmodule b w v) :
    bchRemove s A P B ∈ gradedPolynomialSubmodule b w v := by
  let U := gradedPolynomialSubalgebra b w hb v
  exact lieBCH_mem U s (lieBCH_mem U s (U.neg_mem hA) hP) (U.neg_mem hB)

namespace NilpotentLieFiltration

theorem realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule
    {M κ : Type*} [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration M s) (b : Basis κ ℚ M) (w : κ → ℕ)
    (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (v : σ → ℕ) (x : F.RealPolynomialSymbol v) :
    F.realGradedSymbolPolynomial b w hF v x ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b w hF).baseChange ℝ) w v := by
  intro α
  change basisGradeProjection ((F.associatedGradedBasis b w hF).baseChange ℝ) w
    (Finsupp.weight v α) (coefficients (F.realGradedSymbolPolynomial b w hF v x) α) = _
  apply ((F.associatedGradedBasis b w hF).baseChange ℝ).repr.injective
  apply Finsupp.ext
  intro i
  rw [basisGradeProjection_repr]
  by_cases hi : w i = Finsupp.weight v α
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    exact (F.realGradedSymbolPolynomial_coordinate_of_ne b w hF v x α i (Ne.symm hi)).symm

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficientSubmodule_sup (V W : Submodule ℚ L) :
    coefficientSubmodule (σ := σ) (V ⊔ W) = coefficientSubmodule V ⊔ coefficientSubmodule W := by
  classical
  apply le_antisymm
  · intro P hP
    rw [← sum_monomial_coefficients P]
    change ∑ α ∈ (coefficients P).support, monomial α (coefficients P α) ∈ _
    apply Submodule.sum_mem
    intro α _
    obtain ⟨v, hv, w, hw, he⟩ := Submodule.mem_sup.mp (hP α)
    rw [← he]
    have hmono : monomial (R := ℚ) α (v + w) = monomial α v + monomial α w :=
      TensorProduct.tmul_add _ _ _
    rw [hmono]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (monomial_mem_coefficientSubmodule V α hv))
      (Submodule.mem_sup_right (monomial_mem_coefficientSubmodule W α hw))
  · apply sup_le
    · intro P hP α
      exact Submodule.mem_sup_left (hP α)
    · intro P hP α
      exact Submodule.mem_sup_right (hP α)

theorem coefficients_lie_constant (P : VectorPolynomial σ ℚ L) (x : L) (α : σ →₀ ℕ) :
    coefficients ⁅P, monomial (R := ℚ) 0 x⁆ α = ⁅coefficients P α, x⁆ := by
  induction P using TensorProduct.inductionOn with
  | tmul q y =>
    simp only [monomial, LieAlgebra.ExtendScalars.bracket_tmul,
      MvPolynomial.monomial_zero', MvPolynomial.C_1, mul_one,
      coefficients_tmul, coefficients_tmul, smul_lie]
  | add P Q hP hQ =>
    rw [LieRing.add_lie P Q, map_add, Finsupp.add_apply, hP, hQ,
      map_add, Finsupp.add_apply, LieRing.add_lie]

theorem polynomialLayer_eq_coefficientSubmodule {s : ℕ} (F : NilpotentLieFiltration L s) (j : ℕ) :
    (F.polynomialFiltration (σ := σ)).layer j = coefficientSubmodule (F.layer j) := by
  ext P
  rfl

theorem mem_coefficient_sup_polynomialLayer {s : ℕ} (F : NilpotentLieFiltration L s)
    (V : Submodule ℚ L) (j : ℕ) (P : VectorPolynomial σ ℚ L) :
    P ∈ coefficientSubmodule V ⊔ F.polynomialFiltration.layer j ↔
      ∀ α, coefficients P α ∈ V ⊔ F.layer j := by
  rw [polynomialLayer_eq_coefficientSubmodule, ← coefficientSubmodule_sup]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

section RealBasis

variable {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)
  (b : Basis ι ℝ L) (ω : ι → ℕ) (v : σ → ℕ)

theorem polynomialOrbit_log_mul_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (p q : F.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule b ω v)
    (hq : q.log ∈ gradedPolynomialSubmodule b ω v) :
    (p * q).log ∈ gradedPolynomialSubmodule b ω v :=
  lieBCH_mem (gradedPolynomialSubalgebra b ω hb v) s hp hq

theorem polynomialOrbit_log_inv_mem_graded (p : F.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule b ω v) :
    p⁻¹.log ∈ gradedPolynomialSubmodule b ω v :=
  (gradedPolynomialSubmodule b ω v).neg_mem hp

theorem polynomialOrbit_log_one_mem_graded :
    (1 : F.PolynomialOrbit v).log ∈ gradedPolynomialSubmodule b ω v :=
  (gradedPolynomialSubmodule b ω v).zero_mem

theorem polynomialOrbit_log_list_prod_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (ps : List (F.PolynomialOrbit v))
    (hps : ∀ p ∈ ps, p.log ∈ gradedPolynomialSubmodule b ω v) :
    ps.prod.log ∈ gradedPolynomialSubmodule b ω v := by
  induction ps with
  | nil => exact F.polynomialOrbit_log_one_mem_graded b ω v
  | cons p ps ih =>
    exact F.polynomialOrbit_log_mul_mem_graded b ω v hb p ps.prod
      (hps p List.mem_cons_self) (ih fun q hq => hps q (List.mem_cons_of_mem p hq))

end RealBasis

section RationalBasis

variable {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ) (v : σ → ℕ)

theorem realPolynomialOrbit_log_mul_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (p q : F.realification.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v)
    (hq : q.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    (p * q).log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v :=
  F.realification.polynomialOrbit_log_mul_mem_graded (b.baseChange ℝ) ω v
    (hb.baseChange b ω) p q hp hq

theorem realPolynomialOrbit_log_inv_mem_graded (p : F.realification.PolynomialOrbit v)
    (hp : p.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    p⁻¹.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v :=
  F.realification.polynomialOrbit_log_inv_mem_graded (b.baseChange ℝ) ω v p hp

theorem realPolynomialOrbit_log_one_mem_graded :
    (1 : F.realification.PolynomialOrbit v).log ∈
      gradedPolynomialSubmodule (b.baseChange ℝ) ω v :=
  F.realification.polynomialOrbit_log_one_mem_graded (b.baseChange ℝ) ω v

theorem realPolynomialOrbit_log_list_prod_mem_graded (hb : BasisHomogeneousBrackets b ω)
    (ps : List (F.realification.PolynomialOrbit v))
    (hps : ∀ p ∈ ps, p.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v) :
    ps.prod.log ∈ gradedPolynomialSubmodule (b.baseChange ℝ) ω v :=
  F.realification.polynomialOrbit_log_list_prod_mem_graded (b.baseChange ℝ) ω v
    (hb.baseChange b ω) ps hps

end RationalBasis

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

noncomputable def shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {P | ∀ α,
    (basisGradeProjection b w (Finsupp.weight v α + r)).restrictScalars ℚ
      (coefficients P α) = coefficients P α}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply]
  add_mem' := by
    intro P Q hP hQ α
    simp only [map_add, Finsupp.add_apply, hP α, hQ α]
  smul_mem' := by
    intro a P hP α
    simp only [map_smul, Finsupp.smul_apply, hP α]

theorem monomial_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) (α : σ →₀ ℕ) (x : L)
    (hx : basisGradeProjection b w (Finsupp.weight v α + r) x = x) :
    monomial (R := ℚ) α x ∈ shiftedGradedPolynomialSubmodule b w v r := by
  intro β
  rw [coefficients_monomial]
  by_cases h : α = β
  · subst β
    simpa only [Finsupp.single_eq_same, LinearMap.restrictScalars_apply] using hx
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero]

theorem shiftedGradedPolynomialSubmodule_invariant (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (r : ℕ)
    (P Q : VectorPolynomial σ ℚ L)
    (hP : P ∈ gradedPolynomialSubmodule b w v)
    (hQ : Q ∈ shiftedGradedPolynomialSubmodule b w v r) :
    ⁅P, Q⁆ ∈ shiftedGradedPolynomialSubmodule b w v r := by
  classical
  rw [← sum_monomial_coefficients P, ← sum_monomial_coefficients Q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients P).support (coefficients Q).support
    (fun α => monomial (R := ℚ) α (coefficients P α))
    (fun β => monomial (R := ℚ) β (coefficients Q β))]
  apply (shiftedGradedPolynomialSubmodule b w v r).sum_mem
  intro α _
  apply (shiftedGradedPolynomialSubmodule b w v r).sum_mem
  intro β _
  rw [lie_monomial]
  apply monomial_mem_shiftedGradedPolynomialSubmodule
  rw [map_add, Nat.add_assoc]
  exact hb.projection_lie b w (hP α) (hQ β)

theorem pderiv_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1)) (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L P ∈
      shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 := by
  intro α
  rw [coefficients_pderiv, map_smul]
  have h := congrArg (fun x => (α i + 1 : ℚ) • x) (hP (α + Finsupp.single i 1))
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem shiftedGradedPolynomialSubmodule_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (v : σ → ℕ) (r : ℕ) (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ shiftedGradedPolynomialSubmodule b w v r)
    (j : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight v α + r ≠ j) :
    coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  rw [coefficients_map]
  change basisGradeProjection b w j (coefficients P α) = 0
  have he : basisGradeProjection b w (Finsupp.weight v α + r) (coefficients P α) =
      coefficients P α := hP α
  rw [← he]
  exact basisGradeProjection_other b w (Ne.symm hα) _

theorem shifted_one_projection_homogeneous (b : Basis ι ℝ L) (w : ι → ℕ)
    (P : VectorPolynomial σ ℚ L)
    (hP : P ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    {j : ℕ} (hj : 0 < j) (α : σ →₀ ℕ)
    (hα : Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1) :
    coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) P) α = 0 := by
  apply shiftedGradedPolynomialSubmodule_projection_homogeneous b w (fun _ => 1) 1 P hP j α
  omega

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (v : σ → ℕ) (r : ℕ)
    (P : PolynomialGroup σ hnil) (Q : VectorPolynomial σ ℚ L)
    (hP : P.coord ∈ gradedPolynomialSubmodule b w v)
    (hQ : Q ∈ shiftedGradedPolynomialSubmodule b w v r) :
    dualAdjoint P Q ∈ shiftedGradedPolynomialSubmodule b w v r :=
  dualAdjoint_mem_of_invariant (gradedPolynomialSubalgebra b w hb v)
    (shiftedGradedPolynomialSubmodule b w v r)
    (fun A hA B hB => shiftedGradedPolynomialSubmodule_invariant b w hb v r A B hA hB)
    P hP Q hQ

theorem formalLogDerivative_mem_shiftedGradedPolynomialSubmodule (b : Basis ι ℝ L) (w : ι → ℕ)
    (hb : BasisHomogeneousBrackets b w) (i : σ) (P : PolynomialGroup σ hnil)
    (hP : P.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1)) :
    formalLogDerivative i P ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 :=
  formalLogDerivative_mem_of_invariant (gradedPolynomialSubalgebra b w hb (fun _ : σ => 1))
    (shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (fun A hA B hB => shiftedGradedPolynomialSubmodule_invariant b w hb _ 1 A B hA hB)
    i P hP (pderiv_mem_shiftedGradedPolynomialSubmodule b w P.coord hP i)

theorem polynomial_derivative_removal_preserves_shifted_grading
    (b : Basis ι ℝ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w)
    (i : σ) (A B : PolynomialGroup σ hnil) (small rational : VectorPolynomial σ ℚ L)
    (hA : A.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hB : B.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hsmall : small ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (hrational : rational ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1) :
    dualAdjoint A⁻¹ (small - formalLogDerivative i A) ∈
        shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 ∧
      dualAdjoint B rational - formalLogDerivative i B ∈
        shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 := by
  let W := shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1
  have hYA := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule b w hb i A hA
  have hYB := formalLogDerivative_mem_shiftedGradedPolynomialSubmodule b w hb i B hB
  constructor
  · exact dualAdjoint_mem_shiftedGradedPolynomialSubmodule b w hb _ 1 A⁻¹ _
      ((gradedPolynomialSubmodule b w _).neg_mem hA) (W.sub_mem hsmall hYA)
  · exact W.sub_mem
      (dualAdjoint_mem_shiftedGradedPolynomialSubmodule b w hb _ 1 B rational hB hrational) hYB

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem formal_polynomial_correction_step
    (b : Basis ι ℝ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w)
    (U : LieSubalgebra ℚ L) (W : Submodule ℚ L)
    (hUW : ∀ u ∈ U, ∀ v ∈ W, ⁅u, v⁆ ∈ W)
    (P A B : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (hsystem : PolynomialDerivativeSystem P small rational extra)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hAgraded : A.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hBgraded : B.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1))
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAW : ∀ α, coefficients A.coord α ∈ W)
    (hBW : ∀ α, coefficients B.coord α ∈ W)
    (hsmall : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (hrational : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1)
    (hsmallW : ∀ i α, coefficients (small i) α ∈ W)
    (hrationalW : ∀ i α, coefficients (rational i) α ∈ W)
    (hA0 : coefficients A.coord 0 = 0) (hB0 : coefficients B.coord 0 = 0) :
    let P' := A⁻¹ * P * B⁻¹
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
    let extra' := fun i => dualAdjoint A⁻¹ (extra i)
    P'.coord = bchRemove s A.coord P.coord B.coord ∧
      A * P' * B = P ∧
      coefficients P'.coord 0 = coefficients P.coord 0 ∧
      P'.coord ∈ gradedPolynomialSubmodule b w (fun _ : σ => 1) ∧
      (∀ α, coefficients P'.coord α ∈ U) ∧
      PolynomialDerivativeSystem P' small' rational' extra' ∧
      (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1 ∧
        rational' i ∈ shiftedGradedPolynomialSubmodule b w (fun _ : σ => 1) 1) ∧
      (∀ i α, coefficients (small' i) α ∈ W ∧ coefficients (rational' i) α ∈ W) ∧
      ∀ j, 0 < j → ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 →
        coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) (small' i)) α = 0 ∧
        coefficients (VectorPolynomial.map ((basisGradeProjection b w j).restrictScalars ℚ) (rational' i)) α = 0 := by
  dsimp only
  have hshift (i : σ) := polynomial_derivative_removal_preserves_shifted_grading
    b w hb i A B (small i) (rational i) hAgraded hBgraded (hsmall i) (hrational i)
  have hcoeff (i : σ) := polynomial_derivative_removal_preserves_coefficients
    U W hUW i A B (small i) (rational i) hAU hBU hAW hBW (hsmallW i) (hrationalW i)
  refine ⟨rfl, ?_, bchRemove_constant hnil A.coord P.coord B.coord hA0 hB0,
    bchRemove_mem_gradedPolynomialSubmodule b w hb _ s A.coord P.coord B.coord
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A.coord P.coord B.coord hAU hPU hBU,
    PolynomialDerivativeSystem.remove P A B small rational extra hsystem, hshift,
    (fun i α => ⟨(hcoeff i).1 α, (hcoeff i).2 α⟩), ?_⟩
  · group
  · intro j hj i α hα
    exact ⟨shifted_one_projection_homogeneous b w _ (hshift i).1 hj α hα,
      shifted_one_projection_homogeneous b w _ (hshift i).2 hj α hα⟩

end Erdos3

end

end OAI
