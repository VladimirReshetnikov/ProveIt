/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.SharedFreeComparisonOrbit
import OAI.Combinatorics.Progressions.Linear.SharedFreeComparisonBasis

namespace OAI

section

namespace Erdos3

theorem four_projection_petal_add_invariant
    {R I E : Type*} {V : I → Type*} [CommRing R]
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [AddCommGroup E]
    (f : (∀ i, V i) → E) (K : ∀ i, Submodule R (Fin 4 → V i))
    (hK : ∀ z : ∀ i, Fin 4 → V i, (∀ i, z i ∈ K i) → fourFunctionDifference f z = 0)
    (x p : ∀ i, V i) (hx : ∀ i, x i ∈ (K i).map (LinearMap.proj 0))
    (hp : ∀ i, LinearMap.single R (fun _ : Fin 4 => V i) 0 (p i) ∈ K i) :
    f (x + p) = f x := by
  classical
  have hlift (i : I) : ∃ z ∈ K i, z 0 = x i := hx i
  choose z hz hz0 using hlift
  let y (i : I) := z i + LinearMap.single R (fun _ : Fin 4 => V i) 0 (p i)
  have hy (i : I) : y i ∈ K i := (K i).add_mem (hz i) (hp i)
  have hy0 : (fun i => y i 0) = x + p := by
    funext i
    simp only [y, Pi.add_apply, LinearMap.single_apply, Pi.single_eq_same, hz0]
  have hy1 : (fun i => y i 1) = fun i => z i 1 := by
    funext i
    simp [y, LinearMap.single_apply]
  have hy2 : (fun i => y i 2) = fun i => z i 2 := by
    funext i
    simp [y, LinearMap.single_apply]
  have hy3 : (fun i => y i 3) = fun i => z i 3 := by
    funext i
    simp [y, LinearMap.single_apply]
  have h₀ := hK z hz
  have h₁ := hK y hy
  rw [fourFunctionDifference, hy0, hy1, hy2, hy3] at h₁
  rw [fourFunctionDifference, show (fun i => z i 0) = x from funext hz0] at h₀
  simp only [sub_eq_add_neg] at h₀ h₁
  exact add_right_cancel (add_right_cancel (add_right_cancel (h₁.trans h₀.symm)))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem realifyCoordinateMap_eq_coordinates
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (φ : V →ₗ[ℚ] (ι → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap φ x = realRationalCoordinateEquiv (φ.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    funext i
    rw [realifyCoordinateMap_tmul, LinearMap.baseChange_tmul, realRationalCoordinateEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_controlled_subspace_image_section
    {μ ι κ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hφH : ∀ j i, RationalHeightLE (φ (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      (∀ y, σ y ∈ U.baseChange ℝ) ∧
      (∀ x ∈ U.baseChange ℝ,
        realifyCoordinateMap φ (σ (realifyCoordinateMap φ x)) = realifyCoordinateMap φ x) ∧
      (∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤
        Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18) * ‖y‖) ∧
      ∀ y ∈ realDenominatorGrid l, (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
  classical
  let A : Matrix ι κ ℚ := fun i j => φ (v j) i
  let B : Matrix μ κ ℚ := fun i j => b.repr (v j) i
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH (fun i j => hφH j i)
  let σ := (b.baseChange ℝ).equivFun.symm.toLinearMap.comp
    ((Matrix.mulVecLin (fun i j => (B i j : ℝ))).comp
      (Matrix.mulVecLin (fun i j => (S i j : ℝ))))
  have hσ (y : ι → ℝ) :
      σ y = realGeneratorCombination v ((fun i j => (S i j : ℝ)) *ᵥ y) := by
    apply (b.baseChange ℝ).equivFun.injective
    change (b.baseChange ℝ).equivFun ((b.baseChange ℝ).equivFun.symm
      ((fun i j => (B i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y))) = _
    rw [LinearEquiv.apply_symm_apply, realGeneratorCombination_coordinates]
  have hcoord (y : ι → ℝ) : (b.baseChange ℝ).equivFun (σ y) =
      (fun i j => (B i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y) := by
    rw [hσ, realGeneratorCombination_coordinates]
  have hvU (j : κ) : v j ∈ U := hv ▸ Submodule.subset_span (Set.mem_range_self j)
  have hvφ : Submodule.span ℚ (Set.range (fun j => φ (v j))) = U.map φ := by
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hBden : (matrixDenominator B : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power B hp 1 hμ hκ
      (fun i j => (Nat.cast_le.mpr (hvH j i).2).trans hHp')
  have hSden := real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hBnorm (y : κ → ℝ) :
      ‖(fun i j => (B i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hvH j i).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨σ, matrixDenominator B * (matrixDenominator S * l),
    Nat.mul_pos (matrixDenominator_pos B) (Nat.mul_pos (matrixDenominator_pos S) hl),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hBden hSden (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro y
    rw [hσ]
    exact realGeneratorCombination_mem U v hvU _
  · intro x hx
    have himg : realifyCoordinateMap φ x ∈
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
      rw [← realRationalCoordinateSpan_eq_image (U.map φ) (fun j => φ (v j)) hvφ,
        realifyCoordinateMap_eq_coordinates]
      refine ⟨φ.baseChange ℝ x, ?_, rfl⟩
      rw [realification_map]
      exact ⟨x, hx, rfl⟩
    rw [hσ, realifyCoordinateMap_eq_coordinates, realGeneratorCombination_map_coordinates]
    exact real_matrix_image_section_apply A S hS _ himg
  · intro y
    rw [hcoord]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * ‖(fun i j => (S i j : ℝ)) *ᵥ y‖ := hBnorm _
      _ ≤ Real.exp ((p + 2) ^ 3) * (Real.exp ((p + 2) ^ 18) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (real_image_section_norm_bound S H hSH hp hι hκ hHp y)
          (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]
  · intro y hy
    rw [hcoord]
    exact real_matrix_denominator_grid B _ _ (real_matrix_denominator_grid S l y hy)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realify_basis_coordinates
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap b.equivFun.toLinearMap x = (b.baseChange ℝ).equivFun x := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    funext i
    rw [realifyCoordinateMap_tmul]
    change a * (b.repr v i : ℝ) = (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] v) i
    rw [Basis.baseChange_repr_tmul]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_controlled_subspace_projector
    {μ κ V : Type*} [Fintype μ] [Fintype κ] [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (l : ℕ) (hl : 0 < l)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ j i, rationalLogHeight (b.repr (v j) i) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := p + 1
    ∃ (P : (ℝ ⊗[ℚ] V) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 3 + (q + 2) ^ 36) ∧
      (∀ x, P x ∈ U.baseChange ℝ) ∧ (∀ x ∈ U.baseChange ℝ, P x = x) ∧
      (∀ x, ‖(b.baseChange ℝ).equivFun (P x)‖ ≤
        Real.exp ((q + 2) ^ 3 + (q + 2) ^ 18) * ‖(b.baseChange ℝ).equivFun x‖) ∧
      ∀ x, (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
        (b.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
  intro q
  have hpq : p ≤ q := by dsimp [q]; linarith
  obtain ⟨σ, m, hm, hmp, hσU, hσfix, hσnorm, hσgrid⟩ :=
    exists_controlled_subspace_image_section b U v hv b.equivFun.toLinearMap
      (one_le_ceil_exp p) hl (fun j i => rationalHeightLE_ceil_exp (hvH j i))
      (fun j i => rationalHeightLE_ceil_exp (hvH j i))
      (hp.trans hpq) (hμ.trans hpq) (hμ.trans hpq) (hκ.trans hpq)
      (ceil_exp_le_exp_add_one hp) (hlp.trans (Real.exp_le_exp.mpr hpq))
  let P := σ.comp (b.baseChange ℝ).equivFun.toLinearMap
  refine ⟨P, m, hm, hmp, (fun x => hσU _), ?_, (fun x => hσnorm _), ?_⟩
  · intro x hx
    apply (b.baseChange ℝ).equivFun.injective
    change (b.baseChange ℝ).equivFun (σ ((b.baseChange ℝ).equivFun x)) = _
    simpa only [realify_basis_coordinates] using hσfix x hx
  · intro x hx
    exact hσgrid _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_logHeight_subspace_image_section
    {μ ι κ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hμ : (Fintype.card μ : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ j i, rationalLogHeight (b.repr (v j) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (φ (b i) j) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    let t := (p + 2) ^ 4 + 1
    ∃ (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
      (∀ y, σ y ∈ U.baseChange ℝ) ∧
      (∀ x ∈ U.baseChange ℝ,
        realifyCoordinateMap φ (σ (realifyCoordinateMap φ x)) = realifyCoordinateMap φ x) ∧
      (∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤
        Real.exp ((t + 2) ^ 3 + (t + 2) ^ 18) * ‖y‖) ∧
      ∀ y ∈ realDenominatorGrid l, (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
  intro t
  have hp4 : p ≤ (p + 2) ^ 4 := le_power_budget hp (by decide)
  have hpt : p ≤ t := hp4.trans (le_add_of_nonneg_right (by norm_num))
  have ht : 0 ≤ t := hp.trans hpt
  apply exists_controlled_subspace_image_section b U v hv φ
    (one_le_ceil_exp ((p + 2) ^ 4)) hl _ _ ht (hμ.trans hpt) (hι.trans hpt) (hκ.trans hpt)
    (ceil_exp_le_exp_add_one (by positivity)) (hlp.trans (Real.exp_le_exp.mpr hpt))
  · intro j i
    exact rationalHeightLE_ceil_exp ((hvH j i).trans hp4)
  · intro j i
    apply rationalHeightLE_ceil_exp
    exact linearMap_coordinate_logHeight b (Pi.basisFun ℚ ι) φ hp hμ hφH (v j) (hvH j) i

end Erdos3

end

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_native_pair_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L I : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))]
      (r d : ℕ) (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ (Fin 2 → L))
      (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
      (p : ℝ), 2 ≤ p → T.ComplexityLE p →
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => D.basis)).repr
        (B j a : Fin 2 → L) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (T.realSubgroup s r) I p,
      let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
      ∃ E : RationalFilteredNilmanifold (Algebra S r) s (finrank ℚ (Algebra S r)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = filtration S T.filtration.rank_le_degree ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => D)).basis.repr
            (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ (pi (fun _ : Fin 2 => D)).lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) (I × I) ((p + C) ^ C),
             V.frequency = (pairDifferenceFunctional U.frequency).comp φ.toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_model s
  let K₀ : Polynomial ℕ := (Polynomial.X + 2) ^ 2 +
    (Polynomial.X + (Polynomial.X ^ 2 + Polynomial.X + 3) ^ 2 + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ _ _ _ _ r d D T S B hS p hp hT hB U φ
  have hp₀ : 0 ≤ p := by linarith
  let P := p + (p ^ 2 + p + 3) ^ 2 + 2
  let K := (p + 2) ^ 2 + P
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpP : p ≤ P := by dsimp only [P]; nlinarith [sq_nonneg (p ^ 2 + p + 3)]
  have hPK : P ≤ K := le_add_of_nonneg_left (sq_nonneg (p + 2))
  have hGK : (p + 2) ^ 2 ≤ K := le_add_of_nonneg_right hP
  have hK : 0 ≤ K := hP.trans hPK
  have hbound : (K + a) ^ a ≤ (p + C) ^ C := by
    simpa [K₀, K, P, Polynomial.eval₂_pow] using hbudget p hp₀
  let D₂ := pi (fun _ : Fin 2 => D)
  let T₂ := piRank (fun _ : Fin 2 => D) (fun _ => T)
  have hT₂ : T₂.ComplexityLE K :=
    (piRank_complexity (fun _ : Fin 2 => D) (fun _ => T) hp₀
      (by simpa using hp) (fun _ => hT)).mono T₂ hGK
  have hB₂ (j : Fin s) (k : Fin (finrank ℚ (S j))) (i) :
      rationalLogHeight (D₂.basis.repr (B j k : Fin 2 → L) i) ≤ K := by
    change rationalLogHeight ((productFinBasis (fun _ : Fin 2 => D)).repr _ i) ≤ K
    rw [productFinBasis, Basis.repr_reindex_apply]
    exact (hB j k _).trans (hpP.trans hPK)
  obtain ⟨E, Q, hQ, hQc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree (Fin 2 → L) (I × I) r _ D₂ T₂ S B hS K hK hT₂ hB₂
      ((U.paired T hp hT.1).mono hPK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  exact ⟨E, Q, hQ, hQc.mono Q hbound, hcentral, ⟨frame.mono hbound⟩,
    (fun i j => (hmatrix i j).trans hbound), hlattice, V.mono hbound, hfreq, hobs⟩

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_coefficientFreeSpan_projector (hs : 1 ≤ s) (d : Fin s)
    (l : ℕ) (hl : 0 < l) {A : ℝ} (hA : 0 ≤ A) (hQA : Q ≤ A)
    (hdim : (finrank ℚ D.CoefficientFreeLieAlgebra : ℝ) ≤ A)
    (hlA : (l : ℝ) ≤ Real.exp A) :
    let t := A + 1
    ∃ (P : (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) →ₗ[ℝ]
        (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
      (∀ x, P x ∈ (D.coefficientFreeSpan d).baseChange ℝ) ∧
      (∀ x ∈ (D.coefficientFreeSpan d).baseChange ℝ, P x = x) ∧
      (∀ x, ‖(e.baseChange ℝ).equivFun (P x)‖ ≤
        Real.exp ((t + 2) ^ 3 + (t + 2) ^ 18) * ‖(e.baseChange ℝ).equivFun x‖) ∧
      ∀ x, (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
        (e.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis e F hs d
  have hcspan : Submodule.span ℚ (Set.range (fun j => (c j : D.CoefficientFreeLieAlgebra))) =
      D.coefficientFreeSpan d := by
    change Submodule.span ℚ (Set.range ((D.coefficientFreeSpan d).subtype ∘ c)) = _
    rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  apply exists_controlled_subspace_projector e (D.coefficientFreeSpan d)
    (fun j => (c j : D.CoefficientFreeLieAlgebra)) hcspan l hl hA
  · simpa only [Fintype.card_fin] using hdim
  · have hd : (finrank ℚ (D.coefficientFreeSpan d) : ℝ) ≤
        finrank ℚ D.CoefficientFreeLieAlgebra := by
      exact_mod_cast Submodule.finrank_le (D.coefficientFreeSpan d)
    simpa only [Fintype.card_fin] using hd.trans hdim
  · exact fun j i => (hc j i).trans hQA
  · exact hlA

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreeCommonCorrectionBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let Λ := (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let t := (q + p + Λ) + 1
  (t + 2) ^ 3 + (t + 2) ^ 36 + Λ

theorem refined_firstProjection_le_common
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C D : Submodule R V) (hDC : D ≤ C) (K : Submodule R (Fin 4 → V)) :
    (fourRefinedRelation C D K).map (LinearMap.proj 0) ≤ C := by
  rintro v ⟨w, hw, rfl⟩
  exact ((mem_fourCommonModulo C D w).mp (fourRefinedRelation_le_common C D hDC K hw)).1 0

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_filtered_common
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let L := sharedFreeCommonCorrectionBudget s Q P'
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      ∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp L ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        e d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        q d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp L / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d) := by
  intro L
  classical
  obtain ⟨l, γ, e, q, hdata⟩ :=
    D.exists_shared_free_common_projection E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let A := Q + P' + Λ
  let t := A + 1
  let C := (t + 2) ^ 3 + (t + 2) ^ 18
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hP' (Nat.cast_nonneg _)) _
  have hA : 0 ≤ A := add_nonneg (add_nonneg hQ hP') hΛ
  have hQA : Q ≤ A := (le_add_of_nonneg_right hP').trans (le_add_of_nonneg_right hΛ)
  have hPA : P' ≤ A := (le_add_of_nonneg_left hQ).trans (le_add_of_nonneg_right hΛ)
  have hΛA : Λ ≤ A := le_add_of_nonneg_left (add_nonneg hQ hP')
  have hprojectors (d : Fin s) :
      ∃ (P : (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) →ₗ[ℝ]
          (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
        (∀ x, P x ∈ (D.coefficientFreeSpan d).baseChange ℝ) ∧
        (∀ x ∈ (D.coefficientFreeSpan d).baseChange ℝ, P x = x) ∧
        (∀ x, ‖(E.basis.baseChange ℝ).equivFun (P x)‖ ≤
          Real.exp C * ‖(E.basis.baseChange ℝ).equivFun x‖) ∧
        ∀ x, (E.basis.baseChange ℝ).equivFun x ∈ realDenominatorGrid (l d) →
          (E.basis.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
    exact D.exists_coefficientFreeSpan_projector E.basis F (by omega) d
      (l d) (hdata d).1 hA hQA ((hT.1.1.trans hQP').trans hPA)
      ((hdata d).2.1.trans (Real.exp_le_exp.mpr hΛA))
  choose P m hm hmb hPU hPfix hPnorm hPgrid using hprojectors
  have ht : 0 ≤ t := add_nonneg hA zero_le_one
  have h18 : (t + 2) ^ 18 ≤ (t + 2) ^ 36 := pow_le_pow_right₀ (by linarith only [ht]) (by decide)
  have hL : L = (t + 2) ^ 3 + (t + 2) ^ 36 + Λ := rfl
  have hCL : C + Λ ≤ L := add_le_add (add_le_add (le_refl ((t + 2) ^ 3)) h18) (le_refl Λ)
  refine ⟨m, γ, (fun d => P d (e d)), (fun d => P d (q d)), ?_⟩
  intro d
  obtain ⟨_hl, _hlb, hγ, heq, herr, hgrid⟩ := hdata d
  have hγC : γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ :=
    Submodule.baseChange_mono ℝ
      (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan d) _) hγ
  have hξC : coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.coefficientFreeSpan d).baseChange ℝ :=
    Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d)
  have hsum : e d + q d ∈ (D.coefficientFreeSpan d).baseChange ℝ := by
    have hh : e d + q d = coefficients ξ.log (Finsupp.single () (d.val + 1)) - γ d := by
      rw [heq]
      abel
    rw [hh]
    exact ((D.coefficientFreeSpan d).baseChange ℝ).sub_mem hξC hγC
  have hsumfix := hPfix d (e d + q d) hsum
  rw [map_add] at hsumfix
  refine ⟨hm d, (hmb d).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hΛ)),
    hγ, hγC, hPU d _, hPU d _, ?_, ?_, hPgrid d _ hgrid⟩
  · calc
      _ = γ d + (e d + q d) := by rw [heq, add_assoc]
      _ = γ d + (P d (e d) + P d (q d)) := by rw [hsumfix]
      _ = _ := (add_assoc _ _ _).symm
  · calc
      _ ≤ Real.exp C * ‖(E.basis.baseChange ℝ).equivFun (e d)‖ := hPnorm d _
      _ ≤ Real.exp C * (Real.exp Λ / (N : ℝ) ^ (d.val + 1)) :=
        mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le
      _ = Real.exp (C + Λ) / (N : ℝ) ^ (d.val + 1) := by rw [← mul_div_assoc, ← Real.exp_add]
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCL) (pow_nonneg (Nat.cast_nonneg N) _)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_space_top_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (z : Fin n → Fin 2 → D.CoefficientFreeLieAlgebra)
    (hz : ∀ i, z i ∈ petalComparisonSpace
      ((fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
        (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
      (fourPetalSpace (D.dependentFreeSpan (d i))
        (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
          (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)))
      (D.coefficientFreeFiltration.layer ((d i).val + 1) 2)) :
    pairDifferenceFunctional (B.freeFrequency D) (lieTreeEval z a) = 0 := by
  have hC (j : Fin s) :
      (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
        (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩)).map (LinearMap.proj 0) ≤
          D.coefficientFreeFiltration.layer (j.val + 1) 1 :=
    (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan j) _).trans
      (D.coefficientFreeSpan_le_layer j)
  apply petalComparisonSpace_top_tree D.coefficientFreeFiltration (fun i => (d i).val + 1)
    _ _ (fun i => hC (d i))
    (fun i => (fourPetalSpace_le_first _ _).trans (hC (d i))) (B.freeFrequency D) a hd hr _ z hz
  intro c p hc hp
  apply four_projection_petal_add_invariant
    (fun x => B.freeFrequency D (lieTreeEval x a))
    (fun i => fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
      (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩))
    (B.correlation_refined_four_identity D E T hbQ hT V g hg D' hfreq n d a hd hr) c p hc
  exact fun i => ((mem_fourPetalSpace _ _ _).mp (hp i)).2

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

noncomputable def comparisonCoefficientSpace (d : Fin s) :
    Submodule ℚ (Fin 2 → D.CoefficientFreeLieAlgebra) :=
  petalComparisonSpace
    ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0))
    (fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))
    (D.coefficientFreeFiltration.layer (d.val + 1) 2)

theorem comparisonCoefficientSpace_le_layer
    (hTfil : T.filtration = D.coefficientFreeFiltration) (d : Fin s) :
    D.comparisonCoefficientSpace E T hbQ hT V g hg D' d ≤
      (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration.layer
        (d.val + 1) 0 := by
  have hC : (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0) ≤
      D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
    (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan d) _).trans
      (D.coefficientFreeSpan_le_layer d)
  change petalComparisonSpace _ _ _ ≤
    Submodule.pi Set.univ (fun _ : Fin 2 => T.filtration.layer (d.val + 1) 0)
  rw [hTfil, D.coefficientFreeFiltration.rank_zero_eq_one]
  exact petalComparisonSpace_le_pi _ _ _ _ hC
    ((fourPetalSpace_le_first _ _).trans hC)
    (D.coefficientFreeFiltration.lex_antitone (Or.inr ⟨rfl, by omega⟩))

include F in
theorem exists_comparisonCoefficientBases
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    ∃ B : ∀ d : Fin s, Basis (Fin (finrank ℚ
        (D.comparisonCoefficientSpace E T hbQ hT V g hg D' d))) ℚ
        (D.comparisonCoefficientSpace E T hbQ hT V g hg D' d),
      ∀ d a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B d a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P' := by
  classical
  choose B hB using fun d => D.exists_sharedFreeComparisonSpace_basis E T hbQ hT F V g hg D'
    hTfil hs hP' hQP' d
  exact ⟨B, hB⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def nativePairModelConstant (s : ℕ) : ℕ :=
  (SubspaceFreeLift.exists_native_pair_model.{0, 0} s).choose

noncomputable def sharedFreeComparisonModelBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (q + 2 + sharedFreeComparisonBasisBudget q p + nativePairModelConstant s) ^ nativePairModelConstant s

theorem sharedFreeComparisonBasisBudget_nonneg {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    0 ≤ sharedFreeComparisonBasisBudget q p := by
  have hA := add_nonneg hq (fourRefinementBasisBudget_nonneg
    (add_nonneg hq (coefficientFourHeightBudget_nonneg hp)))
  exact add_nonneg hA (preimageBasisBudget_nonneg (mul_nonneg (by norm_num) hA))

theorem exists_sharedFreeComparisonModelBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeComparisonModelBudget s q p ≤ (p + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_sharedFreeComparisonBasisBudget_bound
  let a := nativePairModelConstant s
  let K : Polynomial ℕ := Polynomial.X + 2 + (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hsmall : q + 2 + sharedFreeComparisonBasisBudget q p + a ≤
      p + 2 + (p + b) ^ b + a := by linarith [hb q p hq hqp hp]
  have hzero : 0 ≤ q + 2 + sharedFreeComparisonBasisBudget q p + a := by
    have := sharedFreeComparisonBasisBudget_nonneg hq hp
    positivity
  apply (pow_le_pow_left₀ hzero hsmall a).trans
  simpa [K, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_native_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
          (finrank ℚ (SubspaceFreeLift.Algebra S r)),
        ∃ U : M.DegreeRankStructure r,
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧ IsCentralLieBasis M.basis ∧
          Nonempty (FreeCoordinateFrame M.basis (sharedFreeComparisonModelBudget s Q P')) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => E)).basis.repr
            (φ (M.basis j)) i) ≤ sharedFreeComparisonModelBudget s Q P') ∧
          M.lattice ≤ (pi (fun _ : Fin 2 => E)).lattice.comap (mapOfSteps
            (hL := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s r)
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             Z.frequency = (pairDifferenceFunctional V.frequency).comp φ.toLinearMap ∧
             ∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  intro S hS
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hH := sharedFreeComparisonBasisBudget_nonneg hQ hP'
  let K := Q + 2 + sharedFreeComparisonBasisBudget Q P'
  have h2 : 2 ≤ K := by dsimp only [K]; linarith
  have hQK : Q ≤ K := by dsimp only [K]; linarith
  have hHK : sharedFreeComparisonBasisBudget Q P' ≤ K := by dsimp only [K]; linarith
  obtain ⟨B, hB⟩ := D.exists_comparisonCoefficientBases E T hbQ hT F V g hg D' hTfil hs hP' hQP'
  refine ⟨B, hB, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fin 2 → D.CoefficientFreeLieAlgebra))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → D.CoefficientFreeLieAlgebra)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (Pi.basis (fun _ : Fin 2 => E.basis))
  exact (SubspaceFreeLift.exists_native_pair_model s).choose_spec.2
    D.CoefficientFreeLieAlgebra (Fin W.family.outputDim) r _ E T S B hS K h2
    (hT.mono T hQK) (fun j a i => (hB j a i).trans hHK) (V.mono hQK)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem exists_native_factored_comparison_orbit
    (hTfil : T.filtration = D.coefficientFreeFiltration) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1)
    (hK0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1)
    (hU0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1)
    (hA : ∀ d : Fin s, coefficients A.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    let a : Fin 2 → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1) := ![A * K * U, A]
    ∀ (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
        (finrank ℚ (SubspaceFreeLift.Algebra S r))) (Q' : M.DegreeRankStructure r),
      Q'.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      let φ := SubspaceFreeLift.evaluation S B
        (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
        (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
          (SubspaceFreeLift.generatorSpan S r j).baseChange ℝ) ∧
        ∀ i x, RationalFilteredNilmanifold.productProjectionHom (fun _ : Fin 2 => E) i
          (NilpotentLieBCHGroup.realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (RationalFilteredNilmanifold.pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ
            (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i) := by
  intro S hS a B M Q' hQ' φ
  apply SubspaceFreeLift.exists_native_pair_orbit E T S B hS M Q' hQ' a
  · intro i
    fin_cases i
    · change E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A * K * U) = 1
      rw [map_mul, map_mul, hA0, hK0, hU0, mul_one, mul_one]
    · exact hA0
  · intro j
    have h := D.paired_affine_orbit_coefficient_mem_comparison E T hbQ hT V g hg D'
      hTfil hs A K U hA hK hU j
    have heq : (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) =
        ![coefficients (A * K * U).log (Finsupp.single () (j.val + 1)),
          coefficients A.log (Finsupp.single () (j.val + 1))] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact h

end Erdos3.NativeRankRelation.CommonData

end

end OAI
