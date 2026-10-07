/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.FourBalancedDual
import OAI.Combinatorics.Progressions.Linear.NativeSharedFreeRankRelation

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

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

noncomputable def realCoefficientFourSpace (d : Fin (s + 1)) :
    Submodule ℝ (Fin 4 → ℝ ⊗[ℚ] W.L) :=
  ((D.coefficientFourSpace d).baseChange ℝ).map
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).toLinearMap

theorem real_coefficient_four_tensor_frequency (n : ℕ) (d : Fin n → Fin (s + 1))
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun j => (d j).val) a = s)
    (hr : a.length = r) (v : Fin n → ℝ ⊗[ℚ] (Fin 4 → W.L))
    (hv : ∀ j, v j ∈ (D.coefficientFourSpace (d j)).baseChange ℝ) :
    fourFunctionDifference (fun x => realifyFunctional W.vertical.frequency (lieTreeEval x a))
      (fun j k => (LinearMap.proj k).baseChange ℝ (v j)) = 0 := by
  classical
  let F := W.rank.filtration
  have hlift (j : Fin n) : ∃ w : ℝ ⊗[ℚ] F.fourHorizontalLayer (d j).val,
      (F.fourHorizontalMap (d j).val).baseChange ℝ w ∈ (D.horizontal (d j)).baseChange ℝ ∧
        (F.fourHorizontalLayer (d j).val).subtype.baseChange ℝ w = v j := by
    have h := hv j
    rw [coefficientFourSpace, realification_map, realification_comap] at h
    exact h
  choose w hw he using hlift
  have hφ : ∀ d x, x ∈ F.fourHorizontalLayer d → ∀ k,
      (LieHom.id : (Fin 4 → W.L) →ₗ⁅ℚ⁆ (Fin 4 → W.L)) x k ∈ F.layer d 1 := by
    intro d x hx
    exact (F.mem_fourHorizontalLayer d x).mp hx
  let u (k : Fin 4) (j : Fin n) : (F.layer (d j).val 1).baseChange ℝ :=
    F.realLayerProjection F.fourHorizontalLayer LieHom.id hφ (d j).val k
      (realificationSubmoduleEquiv (F.fourHorizontalLayer (d j).val) (w j))
  have hmap (k : Fin 4) (j : Fin n) :
      (LinearMap.proj k).baseChange ℝ ((F.fourHorizontalMap (d j).val).baseChange ℝ (w j)) =
        F.realHorizontalMap (d j).val (u k j) :=
    F.real_layerHorizontalMap_component F.fourHorizontalLayer LieHom.id hφ (d j).val k (w j)
  have hval (k : Fin 4) (j : Fin n) : (u k j).val = (LinearMap.proj k).baseChange ℝ (v j) := by
    change (LinearMap.proj k).baseChange ℝ
      ((F.fourHorizontalLayer (d j).val).subtype.baseChange ℝ (w j)) = _
    rw [he j]
  have hvalue (k : Fin 4) :
      F.realHorizontalTreeValue (fun j => (d j).val) a
          (fun j => (LinearMap.proj k).baseChange ℝ
            ((F.fourHorizontalMap (d j).val).baseChange ℝ (w j))) =
        lieTreeEval (fun j => (LinearMap.proj k).baseChange ℝ (v j)) a := by
    simp_rw [hmap k]
    rw [F.realHorizontalTreeValue_map _ a hd hr (u k)]
    simp only [hval]
  have h := D.real_horizontal_frequency n d a hd hr
    (fun j => (F.fourHorizontalMap (d j).val).baseChange ℝ (w j)) hw
  dsimp only [F] at h hvalue
  simpa only [fourFunctionDifference, hvalue] using h

theorem real_coefficient_four_frequency (n : ℕ) (d : Fin n → Fin (s + 1))
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun j => (d j).val) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → ℝ ⊗[ℚ] W.L)
    (hv : ∀ j, v j ∈ D.realCoefficientFourSpace (d j)) :
    fourFunctionDifference (fun x => realifyFunctional W.vertical.frequency (lieTreeEval x a)) v = 0 := by
  classical
  have hlift (j : Fin n) : ∃ w ∈ (D.coefficientFourSpace (d j)).baseChange ℝ,
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) w = v j := hv j
  choose w hw he using hlift
  have h := D.real_coefficient_four_tensor_frequency n d a hd hr w hw
  have hproj (x : ℝ ⊗[ℚ] (Fin 4 → W.L)) (k : Fin 4) :
      (LinearMap.proj k).baseChange ℝ x =
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) x k := by
    induction x using TensorProduct.inductionOn with
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hcoord (j : Fin n) (k : Fin 4) : (LinearMap.proj k).baseChange ℝ (w j) = v j k :=
    (hproj (w j) k).trans (congrFun (he j) k)
  simpa only [hcoord] using h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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

theorem mem_real_coefficientFourSpace (d : Fin (s + 1))
    (v : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) v.val ∈
        D.realCoefficientFourSpace d ↔
      W.rank.filtration.realFourHorizontalMap d.val v ∈ (D.horizontal d).baseChange ℝ := by
  obtain ⟨x, rfl⟩ :=
    (realificationSubmoduleEquiv (W.rank.filtration.fourHorizontalLayer d.val)).surjective v
  rw [W.rank.filtration.realFourHorizontalMap_baseChange]
  unfold realCoefficientFourSpace
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    realificationSubmoduleEquiv_coe, coefficientFourSpace, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have h := realification_subtype_injective (W.rank.filtration.fourHorizontalLayer d.val) he
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.finite_combined_free_sunflower {J : Type*} [Fintype J]
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : J → D.CoefficientFreeLieAlgebra) (hv : ∀ i, v i ∈ D.coefficientFreeSpan (d i))
    (i j : J) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ D.dependentFreeSpan (d i)) (hvj : v j ∈ D.dependentFreeSpan (d j)) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  classical
  let e := Fintype.equivFin J
  have hweight : lieTreeWeight (fun k => (d (e.symm k)).val + 1) (FreeMagma.map e a) = s := by
    rw [lieTreeWeight_relabel]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hd
  have hsupp (k : J) (hk : k ∈ lieTreeSupport a) : e k ∈ lieTreeSupport (FreeMagma.map e a) := by
    rw [lieTreeSupport_relabel]
    exact ⟨k, hk, rfl⟩
  have h := B.combined_free_sunflower D (Fintype.card J) (fun k => d (e.symm k))
    (FreeMagma.map e a) hweight ((lieTreeLength_relabel e a).trans hr)
    (fun k => v (e.symm k)) (fun k => hv (e.symm k)) (e i) (e j)
    (fun h => hij (e.injective h)) (hsupp i hi) (hsupp j hj)
    (by simpa only [Equiv.symm_apply_apply] using hvi)
    (by simpa only [Equiv.symm_apply_apply] using hvj)
  simpa only [lieTreeEval_relabel, Function.comp_def, Equiv.symm_apply_apply] using h

theorem CoefficientBases.real_finite_combined_free_sunflower {J : Type*} [Fintype J]
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (v : J → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (D.coefficientFreeSpan (d i)).baseChange ℝ)
    (i j : J) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ (D.dependentFreeSpan (d i)).baseChange ℝ)
    (hvj : v j ∈ (D.dependentFreeSpan (d j)).baseChange ℝ) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval v a) = 0 := by
  classical
  let e := Fintype.equivFin J
  have hweight : lieTreeWeight (fun k => (d (e.symm k)).val + 1) (FreeMagma.map e a) = s := by
    rw [lieTreeWeight_relabel]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hd
  have hsupp (k : J) (hk : k ∈ lieTreeSupport a) : e k ∈ lieTreeSupport (FreeMagma.map e a) := by
    rw [lieTreeSupport_relabel]
    exact ⟨k, hk, rfl⟩
  have h := B.real_combined_free_sunflower D (Fintype.card J) (fun k => d (e.symm k))
    (FreeMagma.map e a) hweight ((lieTreeLength_relabel e a).trans hr)
    (fun k => v (e.symm k)) (fun k => hv (e.symm k)) (e i) (e j)
    (fun h => hij (e.injective h)) (hsupp i hi) (hsupp j hj)
    (by simpa only [Equiv.symm_apply_apply] using hvi)
    (by simpa only [Equiv.symm_apply_apply] using hvj)
  simpa only [lieTreeEval_relabel, Function.comp_def, Equiv.symm_apply_apply] using h

theorem CoefficientBases.exists_free_tree_linearization {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (x : J → D.CoefficientFreeLieAlgebra) (hx : ∀ i, x i ∈ D.coefficientFreeSpan (d i)) :
    ∃ A : (∀ i, D.dependentFreeSpan (d i)) →ₗ[ℚ] ℚ, ∀ y : ∀ i, D.dependentFreeSpan (d i),
      B.freeFrequency D (lieTreeEval (fun i => x i + (y i : D.CoefficientFreeLieAlgebra)) a) =
        B.freeFrequency D (lieTreeEval x a) + A y := by
  apply exists_linear_lieTree_expansion (B.freeFrequency D)
    (fun i => D.coefficientFreeSpan (d i)) (fun i => D.dependentFreeSpan (d i))
    (fun i => D.dependentFreeSpan_le_coefficientFreeSpan (d i)) a x hx
  intro v hv i j hij hi hj
  exact B.finite_combined_free_sunflower D (fun k => d (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a)
    ((lieTreeOccurrenceTree_weight (fun k => (d k).val + 1) a).trans hd)
    ((lieTreeOccurrenceTree_length a).trans hr) v hv i j hij
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial) hi hj

theorem CoefficientBases.exists_real_free_tree_linearization {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (x : J → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hx : ∀ i, x i ∈ (D.coefficientFreeSpan (d i)).baseChange ℝ) :
    ∃ A : (∀ i, (D.dependentFreeSpan (d i)).baseChange ℝ) →ₗ[ℝ] ℝ,
      ∀ y : ∀ i, (D.dependentFreeSpan (d i)).baseChange ℝ,
        realifyFunctional (B.freeFrequency D)
            (lieTreeEval (fun i => x i + (y i : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) a) =
          realifyFunctional (B.freeFrequency D) (lieTreeEval x a) + A y := by
  apply exists_linear_lieTree_expansion (realifyFunctional (B.freeFrequency D))
    (fun i => (D.coefficientFreeSpan (d i)).baseChange ℝ)
    (fun i => (D.dependentFreeSpan (d i)).baseChange ℝ)
    (fun i => Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_coefficientFreeSpan (d i))) a x hx
  intro v hv i j hij hi hj
  exact B.real_finite_combined_free_sunflower D (fun k => d (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a)
    ((lieTreeOccurrenceTree_weight (fun k => (d k).val + 1) a).trans hd)
    ((lieTreeOccurrenceTree_length a).trans hr) v hv i j hij
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial) hi hj

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.free_refined_four_identity {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℚ (Fin 4 → D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0)
    (v : J → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (K i)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  four_refined_affine_identity _ _ _
    (fun x hx => B.exists_free_tree_linearization D d a hd hr x hx) K hK v hv

theorem CoefficientBases.real_free_refined_four_identity {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℝ (Fin 4 → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => realifyFunctional (B.freeFrequency D) (lieTreeEval x a)) v = 0)
    (v : J → Fin 4 → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ) (K i)) :
    fourFunctionDifference (fun x => realifyFunctional (B.freeFrequency D) (lieTreeEval x a)) v = 0 :=
  four_refined_affine_identity _ _ _
    (fun x hx => B.exists_real_free_tree_linearization D d a hd hr x hx) K hK v hv

theorem CoefficientBases.free_refined_petal_vanish {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℚ (Fin 4 → D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0)
    (v : J → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (K i)).map (LinearMap.proj 0))
    (i : J) (hi : i ∈ lieTreeSupport a)
    (hvi : v i ∈ fourPetalSpace (D.dependentFreeSpan (d i))
      (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i)) (K i))) :
    B.freeFrequency D (lieTreeEval v a) = 0 := by
  apply four_single_input_vanish (fun x => B.freeFrequency D (lieTreeEval x a))
    (fun j => fourRefinedRelation (D.coefficientFreeSpan (d j)) (D.dependentFreeSpan (d j)) (K j))
    (fun w hw => B.free_refined_four_identity D d a hd hr K hK w hw) v hv i ?_ hvi.2
  intro x hx
  rw [lieTreeEval_eq_zero_of_leaf x a hi hx, map_zero]

theorem CoefficientBases.real_free_refined_petal_vanish {J : Type*}
    (d : J → Fin s) (a : FreeMagma J)
    (hd : lieTreeWeight (fun i => (d i).val + 1) a = s) (hr : a.length = r)
    (K : J → Submodule ℝ (Fin 4 → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (hK : ∀ v, (∀ i, v i ∈ K i) →
      fourFunctionDifference (fun x => realifyFunctional (B.freeFrequency D) (lieTreeEval x a)) v = 0)
    (v : J → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ) (K i)).map (LinearMap.proj 0))
    (i : J) (hi : i ∈ lieTreeSupport a)
    (hvi : v i ∈ fourPetalSpace ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
        ((D.dependentFreeSpan (d i)).baseChange ℝ) (K i))) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval v a) = 0 := by
  apply four_single_input_vanish (fun x => realifyFunctional (B.freeFrequency D) (lieTreeEval x a))
    (fun j => fourRefinedRelation ((D.coefficientFreeSpan (d j)).baseChange ℝ)
      ((D.dependentFreeSpan (d j)).baseChange ℝ) (K j))
    (fun w hw => B.real_free_refined_four_identity D d a hd hr K hK w hw) v hv i ?_ hvi.2
  intro x hx
  rw [lieTreeEval_eq_zero_of_leaf x a hi hx, map_zero]

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

theorem CoefficientBases.correlation_four_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 := by
  have h := D'.coefficient_four_frequency n (fun i => ⟨(d i).val + 1, by omega⟩)
    a hd hr v hv
  change fourFunctionDifference (fun x => V.frequency (lieTreeEval x a)) v = 0 at h
  simpa only [hfreq] using h

theorem CoefficientBases.real_correlation_four_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩) :
    fourFunctionDifference (fun x => realifyFunctional (B.freeFrequency D) (lieTreeEval x a)) v = 0 := by
  have h := D'.real_coefficient_four_frequency n (fun i => ⟨(d i).val + 1, by omega⟩)
    a hd hr v hv
  change fourFunctionDifference (fun x => realifyFunctional V.frequency (lieTreeEval x a)) v = 0 at h
  simpa only [hfreq] using h

theorem CoefficientBases.correlation_refined_four_identity
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)) :
    fourFunctionDifference (fun x => B.freeFrequency D (lieTreeEval x a)) v = 0 :=
  B.free_refined_four_identity D d a hd hr _
    (B.correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv

theorem CoefficientBases.real_correlation_refined_four_identity
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → Fin 4 → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩)) :
    fourFunctionDifference (fun x => realifyFunctional (B.freeFrequency D) (lieTreeEval x a)) v = 0 :=
  B.real_free_refined_four_identity D d a hd hr _
    (B.real_correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv

theorem CoefficientBases.correlation_refined_petal_vanish
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (fourRefinedRelation (D.coefficientFreeSpan (d i))
      (D.dependentFreeSpan (d i)) (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map
        (LinearMap.proj 0))
    (i : Fin n) (hi : i ∈ lieTreeSupport a)
    (hvi : v i ∈ fourPetalSpace (D.dependentFreeSpan (d i))
      (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
        (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩))) :
    B.freeFrequency D (lieTreeEval v a) = 0 :=
  B.free_refined_petal_vanish D d a hd hr _
    (B.correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv i hi hvi

theorem CoefficientBases.real_correlation_refined_petal_vanish
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (v : Fin n → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ i, v i ∈ (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
      ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
    (i : Fin n) (hi : i ∈ lieTreeSupport a)
    (hvi : v i ∈ fourPetalSpace ((D.dependentFreeSpan (d i)).baseChange ℝ)
      (fourRefinedRelation ((D.coefficientFreeSpan (d i)).baseChange ℝ)
        ((D.dependentFreeSpan (d i)).baseChange ℝ)
        (D'.realCoefficientFourSpace ⟨(d i).val + 1, by omega⟩))) :
    realifyFunctional (B.freeFrequency D) (lieTreeEval v a) = 0 :=
  B.real_free_refined_petal_vanish D d a hd hr _
    (B.real_correlation_four_frequency D E T hbQ hT V g hg D' hfreq n d a hd hr) v hv i hi hvi

end Erdos3.NativeRankRelation.CommonData

end

end OAI
