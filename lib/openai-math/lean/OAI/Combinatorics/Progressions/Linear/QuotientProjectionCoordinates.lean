/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Isomorphisms
import OAI.Combinatorics.Progressions.Dynamics.NativeHorizontalLiftBudget

namespace OAI

section

namespace Erdos3

open Module

variable {K V ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]

def BasisBlockInvariant (b : Basis ι K V) (c : ι → δ) (U : Submodule K V) : Prop :=
  ∀ d x, x ∈ U → basisCoordinateProjection b {i | c i = d} x ∈ U

theorem sum_basisBlockProjection [Fintype ι] [DecidableEq δ]
    (b : Basis ι K V) (c : ι → δ) (x : V) :
    ∑ d ∈ Finset.univ.image c, basisCoordinateProjection b {i | c i = d} x = x := by
  classical
  apply b.repr.injective
  ext i
  have hi : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  simp only [map_sum, Finsupp.finsetSum_apply, basisCoordinateProjection_repr]
  change (∑ d ∈ Finset.univ.image c, if c i = d then b.repr x i else 0) = b.repr x i
  simp [hi]

noncomputable def blockSpanningFamily (b : Basis ι K V) (c : ι → δ) (v : κ → V) : ι × κ → V :=
  fun z => basisCoordinateProjection b {i | c i = c z.1} (v z.2)

theorem blockSpanningFamily_repr [DecidableEq δ] (b : Basis ι K V) (c : ι → δ) (v : κ → V)
    (z : ι × κ) (i : ι) :
    b.repr (blockSpanningFamily b c v z) i = if c i = c z.1 then b.repr (v z.2) i else 0 := by
  exact basisCoordinateProjection_repr b {i | c i = c z.1} (v z.2) i

theorem blockSpanningFamily_span [Fintype ι] (b : Basis ι K V) (c : ι → δ)
    (U : Submodule K V) (v : κ → V) (hspan : Submodule.span K (Set.range v) = U)
    (hU : BasisBlockInvariant b c U) :
    Submodule.span K (Set.range (blockSpanningFamily b c v)) = U := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply hU (c z.1) (v z.2)
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← sum_basisBlockProjection b c (v j)]
    apply Submodule.sum_mem
    intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    exact Submodule.subset_span ⟨(i, j), rfl⟩

theorem blockSpanningFamily_height {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (c : ι → δ) (v : κ → V) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∀ z i, RationalHeightLE (b.repr (blockSpanningFamily b c v z) i) H := by
  classical
  intro z i
  rw [blockSpanningFamily_repr]
  split_ifs
  · exact hv z.2 i
  · exact rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V W ι κ δ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem basisBlockMap_commutes (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0) (a : δ) (x : V) :
    T (basisCoordinateProjection e {i | c i = a} x) =
      basisCoordinateProjection f {j | d j = a} (T x) := by
  classical
  have he : T.comp (basisCoordinateProjection e {i | c i = a}) =
      (basisCoordinateProjection f {j | d j = a}).comp T := by
    apply e.ext
    intro i
    apply f.repr.injective
    ext j
    by_cases hi : c i = a <;> by_cases hj : d j = a
    · simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj]
    · have hij : d j ≠ c i := fun h => hj (h.trans hi)
      simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj, hT i j hij]
    · have hij : d j ≠ c i := fun h => hi (h.symm.trans hj)
      simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj, hT i j hij]
    · simp [LinearMap.comp_apply, basisCoordinateProjection_basis, basisCoordinateProjection_repr, hi, hj]
  exact DFunLike.congr_fun he x

theorem BasisBlockInvariant.map (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0)
    (U : Submodule K V) (hU : BasisBlockInvariant e c U) :
    BasisBlockInvariant f d (U.map T) := by
  rintro a y ⟨x, hx, rfl⟩
  exact ⟨basisCoordinateProjection e {i | c i = a} x, hU a x hx,
    basisBlockMap_commutes e f c d T hT a x⟩

theorem basisBlockInvariant_ker (e : Basis ι K V) (f : Basis κ K W)
    (c : ι → δ) (d : κ → δ) (T : V →ₗ[K] W)
    (hT : ∀ i j, d j ≠ c i → f.repr (T (e i)) j = 0) :
    BasisBlockInvariant e c (LinearMap.ker T) := by
  intro a x hx
  change T (basisCoordinateProjection e {i | c i = a} x) = 0
  rw [basisBlockMap_commutes e f c d T hT a x, show T x = 0 from hx, map_zero]

theorem BasisBlockInvariant.inf (e : Basis ι K V) (c : ι → δ)
    (U Z : Submodule K V) (hU : BasisBlockInvariant e c U) (hZ : BasisBlockInvariant e c Z) :
    BasisBlockInvariant e c (U ⊓ Z) :=
  fun a x hx => ⟨hU a x hx.1, hZ a x hx.2⟩

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

section Algebra

variable {ι κ μ δ K : Type*} [Semiring K]

noncomputable def matrixBlockPart (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K) : Matrix ι κ K := by
  classical
  exact fun i j => if r i = c j then A i j else 0

theorem matrixBlockPart_eq (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) : matrixBlockPart r c A = A := by
  classical
  ext i j
  by_cases h : r i = c j
  · simp only [matrixBlockPart, h, ↓reduceIte]
  · simp only [matrixBlockPart, h, ↓reduceIte, hA i j h]

theorem matrixBlockPart_off_block (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K)
    (i : ι) (j : κ) (h : r i ≠ c j) : matrixBlockPart r c A i j = 0 := by
  classical
  simp only [matrixBlockPart, h, ↓reduceIte]

theorem matrix_mul_blockPart [Fintype κ] (r : ι → δ) (c : κ → δ) (d : μ → δ)
    (A : Matrix ι κ K) (B : Matrix κ μ K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) :
    A * matrixBlockPart c d B = matrixBlockPart r d (A * B) := by
  classical
  ext i k
  have hterm (j : κ) :
      A i j * (if c j = d k then B j k else 0) =
        if r i = d k then A i j * B j k else 0 := by
    by_cases hij : r i = c j
    · rw [hij]
      split_ifs <;> simp only [mul_zero]
    · rw [hA i j hij]
      split_ifs <;> simp only [zero_mul]
  simp only [Matrix.mul_apply, matrixBlockPart, hterm]
  by_cases h : r i = d k <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]

theorem matrix_blockPart_mul [Fintype κ] (r : ι → δ) (c : κ → δ) (d : μ → δ)
    (A : Matrix ι κ K) (B : Matrix κ μ K)
    (hB : ∀ j k, c j ≠ d k → B j k = 0) :
    matrixBlockPart r c A * B = matrixBlockPart r d (A * B) := by
  classical
  ext i k
  have hterm (j : κ) :
      (if r i = c j then A i j else 0) * B j k =
        if r i = d k then A i j * B j k else 0 := by
    by_cases hjk : c j = d k
    · rw [hjk]
      split_ifs <;> simp only [zero_mul]
    · rw [hB j k hjk]
      split_ifs <;> simp only [mul_zero]
  simp only [Matrix.mul_apply, matrixBlockPart, hterm]
  by_cases h : r i = d k <;> simp only [h, ↓reduceIte, Finset.sum_const_zero]

theorem matrixBlockPart_image_section [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ K) (S : Matrix κ ι K)
    (hA : ∀ i j, r i ≠ c j → A i j = 0) (hS : A * S * A = A) :
    A * matrixBlockPart c r S * A = A := by
  rw [matrix_mul_blockPart r c r A S hA, matrix_blockPart_mul r r c (A * S) A hA,
    hS, matrixBlockPart_eq r c A hA]

end Algebra

theorem exists_bounded_block_image_section {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ S : Matrix κ ι ℚ, A * S * A = A ∧
      (∀ i j, c i ≠ r j → S i j = 0) ∧
      ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  refine ⟨matrixBlockPart c r S, matrixBlockPart_image_section r c A S hblock hS,
    matrixBlockPart_off_block c r S, ?_⟩
  intro i j
  by_cases h : c i = r j
  · simpa only [matrixBlockPart, h, ↓reduceIte] using hSH i j
  · simpa only [matrixBlockPart, h, ↓reduceIte] using
      rationalHeightLE_zero (rationalKernelHeight_pos (Fintype.card ι) hH)

end Erdos3

end

section

open scoped Matrix

namespace Erdos3

theorem real_matrix_image_section {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ) (hS : A * S * A = A) :
    Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) *
      Matrix.of (fun i j => (A i j : ℝ)) = Matrix.of (fun i j => (A i j : ℝ)) := by
  ext i j
  have he := congrArg (fun q : ℚ => (q : ℝ)) (congrFun (congrFun hS i) j)
  simpa only [Matrix.mul_apply, Matrix.of_apply, Rat.cast_sum, Rat.cast_mul] using he

theorem exists_real_span_defining_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H)) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hSr := real_matrix_image_section A S hS
  have hQr : Matrix.of (fun i j => (Q i j : ℝ)) =
      1 - Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hprod
  · ext x
    change Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ↔
      ∃ y, Matrix.of (fun i j => (A i j : ℝ)) *ᵥ y = x
    rw [hQr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨(fun i j => (S i j : ℝ)) *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr, sub_self]

theorem real_column_span_mem_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (x : ι → ℝ) :
    x ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ↔
      x ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  have h := congrArg (fun U : Submodule ℝ (ι → ℝ) => x ∈ U)
    (Matrix.range_mulVecLin (Matrix.of (fun i j => (A i j : ℝ))))
  exact (iff_of_eq h).symm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem imageDefiningHeight_pos (d n H : ℕ) (hH : 1 ≤ H) :
    0 < imageDefiningHeight d n H := by
  have hHp : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hH
  have hK := rationalKernelHeight_pos n hH
  unfold imageDefiningHeight
  positivity

theorem exists_bounded_block_quotient_projection {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → δ) (d : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, c i ≠ d j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ, Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = LinearMap.range A.mulVecLin ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H) := by
  classical
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section c d A hblock hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hId : (A * S) * (A * S) = A * S := by rw [← Matrix.mul_assoc, hS]
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hId, sub_self, sub_zero]
  · ext x
    change (1 - A * S) *ᵥ x = 0 ↔ ∃ y, A *ᵥ y = x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨S *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS, sub_self]
  · intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg c h)
    have hprod : (A * S) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : c i = d k
      · exact (congrArg (fun z : ℚ => A i k * z)
          (hSb k j (fun hkj => hij (hik.trans hkj)))).trans (mul_zero _)
      · exact (congrArg (fun z : ℚ => z * S k j) (hblock i k hik)).trans (zero_mul _)
    simp only [Q, Matrix.sub_apply, Matrix.one_apply, hne, ↓reduceIte, hprod, sub_self]
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hp := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hp

theorem exists_submodule_block_quotient_projection
    {V ι κ δ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (b : Basis ι ℚ V) (c : ι → δ) (U : Submodule ℚ V) (v : κ → V)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ Q : Matrix ι ι ℚ, Q * Q = Q ∧
      LinearMap.ker Q.mulVecLin = U.map b.equivFun.toLinearMap ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ i j, RationalHeightLE (Q i j)
        (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H) := by
  classical
  let v' := blockSpanningFamily b c v
  let A : Matrix ι (ι × κ) ℚ := fun i j => b.repr (v' j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H :=
    fun i j => blockSpanningFamily_height b c v hH hv j i
  have hAb : ∀ i j, c i ≠ c j.1 → A i j = 0 := by
    intro i j hij
    exact (blockSpanningFamily_repr b c v j i).trans (ite_eq_right hij)
  have he := exists_bounded_block_quotient_projection c (fun j : ι × κ => c j.1) A hAb hH hA
  obtain ⟨Q, hQQ, hker, hblock, hQ⟩ := he
  refine ⟨Q, hQQ, hker.trans ?_, hblock, ?_⟩
  · rw [Matrix.range_mulVecLin, ← blockSpanningFamily_span b c U v hspan hU,
      Submodule.map_span, ← Set.range_comp]
    rfl
  · simpa only [Fintype.card_prod] using hQ

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_real_block_span_defining_matrix {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H)) ∧
      (∀ i j, r i ≠ r j → Q i j = 0) ∧
      LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) =
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
  classical
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section r c A hblock hH hA
  let Q : Matrix ι ι ℚ := 1 - A * S
  have hSr := real_matrix_image_section A S hS
  have hQr : Matrix.of (fun i j => (Q i j : ℝ)) =
      1 - Matrix.of (fun i j => (A i j : ℝ)) * Matrix.of (fun i j => (S i j : ℝ)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Q, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, hij]
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix ι ι ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul A S hA hSH i j
    simpa only [Q, Matrix.sub_apply, imageDefiningHeight, mul_one] using hI.sub hprod
  · intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg r h)
    have hprod : (A * S) i j = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : r i = c k
      · exact (congrArg (fun x : ℚ => A i k * x)
          (hSb k j (fun hkj => hij (hik.trans hkj)))).trans (mul_zero _)
      · exact (congrArg (fun x : ℚ => x * S k j) (hblock i k hik)).trans (zero_mul _)
    simp only [Q, Matrix.sub_apply, Matrix.one_apply, hne, ↓reduceIte, hprod, sub_self]
  · ext x
    change Matrix.of (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ↔
      ∃ y, Matrix.of (fun i j => (A i j : ℝ)) *ᵥ y = x
    rw [hQr, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro hx
      exact ⟨(fun i j => (S i j : ℝ)) *ᵥ x, (sub_eq_zero.mp hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hSr, sub_self]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
  (b : Basis ι ℚ V) (U : Submodule ℚ V) (Q : Matrix ι ι ℚ)
  (hker : LinearMap.ker Q.mulVecLin = U.map b.equivFun.toLinearMap)

noncomputable def quotientProjectionEquiv :
    (V ⧸ U) ≃ₗ[ℚ] LinearMap.range Q.mulVecLin :=
  (Submodule.Quotient.equiv U (U.map b.equivFun.toLinearMap) b.equivFun rfl).trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans Q.mulVecLin.quotKerEquivRange)

theorem quotientProjectionEquiv_mk (x : V) :
    (quotientProjectionEquiv b U Q hker (U.mkQ x) : ι → ℚ) = Q *ᵥ b.equivFun x := by
  change (Q.mulVecLin.quotKerEquivRange (Submodule.Quotient.mk (b.equivFun x)) : ι → ℚ) = _
  rfl

theorem quotientProjectionEquiv_symm (hQ : Q * Q = Q) (y : LinearMap.range Q.mulVecLin) :
    (quotientProjectionEquiv b U Q hker).symm y = U.mkQ (b.equivFun.symm y.val) := by
  apply (quotientProjectionEquiv b U Q hker).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [quotientProjectionEquiv_mk, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := y.property
  change Q *ᵥ x = y.val at hx
  rw [← hx, Matrix.mulVec_mulVec, hQ]

end Erdos3

end

end OAI
