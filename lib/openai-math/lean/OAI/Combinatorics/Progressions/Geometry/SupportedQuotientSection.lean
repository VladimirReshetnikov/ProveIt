/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Linear.BaseChangeCoordinateProjection
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
import OAI.Combinatorics.Progressions.Linear.SortedBasisTriangular

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section Algebra

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
  (hP : P = Submodule.span K (b '' S))

noncomputable def supportedQuotientSection : (V ⧸ P) →ₗ[K] V :=
  (supportedQuotientBasis b P S hP).constr K (fun i => b i.val)

@[simp] theorem supportedQuotientSection_basis (i : {i // i ∉ S}) :
    supportedQuotientSection b P S hP (supportedQuotientBasis b P S hP i) = b i.val :=
  Basis.constr_basis _ _ _ i

theorem supportedQuotientSection_rightInverse (x : V ⧸ P) :
    P.mkQ (supportedQuotientSection b P S hP x) = x := by
  have he : P.mkQ.comp (supportedQuotientSection b P S hP) = LinearMap.id := by
    apply (supportedQuotientBasis b P S hP).ext
    intro i
    change P.mkQ (supportedQuotientSection b P S hP
      (supportedQuotientBasis b P S hP i)) = supportedQuotientBasis b P S hP i
    rw [supportedQuotientSection_basis, supportedQuotientBasis_apply]
  exact DFunLike.congr_fun he x

theorem supportedQuotientSection_coordinate (x : V ⧸ P) (i : {i // i ∉ S}) :
    b.repr (supportedQuotientSection b P S hP x) i =
      (supportedQuotientBasis b P S hP).repr x i := by
  rw [← supportedQuotientBasis_repr_mk b P S hP, supportedQuotientSection_rightInverse]

theorem supportedQuotientSection_coordinate_zero (x : V ⧸ P) (i : ι) (hi : i ∈ S) :
    b.repr (supportedQuotientSection b P S hP x) i = 0 := by
  have he : (b.coord i).comp (supportedQuotientSection b P S hP) = 0 := by
    apply (supportedQuotientBasis b P S hP).ext
    intro j
    change b.repr (supportedQuotientSection b P S hP
      (supportedQuotientBasis b P S hP j)) i = 0
    rw [supportedQuotientSection_basis, b.repr_self]
    apply Finsupp.single_eq_of_ne
    exact fun hij => j.property (hij ▸ hi)
  exact DFunLike.congr_fun he x

end Algebra

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (P : Submodule ℚ V) (S : Set ι)
  (hP : P = Submodule.span ℚ (b '' S))

theorem realSupportedQuotientSection_rightInverse (x : ℝ ⊗[ℚ] (V ⧸ P)) :
    P.mkQ.baseChange ℝ ((supportedQuotientSection b P S hP).baseChange ℝ x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      supportedQuotientSection_rightInverse]

theorem realSupportedQuotientSection_coordinate
    (x : ℝ ⊗[ℚ] (V ⧸ P)) (i : {i // i ∉ S}) :
    (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i =
      ((supportedQuotientBasis b P S hP).baseChange ℝ).repr x i := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, supportedQuotientSection_coordinate]

theorem realSupportedQuotientSection_coordinate_zero
    (x : ℝ ⊗[ℚ] (V ⧸ P)) (i : ι) (hi : i ∈ S) :
    (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      supportedQuotientSection_coordinate_zero b P S hP x i hi]
    exact zero_smul ℚ r

theorem realSupportedQuotientSection_norm [Fintype ι] [DecidablePred (· ∈ S)]
    (x : ℝ ⊗[ℚ] (V ⧸ P)) :
    ‖(b.baseChange ℝ).equivFun ((supportedQuotientSection b P S hP).baseChange ℝ x)‖ =
      ‖((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    by_cases hi : i ∈ S
    · rw [Basis.equivFun_apply, realSupportedQuotientSection_coordinate_zero b P S hP x i hi,
        norm_zero]
      exact norm_nonneg _
    · rw [Basis.equivFun_apply,
        realSupportedQuotientSection_coordinate b P S hP x ⟨i, hi⟩]
      exact norm_le_pi_norm (((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x) ⟨i, hi⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [Basis.equivFun_apply, ← realSupportedQuotientSection_coordinate b P S hP x i]
    exact norm_le_pi_norm ((b.baseChange ℝ).equivFun
      ((supportedQuotientSection b P S hP).baseChange ℝ x)) i.val

theorem realSupportedQuotientSection_grid [Fintype ι] [DecidablePred (· ∈ S)]
    (l : ℕ) (x : ℝ ⊗[ℚ] (V ⧸ P))
    (hx : ((supportedQuotientBasis b P S hP).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun ((supportedQuotientSection b P S hP).baseChange ℝ x) ∈
      realDenominatorGrid l := by
  classical
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun i => if hi : i ∈ S then 0 else v ⟨i, hi⟩, ?_⟩
  funext i
  change ((if hi : i ∈ S then 0 else v ⟨i, hi⟩ : ℤ) : ℝ) =
    (l : ℝ) * (b.baseChange ℝ).repr ((supportedQuotientSection b P S hP).baseChange ℝ x) i
  by_cases hi : i ∈ S
  · rw [dite_eq_left hi, realSupportedQuotientSection_coordinate_zero b P S hP x i hi]
    simp only [Int.cast_zero, mul_zero]
  · rw [dite_eq_right hi, realSupportedQuotientSection_coordinate b P S hP x ⟨i, hi⟩]
    exact congrFun hv ⟨i, hi⟩

end Erdos3

end

end OAI
