import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3
open scoped BigOperators
variable {D α : Type*} {B : D → Type*} {h : D → ℕ}
variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

theorem principalCoordinateWeights_partition_weight (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (p : ∀ j, FiniteProbabilityWeights (IntegerScalarCubeBox α (L j))) (y : PrincipalIntegerTuples B h α L) :
    (FiniteProbabilityWeights.pi p).weight y =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).weight (principalAxisRestrict P y) *
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).weight
          (principalAxisRestrict (fun d => ¬P d) y) := by
  simp only [FiniteProbabilityWeights.pi, principalAxisRestrict, Fintype.prod_sigma]
  exact (Fintype.prod_subtype_mul_prod_subtype P
    (fun d => ∏ j : B d × Fin (h d),
      (p ⟨d,j⟩).weight (y ⟨d, j⟩))).symm

theorem principalCoordinateWeights_partition (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (p : ∀ j, FiniteProbabilityWeights (IntegerScalarCubeBox α (L j))) (f : PrincipalIntegerTuples B h α L → ℂ) :
    (FiniteProbabilityWeights.pi p).complexMean f =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).complexMean (fun u =>
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let pL := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun d : {d // P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)
  let pR := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)
  calc
    _ = ∑ z : PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L,
        ((pL.weight z.1 * pR.weight z.2 : ℝ) : ℂ) * f (principalAxisJoin P z.1 z.2) := by
      apply Fintype.sum_equiv (principalAxisPartitionEquiv P L)
      intro y
      simp only [principalAxisPartitionEquiv, Equiv.coe_fn_mk, principalAxisJoin_restrict]
      rw [principalCoordinateWeights_partition_weight P L p y]
    _ = _ := by
      simp only [FiniteProbabilityWeights.complexMean, Fintype.sum_prod_type,
        Complex.ofReal_mul, Finset.mul_sum, mul_assoc, pL, pR]
      rfl

end Erdos3

end

end OAI
