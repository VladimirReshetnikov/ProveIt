/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.Combinatorics.Progressions.Estimates.FiniteAssignmentPartition
import OAI.Combinatorics.Progressions.Geometry.MissingCoordinateProducts
import OAI.Combinatorics.Progressions.Sampling.MixedAssignmentSampling

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_product_unit_vector {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    (f : A → I → ℂ) (hf : ∀ a, ∑ i, ‖f a i‖ ^ 2 = 1) :
    ∑ v : A → I, ‖∏ a, f a (v a)‖ ^ 2 = 1 := by
  simp only [norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (a : A) (i : I) => ‖f a i‖ ^ 2)]
  simp only [hf, Finset.prod_const_one]

theorem function_card_le_exp {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] {p : ℝ}
    (hI : (Fintype.card I : ℝ) ≤ Real.exp p) :
    (Fintype.card (A → I) : ℝ) ≤ Real.exp ((Fintype.card A : ℝ) * p) := by
  simp only [Fintype.card_fun, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hI _).trans_eq (Real.exp_nat_mul _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedPermutationFamily {s : ℕ} (e : Equiv.Perm (Fin s)) :
    ReplicatedPermutation (mixedCorrelationDegree s) :=
  Fin.cases (motive := fun b : Fin 2 => Equiv.Perm (Fin (mixedCorrelationDegree s b)))
    (Equiv.refl _) (fun _ => e)

theorem mixedPermutation_head {s : ℕ} (e : Equiv.Perm (Fin s)) :
    replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e) (mixedHead s) =
      mixedHead s := rfl

theorem mixedPermutation_replica {s : ℕ} (e : Equiv.Perm (Fin s)) (j : Fin s) :
    replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e) (mixedReplica j) =
      mixedReplica (e j) := rfl

theorem mixedPermutation_symm_head {s : ℕ} (e : Equiv.Perm (Fin s)) :
    (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm (mixedHead s) =
      mixedHead s := by
  have H := (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm_apply_apply
    (mixedHead s)
  simpa only [mixedPermutation_head] using H

theorem mixedPermutation_symm_replica {s : ℕ} (e : Equiv.Perm (Fin s)) (j : Fin s) :
    (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm (mixedReplica j) =
      mixedReplica (e.symm j) := by
  have H := (replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm_apply_apply
    (mixedReplica (e.symm j))
  simpa only [mixedPermutation_replica, Equiv.apply_symm_apply] using H

theorem mixedReplicatedInput_permuted {s : ℕ} {α : Type*} (e : Equiv.Perm (Fin s))
    (h : α) (v : Fin s → α) :
    (fun j => mixedReplicatedInput h v
      ((replicatedPermutation (mixedCorrelationDegree s) (mixedPermutationFamily e)).symm j)) =
      mixedReplicatedInput h (fun i => v (e.symm i)) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedPermutation_symm_head, mixedReplicatedInput_head, mixedReplicatedInput_head]
  · rw [mixedPermutation_symm_replica, mixedReplicatedInput_replica, mixedReplicatedInput_replica]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)

theorem mixed_permutation_eval
    (hsym : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
      W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x)
    (e : Equiv.Perm (Fin s)) (k : Fin W.outputDim) (h : ℤ) (v : Fin s → ℤ) :
    W.eval k (mixedReplicatedInput h (fun j => v (e j))) = W.eval k (mixedReplicatedInput h v) := by
  have H := hsym (mixedPermutationFamily e.symm) k (mixedReplicatedInput h v)
  simpa only [mixedReplicatedInput_permuted, Equiv.symm_symm] using H

theorem mixed_assignment_product_grouped
    (hsym : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
      W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x)
    (h : ℤ) (x : Fin s → ℤ) (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → Fin W.outputDim) :
    (∏ v : Fin s → Fin s, W.eval (a ((assignmentSplitEquiv s).symm v))
      (mixedReplicatedInput h (fun j => x (v j)))) =
      (∏ e : Equiv.Perm (Fin s), W.eval (a (Sum.inl e)) (mixedReplicatedInput h x)) *
        ∏ v : MissingAssignment s, W.eval (a (Sum.inr v))
          (mixedReplicatedInput h (fun j => x (v.val j))) := by
  classical
  rw [assignment_product_split (fun v k => W.eval k (mixedReplicatedInput h (fun j => x (v j)))) a]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact W.mixed_permutation_eval hsym e _ h x

theorem mixed_missing_assignment_independent (v : MissingAssignment s) :
    ∃ j : Fin s, ∀ (k : Fin W.outputDim) (x y : Fin (s + 1) → ℤ),
      (∀ a, a ≠ j.succ → x a = y a) →
      W.eval k (mixedReplicatedInput (x 0) (fun i => x (v.val i).succ)) =
        W.eval k (mixedReplicatedInput (y 0) (fun i => y (v.val i).succ)) := by
  obtain ⟨j, hj⟩ := missingAssignment_coordinate v
  refine ⟨j, ?_⟩
  intro k x y hxy
  congr 1
  funext a
  rcases mixedReplicated_cases a with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head, mixedReplicatedInput_head]
    apply hxy
    exact (Fin.succ_ne_zero j).symm
  · rw [mixedReplicatedInput_replica, mixedReplicatedInput_replica]
    apply hxy
    exact fun heq => hj i (Fin.succ_injective s heq)

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_finite_assignment_expansion (s n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin (n + 2) → ℤ) => W.eval k
          (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ a : Fin (n + 1), x a.succ)))
        (fun a : (Fin s → Fin (n + 1)) → Fin W.outputDim => fun x =>
          ∏ v : Fin s → Fin (n + 1), W.eval (a v)
            (mixedReplicatedInput (x 0) (fun j => x (v j).succ))) := by
  let : Nonempty (MixedReplicatedIndex s) := replicatedMixed_nonempty s
  obtain ⟨A, _, hexpand⟩ := exists_finite_assignment_equivalence n (mixedRepeatedCoordinates s)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C ((n + 1) ^ s) * X + X)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hsum : (p + A) ^ A + ((n + 1) ^ s : ℕ) * p + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hnp : 0 ≤ ((n + 1) ^ s : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hAC : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hnC : ((n + 1) ^ s : ℕ) * p ≤ (p + C) ^ C := by linarith
  let M (j : Fin (n + 1) × MixedReplicatedIndex s) : ((Fin (n + 2) → ℤ) →+ ℤ) :=
    { toFun := fun x => mixedChoiceSample (x 0) (fun a => x a.succ) j
      map_zero' := by rcases j with ⟨a, b, k⟩; fin_cases b <;> rfl
      map_add' := by intro x y; rcases j with ⟨a, b, k⟩; fin_cases b <;> rfl }
  have hM (x : Fin (n + 2) → ℤ) :
      (fun j => M j x) = mixedChoiceSample (x 0) (fun a => x a.succ) := rfl
  have E := (hexpand W (mixedRepeatedCoordinates_nodup s)).linearPullbackHom M
  have H : NativeIntegerVectorEquivalence s ((p + A) ^ A)
      (fun k (x : Fin (n + 2) → ℤ) => W.eval k
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ a : Fin (n + 1), x a.succ)))
      (fun a : (Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) → Fin W.outputDim =>
        fun x => ∏ v, W.eval (a v)
          (mixedReplicatedInput (x 0) (fun j => x (mixedChoiceAssignmentEquiv s n v j).succ))) := by
    simpa only [hM, finiteChoiceExpansion, mixedChoiceSample_sum, mixedChoiceSample_leaf,
      replicatedMixed_card, Nat.add_sub_cancel] using E
  have hdim : (Fintype.card ((Fin s → Fin (n + 1)) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ ((n + 1) ^ s) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
      _ = Real.exp (((n + 1) ^ s : ℕ) * p) := (Real.exp_nat_mul p ((n + 1) ^ s)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnC
  apply H.of_coordinate_maps _ _ id (fun a v => a (mixedChoiceAssignmentEquiv s n v))
    (fun _ _ => rfl) _ _ hdim hAC
  · intro a x
    exact ((mixedChoiceAssignmentEquiv s n).prod_comp (fun v : Fin s → Fin (n + 1) =>
      W.eval (a v) (mixedReplicatedInput (x 0) (fun j => x (v j).succ)))).symm
  · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationProduct {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : Equiv.Perm (Fin s) → I) (x : Fin (s + 1) → ℤ) : ℂ :=
  ∏ e, f (a e) (mixedReplicatedInput (x 0) (fun j => x j.succ))

noncomputable def mixedMissingProduct {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : MissingAssignment s → I) (x : Fin (s + 1) → ℤ) : ℂ := by
  classical
  exact ∏ v, f (a v) (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))

noncomputable def mixedAssignmentPartitionVector {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) (x : Fin (s + 1) → ℤ) : ℂ :=
  mixedPermutationProduct f (fun e => a (Sum.inl e)) x *
    mixedMissingProduct f (fun v => a (Sum.inr v)) x

theorem mixedAssignmentPartitionVector_unit {s : ℕ} {I : Type*} [Fintype I]
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ) (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1)
    (x : Fin (s + 1) → ℤ) :
    ∑ a, ‖mixedAssignmentPartitionVector f a x‖ ^ 2 = 1 := by
  classical
  let F (r : Equiv.Perm (Fin s) ⊕ MissingAssignment s) (i : I) :=
    match r with
    | Sum.inl _ => f i (mixedReplicatedInput (x 0) (fun j => x j.succ))
    | Sum.inr v => f i (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))
  have hF : ∀ r, ∑ i, ‖F r i‖ ^ 2 = 1 := by
    intro r
    cases r <;> exact hf _
  simpa only [mixedAssignmentPartitionVector, mixedPermutationProduct, mixedMissingProduct,
    Fintype.prod_sum_type, F] using finite_product_unit_vector F hF

theorem mixedPermutationProduct_norm {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (a : Equiv.Perm (Fin s) → I) (x : Fin (s + 1) → ℤ) :
    ‖mixedPermutationProduct f a x‖ ≤ 1 := by
  rw [mixedPermutationProduct, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hf _ _)

theorem mixedAssignmentPartitionVector_norm {s : ℕ} {I : Type*}
    (f : I → (MixedReplicatedIndex s → ℤ) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → I) (x : Fin (s + 1) → ℤ) :
    ‖mixedAssignmentPartitionVector f a x‖ ≤ 1 := by
  classical
  rw [mixedAssignmentPartitionVector, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (mixedPermutationProduct_norm f hf _ _)).trans ?_
  rw [mixedMissingProduct, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hf _ _)

theorem NativeMultidegreeNilcharacter.exists_mixed_missing_factors {s : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)
    (a : MissingAssignment s → Fin W.outputDim) :
    ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
      (∀ k x, ‖A k x‖ ≤ 1) ∧
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) ∧
      ∀ x, (∏ k, A k x) = mixedMissingProduct W.eval a x := by
  classical
  apply exists_missing_coordinate_product_factors
    (fun v x => W.eval (a v) (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ)))
    (fun _ _ => W.norm_eval _ _)
  intro v
  obtain ⟨j, hj⟩ := W.mixed_missing_assignment_independent v
  exact ⟨j.succ, hj (a v)⟩

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_permutation_partition_expansion (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin (s + 1) → ℤ) => W.eval k
          (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ j : Fin s, x j.succ)))
        (fun a : Equiv.Perm (Fin s) ⊕ MissingAssignment s → Fin W.outputDim => fun x =>
          (∏ e : Equiv.Perm (Fin s), W.eval (a (Sum.inl e))
            (mixedReplicatedInput (x 0) (fun j => x j.succ))) *
          ∏ v : MissingAssignment s, W.eval (a (Sum.inr v))
            (mixedReplicatedInput (x 0) (fun j => x (v.val j).succ))) := by
  cases s with
  | zero => omega
  | succ n =>
      obtain ⟨C, hC, hexpand⟩ := exists_mixed_finite_assignment_expansion (n + 1) n
      refine ⟨C, hC, ?_⟩
      intro p W hsym
      classical
      have E := hexpand W
      apply E.of_coordinate_maps _ _ id
        (fun a v => a ((assignmentSplitEquiv (n + 1)).symm v))
        (fun _ _ => rfl) _ E.left_dimension _ le_rfl
      · intro a x
        exact (W.mixed_assignment_product_grouped hsym (x 0) (fun j => x j.succ) a).symm
      · have hcard : Fintype.card (Equiv.Perm (Fin (n + 1)) ⊕ MissingAssignment (n + 1)) =
            Fintype.card (Fin (n + 1) → Fin (n + 1)) :=
          Fintype.card_congr (assignmentSplitEquiv (n + 1))
        simpa only [Fintype.card_fun, hcard] using E.right_dimension

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedPermutationIndex (s : ℕ) : Equiv.Perm (Fin s) ≃ Fin s.factorial :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_perm, Fintype.card_fin])

noncomputable def mixedPermutationTensorIndex {s : ℕ} (d : ℕ)
    (a : Equiv.Perm (Fin s) → Fin d) : Fin (d ^ s.factorial) :=
  tensorIndexEquiv d s.factorial (fun j => a ((mixedPermutationIndex s).symm j))

theorem NativeMultidegreeNilcharacter.mixedPermutationProduct_tensorPower {s : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p)
    (a : Equiv.Perm (Fin s) → Fin W.outputDim) (x : Fin (s + 1) → ℤ) :
    mixedPermutationProduct W.eval a x =
      (W.tensorPower s.factorial).eval (mixedPermutationTensorIndex W.outputDim a)
        (mixedReplicatedInput (x 0) (fun j => x j.succ)) := by
  simp only [tensorPower_eval, mixedPermutationTensorIndex, Equiv.symm_apply_apply]
  exact ((mixedPermutationIndex s).symm.prod_comp
    (fun e => W.eval (a e) (mixedReplicatedInput (x 0) (fun j => x j.succ)))).symm

end Erdos3

end

end OAI
