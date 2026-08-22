import ExponentialIdentities.TwoBaseIntegerExponent.BeattyTropicalFiber
import Mathlib.Data.Fintype.EquivFin

/-!
# Row-block Laplace expansions for rank-one tropical determinants

Grouping columns by a repeated structural weight partitions the Leibniz
permutations according to the set of rows assigned to every column block.
This module factors each such fiber into a signed product of square unit
minors, then sums the fibers to obtain an exact all-layer expansion.  After
removing the minimum rank-one power, the exponent of each summand is its
assignment-cost excess.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix Function

/-- A row-block assignment has the same fiber sizes as the fixed column-block map. -/
def RowBlockAssignment
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) :=
  {a : n → o // ∀ k, Nonempty ({i : n // b i = k} ≃ {r : n // a r = k})}

noncomputable instance rowBlockAssignmentFintype
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) :
    Fintype (RowBlockAssignment b) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The row-block assignment induced by a Leibniz permutation. -/
def permutationRowBlockAssignment
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (sigma : Equiv.Perm n) :
    RowBlockAssignment b :=
  ⟨b ∘ sigma.symm, fun k ↦ ⟨
    { toFun := fun i ↦ ⟨sigma i, by simpa [Function.comp_def] using i.property⟩
      invFun := fun r ↦ ⟨sigma.symm r, by simpa using r.property⟩
      left_inv := fun i ↦ Subtype.ext (sigma.symm_apply_apply i)
      right_inv := fun r ↦ Subtype.ext (sigma.apply_symm_apply r) }⟩⟩

@[simp]
theorem permutationRowBlockAssignment_apply
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (sigma : Equiv.Perm n) (r : n) :
    (permutationRowBlockAssignment b sigma).1 r = b (sigma.symm r) :=
  rfl

/-- A canonical (noncomputably chosen) permutation aligning the fixed column
blocks with a prescribed row-block assignment. -/
noncomputable def rowBlockAlignment
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (a : RowBlockAssignment b) :
    Equiv.Perm n :=
  Equiv.ofFiberEquiv fun k ↦ Classical.choice (a.property k)

theorem rowBlockAlignment_map
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (a : RowBlockAssignment b) (i : n) :
    a.1 (rowBlockAlignment b a i) = b i := by
  exact Equiv.ofFiberEquiv_map (fun k ↦ Classical.choice (a.property k)) i

@[simp]
theorem permutationRowBlockAssignment_alignment
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (a : RowBlockAssignment b) :
    permutationRowBlockAssignment b (rowBlockAlignment b a) = a := by
  apply Subtype.ext
  funext r
  have h := rowBlockAlignment_map b a ((rowBlockAlignment b a).symm r)
  simpa using h.symm

/-- Two permutations induce the same row-block assignment exactly when
their relative permutation preserves every column block. -/
theorem permutationRowBlockAssignment_eq_iff
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o)
    (sigma rho : Equiv.Perm n) :
    permutationRowBlockAssignment b sigma = permutationRowBlockAssignment b rho ↔
      rho.symm * sigma ∈ blockPreservingPermutations b := by
  rw [mem_blockPreservingPermutations]
  constructor
  · intro h i
    have hfun := congrArg Subtype.val h
    have hi := congrFun hfun (sigma i)
    simpa using hi.symm
  · intro h
    apply Subtype.ext
    funext r
    have hi := h (sigma.symm r)
    simpa using hi.symm

/-- A permutation belongs to the assignment fiber represented by `rho`
exactly when it is `rho` followed by a block-preserving permutation. -/
theorem permutationRowBlockAssignment_eq_alignment_iff
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o)
    (a : RowBlockAssignment b) (sigma : Equiv.Perm n) :
    permutationRowBlockAssignment b sigma = a ↔
      (rowBlockAlignment b a).symm * sigma ∈ blockPreservingPermutations b := by
  have hbase := permutationRowBlockAssignment_eq_iff b sigma (rowBlockAlignment b a)
  constructor
  · intro h
    exact hbase.mp (h.trans (permutationRowBlockAssignment_alignment b a).symm)
  · intro h
    exact (hbase.mpr h).trans (permutationRowBlockAssignment_alignment b a)

/-- Structural cost of assigning every row to a repeated-weight column block. -/
def rowBlockAssignmentCost
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o]
    (depth : n → ℕ) (value : o → ℕ) {b : n → o}
    (a : RowBlockAssignment b) : ℕ :=
  ∑ r, depth r * value (a.1 r)

/-- The canonical row assignment, in which each row remains in its own
column block. -/
def canonicalRowBlockAssignment
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) : RowBlockAssignment b :=
  permutationRowBlockAssignment b (Equiv.refl _)

/-- Structural cost above the canonical oppositely sorted assignment. -/
def rowBlockAssignmentExcess
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (depth : Fin N → ℕ) (value : o → ℕ) (b : Fin N → o)
    (a : RowBlockAssignment b) : ℕ :=
  rowBlockAssignmentCost depth value a -
    rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)

/-- The signed product of unit minors belonging to one row partition. -/
noncomputable def rowBlockMinorProduct
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (A : Matrix (Fin N) (Fin N) ℤ)
    (a : RowBlockAssignment b) : ℤ :=
  (Equiv.Perm.sign (rowBlockAlignment b a) : ℤ) *
    ∏ k : o, ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det

@[simp]
theorem canonicalRowBlockAssignment_apply
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (r : n) :
    (canonicalRowBlockAssignment b).1 r = b r := by
  rfl

/-- The permutation cost depends only on its induced row-block assignment. -/
theorem rankOneAssignmentCost_eq_rowBlockAssignmentCost
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (depth : Fin N → ℕ) (value : o → ℕ) (b : Fin N → o)
    (sigma : Equiv.Perm (Fin N)) :
    rankOneAssignmentCost depth (value ∘ b) sigma =
      rowBlockAssignmentCost depth value (permutationRowBlockAssignment b sigma) := by
  classical
  simp only [rankOneAssignmentCost, rowBlockAssignmentCost,
    permutationRowBlockAssignment_apply, Function.comp_apply]
  simpa using Equiv.sum_comp sigma
    (fun r ↦ depth r * value (b (sigma.symm r)))

/-- The finite fiber of permutations inducing a prescribed row-block assignment. -/
noncomputable def permutationRowBlockAssignmentFiber
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o) (a : RowBlockAssignment b) :
    Finset (Equiv.Perm n) := by
  classical
  exact Finset.univ.filter fun sigma ↦ permutationRowBlockAssignment b sigma = a

@[simp]
theorem mem_permutationRowBlockAssignmentFiber_iff
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] {b : n → o} {a : RowBlockAssignment b}
    {sigma : Equiv.Perm n} :
    sigma ∈ permutationRowBlockAssignmentFiber b a ↔
      permutationRowBlockAssignment b sigma = a := by
  classical
  simp [permutationRowBlockAssignmentFiber]

/-- **Laplace fiber factorization.**  Once the rows assigned to every
column block are fixed, the signed Leibniz sum factors into the product of
the corresponding square minors.  The representative contributes one
global sign. -/
theorem sum_permutationRowBlockAssignmentFiber_eq_sign_mul_prod_blockDet
    {n o R : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] [LinearOrder o] [CommRing R]
    (b : n → o) (A : Matrix n n R) (a : RowBlockAssignment b) :
    (∑ sigma ∈ permutationRowBlockAssignmentFiber b a,
      (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i) =
      (Equiv.Perm.sign (rowBlockAlignment b a) : R) *
        ∏ k : o,
          ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det := by
  classical
  let rho := rowBlockAlignment b a
  let S := blockPreservingPermutations b
  let T := permutationRowBlockAssignmentFiber b a
  have hcoset :
      (∑ pi ∈ S, (Equiv.Perm.sign (rho * pi) : R) * ∏ i, A (rho (pi i)) i) =
        ∑ sigma ∈ T, (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i := by
    apply Finset.sum_equiv (Equiv.mulLeft rho)
    · intro pi
      simp only [S, T, mem_permutationRowBlockAssignmentFiber_iff]
      rw [permutationRowBlockAssignment_eq_alignment_iff]
      simp [rho, Equiv.mulLeft]
    · intro pi hpi
      rfl
  rw [← hcoset]
  exact sum_basePerm_mul_blockPreserving_eq_sign_mul_prod_blockDet b A rho

/-- **Ordered row-partition expansion.**  The full determinant is the sum,
over every row assignment with the prescribed block sizes, of the signed
product of the associated square minors. -/
theorem det_eq_sum_rowBlockAssignment_minorProducts
    {n o R : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] [LinearOrder o] [CommRing R]
    (b : n → o) (A : Matrix n n R) :
    A.det =
      ∑ a : RowBlockAssignment b,
        (Equiv.Perm.sign (rowBlockAlignment b a) : R) *
          ∏ k : o,
            ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det := by
  classical
  rw [Matrix.det_apply']
  rw [← Fintype.sum_fiberwise (permutationRowBlockAssignment b)
    (fun sigma : Equiv.Perm n ↦
      (Equiv.Perm.sign sigma : R) * ∏ i, A (sigma i) i)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← sum_permutationRowBlockAssignmentFiber_eq_sign_mul_prod_blockDet b A a]
  symm
  apply Finset.sum_subtype (permutationRowBlockAssignmentFiber b a)
  intro sigma
  exact mem_permutationRowBlockAssignmentFiber_iff

/-- On one row-partition fiber, all structural rank-one powers coincide;
the remaining signed sum is the product of its unit minors. -/
theorem sum_permutationRowBlockAssignmentFiber_rankOnePowerMatrix
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) (depth : Fin N → ℕ) (b : Fin N → o) (value : o → ℕ)
    (A : Matrix (Fin N) (Fin N) ℤ) (a : RowBlockAssignment b) :
    (∑ sigma ∈ permutationRowBlockAssignmentFiber b a,
        (Equiv.Perm.sign sigma : ℤ) *
          ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i) =
      p ^ rowBlockAssignmentCost depth value a *
        ((Equiv.Perm.sign (rowBlockAlignment b a) : ℤ) *
          ∏ k : o,
            ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det) := by
  classical
  have hprod : ∀ sigma ∈ permutationRowBlockAssignmentFiber b a,
      ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i =
        p ^ rowBlockAssignmentCost depth value a * ∏ i, A (sigma i) i := by
    intro sigma hsigma
    have hassignment : permutationRowBlockAssignment b sigma = a :=
      mem_permutationRowBlockAssignmentFiber_iff.mp hsigma
    have hcost : rankOneAssignmentCost depth (value ∘ b) sigma =
        rowBlockAssignmentCost depth value a := by
      rw [rankOneAssignmentCost_eq_rowBlockAssignmentCost]
      exact congrArg (rowBlockAssignmentCost depth value) hassignment
    calc
      ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i =
          p ^ rankOneAssignmentCost depth (value ∘ b) sigma *
            ∏ i, A (sigma i) i := by
        simp only [rankOnePowerMatrix, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum, rankOneAssignmentCost, Function.comp_apply]
      _ = p ^ rowBlockAssignmentCost depth value a *
            ∏ i, A (sigma i) i := by rw [hcost]
  calc
    (∑ sigma ∈ permutationRowBlockAssignmentFiber b a,
        (Equiv.Perm.sign sigma : ℤ) *
          ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i) =
      ∑ sigma ∈ permutationRowBlockAssignmentFiber b a,
        p ^ rowBlockAssignmentCost depth value a *
          ((Equiv.Perm.sign sigma : ℤ) * ∏ i, A (sigma i) i) := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      rw [hprod sigma hsigma]
      ring
    _ = p ^ rowBlockAssignmentCost depth value a *
        (∑ sigma ∈ permutationRowBlockAssignmentFiber b a,
          (Equiv.Perm.sign sigma : ℤ) * ∏ i, A (sigma i) i) := by
      rw [Finset.mul_sum]
    _ = p ^ rowBlockAssignmentCost depth value a *
        ((Equiv.Perm.sign (rowBlockAlignment b a) : ℤ) *
          ∏ k : o,
            ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det) := by
      congr 1
      exact sum_permutationRowBlockAssignmentFiber_eq_sign_mul_prod_blockDet b A a

/-- **All-layer row-partition expansion for a rank-one valuation matrix.**
Every row-block assignment contributes its exact structural power times a
product of generalized-Vandermonde-type unit minors.  Thus higher tropical
layers are indexed by row partitions, rather than individual permutations. -/
theorem det_rankOnePowerMatrix_eq_sum_rowBlockAssignment_minorProducts
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) (depth : Fin N → ℕ) (b : Fin N → o) (value : o → ℕ)
    (A : Matrix (Fin N) (Fin N) ℤ) :
    (rankOnePowerMatrix p depth b value A).det =
      ∑ a : RowBlockAssignment b,
        p ^ rowBlockAssignmentCost depth value a *
          ((Equiv.Perm.sign (rowBlockAlignment b a) : ℤ) *
            ∏ k : o,
              ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det) := by
  classical
  rw [Matrix.det_apply']
  let term : Equiv.Perm (Fin N) → ℤ := fun sigma ↦
    (Equiv.Perm.sign sigma : ℤ) *
      ∏ i, rankOnePowerMatrix p depth b value A (sigma i) i
  calc
    (∑ sigma : Equiv.Perm (Fin N), term sigma) =
        ∑ a : RowBlockAssignment b,
          ∑ sigma : {sigma // permutationRowBlockAssignment b sigma = a},
            term sigma :=
      (Fintype.sum_fiberwise (permutationRowBlockAssignment b) term).symm
    _ = ∑ a : RowBlockAssignment b,
          ∑ sigma ∈ permutationRowBlockAssignmentFiber b a, term sigma := by
      apply Finset.sum_congr rfl
      intro a _
      symm
      apply Finset.sum_subtype (permutationRowBlockAssignmentFiber b a)
      intro sigma
      exact mem_permutationRowBlockAssignmentFiber_iff
    _ = ∑ a : RowBlockAssignment b,
        p ^ rowBlockAssignmentCost depth value a *
          ((Equiv.Perm.sign (rowBlockAlignment b a) : ℤ) *
            ∏ k : o,
              ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det) := by
      apply Finset.sum_congr rfl
      intro a _
      exact sum_permutationRowBlockAssignmentFiber_rankOnePowerMatrix
        p depth b value A a

/-- **Normalized all-layer expansion.**  Under opposite sorting, the
canonical row partition has minimum structural cost.  Factoring that power
from the determinant leaves a finite sum whose exponent on each partition
is exactly its assignment-cost excess. -/
theorem det_rankOnePowerMatrix_eq_minPow_mul_sum_assignmentExcess
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value) :
    (rankOnePowerMatrix p depth b value A).det =
      p ^ rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) *
        ∑ a : RowBlockAssignment b,
          p ^ (rowBlockAssignmentCost depth value a -
              rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)) *
            ((Equiv.Perm.sign (rowBlockAlignment b a) : ℤ) *
              ∏ k : o,
                ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det) := by
  classical
  rw [det_rankOnePowerMatrix_eq_sum_rowBlockAssignment_minorProducts]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  let tau := rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)
  let cost := rowBlockAssignmentCost depth value a
  have hle : tau ≤ cost := by
    calc
      tau ≤ rankOneAssignmentCost depth (value ∘ b) (rowBlockAlignment b a) :=
        rankOneAssignmentCost_refl_le hdepth (hvalue.comp hb) (rowBlockAlignment b a)
      _ = rowBlockAssignmentCost depth value
          (permutationRowBlockAssignment b (rowBlockAlignment b a)) :=
        rankOneAssignmentCost_eq_rowBlockAssignmentCost depth value b _
      _ = cost := by
        rw [permutationRowBlockAssignment_alignment]
  have hsplit : cost = tau + (cost - tau) := (Nat.add_sub_of_le hle).symm
  change p ^ cost * _ = p ^ tau * (p ^ (cost - tau) * _)
  rw [hsplit, pow_add]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- **Exact finite-depth cascade truncation.**  Modulo `p ^ K` after the
minimum structural power is removed, only row partitions of assignment
excess `< K` survive.  The displayed second sum is the exact higher-layer
remainder, rather than an existential error term.

This controls which row partitions can contribute at a fixed depth, but it
does not bound cancellation among the surviving minor products. -/
theorem det_rankOnePowerMatrix_eq_minPow_mul_truncatedAssignmentSum
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value)
    (K : ℕ) :
    (rankOnePowerMatrix p depth b value A).det =
      p ^ rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) *
        ((∑ a ∈ (Finset.univ.filter fun a : RowBlockAssignment b ↦
              rowBlockAssignmentExcess depth value b a < K),
            p ^ rowBlockAssignmentExcess depth value b a *
              rowBlockMinorProduct b A a) +
          p ^ K *
            ∑ a ∈ (Finset.univ.filter fun a : RowBlockAssignment b ↦
                K ≤ rowBlockAssignmentExcess depth value b a),
              p ^ (rowBlockAssignmentExcess depth value b a - K) *
                rowBlockMinorProduct b A a) := by
  classical
  rw [det_rankOnePowerMatrix_eq_minPow_mul_sum_assignmentExcess
    p A hdepth hb hvalue]
  congr 1
  let e : RowBlockAssignment b → ℕ := rowBlockAssignmentExcess depth value b
  let m : RowBlockAssignment b → ℤ := rowBlockMinorProduct b A
  let low := Finset.univ.filter fun a : RowBlockAssignment b ↦ e a < K
  let high := Finset.univ.filter fun a : RowBlockAssignment b ↦ K ≤ e a
  have hnotLow : Finset.univ.filter (fun a : RowBlockAssignment b ↦ ¬ e a < K) = high := by
    ext a
    simp only [high, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (RowBlockAssignment b)) (fun a ↦ e a < K)
    (fun a ↦ p ^ e a * m a)
  change (∑ a : RowBlockAssignment b, p ^ e a * m a) =
    (∑ a ∈ low, p ^ e a * m a) +
      p ^ K * ∑ a ∈ high, p ^ (e a - K) * m a
  change (∑ a ∈ low, p ^ e a * m a) +
      (∑ a ∈ (Finset.univ.filter fun a ↦ ¬ e a < K), p ^ e a * m a) =
        ∑ a : RowBlockAssignment b, p ^ e a * m a at hpartition
  rw [hnotLow] at hpartition
  rw [← hpartition]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hKa : K ≤ e a := (Finset.mem_filter.mp ha).2
  have hsplit : e a = K + (e a - K) := (Nat.add_sub_of_le hKa).symm
  rw [hsplit, pow_add]
  simp only [Nat.add_sub_cancel_left]
  ring

/-- A noncanonical row partition is represented by a permutation outside
the block-preserving minimum fiber. -/
theorem rowBlockAlignment_not_blockPreserving_of_ne_canonical
    {n o : Type*} [Fintype n] [DecidableEq n]
    [Fintype o] [DecidableEq o] (b : n → o)
    {a : RowBlockAssignment b} (ha : a ≠ canonicalRowBlockAssignment b) :
    rowBlockAlignment b a ∉ blockPreservingPermutations b := by
  intro hpreserve
  have heq := (permutationRowBlockAssignment_eq_iff b
    (rowBlockAlignment b a) (Equiv.refl _)).mpr (by simpa using hpreserve)
  apply ha
  rw [← permutationRowBlockAssignment_alignment b a]
  exact heq

/-- In the concrete Beatty depths, every noncanonical row partition lies at
least `floor beta` above the minimum structural layer. -/
theorem beattyRowBlockAssignment_excess_ge_floor
    {N T : ℕ} {beta : ℝ}
    {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} {value : o → ℕ}
    (hbeta : 0 ≤ beta)
    (hT : ∀ k : Fin N, ⌊(k : ℝ) * beta⌋₊ ≤ T)
    (hb : Monotone b) (hvalue : StrictMono value)
    {a : RowBlockAssignment b} (ha : a ≠ canonicalRowBlockAssignment b) :
    ⌊beta⌋₊ ≤
      rowBlockAssignmentCost (beattyRowDepth T beta) value a -
        rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b) (Equiv.refl _) := by
  have hgap := beattyAssignmentCost_add_floor_le_of_not_blockPreserving
    hbeta hT hb hvalue
      (rowBlockAlignment_not_blockPreserving_of_ne_canonical b ha)
  have hcost : rankOneAssignmentCost (beattyRowDepth T beta) (value ∘ b)
      (rowBlockAlignment b a) =
        rowBlockAssignmentCost (beattyRowDepth T beta) value a := by
    rw [rankOneAssignmentCost_eq_rowBlockAssignmentCost,
      permutationRowBlockAssignment_alignment]
  rw [hcost] at hgap
  omega

end LeanProofs.TwoBaseIntegerExponent
