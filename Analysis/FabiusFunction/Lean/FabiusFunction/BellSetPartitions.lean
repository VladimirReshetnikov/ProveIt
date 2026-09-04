import FabiusFunction.PartialBellPolynomials
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Order.Partition.Finpartition

/-!
# The partial Bell polynomials count weighted set partitions

`Fabius.partialBell` is defined in `FabiusFunction.PartialBellPolynomials` purely
by the block recurrence

`B_{n+1,k+1} = ∑_{i ≤ n} C(n,i) x_{i+1} B_{n-i,k}`,  `B_{0,0} = 1`.

Nothing there — and, before this module, nothing anywhere in the corpus —
connects that recurrence to actual set partitions.  This module closes that gap:
it defines the total weight of the partitions of a `Finset` into a prescribed
number of blocks and proves it equals `partialBell`.

## Main results

* `IsSetPartition s P`, `setPartitions s k`, `partitionWeight x s k`: a block set
  `P` partitions `s`; the finset of partitions of `s` into exactly `k` blocks;
  the total weight of those partitions, a block of size `i` weighing `x i`.
* `partitionWeight_insert`: **the combinatorial heart.**  Splitting on the block
  that contains a distinguished new element `a ∉ s` gives
  `W(insert a s, k+1) = ∑_{t ⊆ s} x_{|t|+1} · W(s \ t, k)`,
  the block being `insert a t`.
* `partitionWeight_eq_partialBell`: the weight sum satisfies the same recurrence
  and the same initial data as `partialBell`, hence equals it.  This is
  `thm:bell-poly-partitions` of the manuscript
  `Combinatorial_Coefficient_Calculus`, first half.
* `partialBell_eq_sum_setPartitions`, `partialBell_eq_sum_setPartitions_range`:
  the theorem read as a statement about `partialBell`.
* `bell_complete_eq_sum_allSetPartitions`: the complete Bell polynomial
  `Bell.complete` is the total weight of *all* partitions, the second half of
  `thm:bell-poly-partitions`.
* `card_setPartitions`: **`#(setPartitions s k) = Nat.stirlingSecond #s k`.**
  Mathlib defines `Nat.stirlingSecond` by its recurrence and asserts the
  counting interpretation only in a docstring; `Nat.bell` carries an explicit
  `TODO` saying the counting property is unproved.  This corollary supplies it
  for the second-kind numbers.
* `isSetPartition_iff_exists_finpartition`: interoperability with Mathlib's
  `Finpartition`.

## What is *not* covered

`cor:partition-type`, the count `n! / ∏_i (i!)^{j_i} j_i!` of partitions with
exactly `j_i` blocks of size `i`, is **not** formalized here, and neither is the
multinomial formula `eq:partial-bell-definition` that the manuscript proves it
from.  Both are statements about the *individual monomials* of `B_{n,k}` rather
than about its value, so deriving them from the theorem below requires reading
off the coefficient of `∏ x_i^{j_i}` in `MvPolynomial ℕ ℚ` — a coefficient
extraction layer that the corpus does not have.  The present module proves the
value statement; nothing here implies the type-by-type count.

## The insight the formalization exposed

The obvious plan — induct on the multinomial sum — is the wrong one, and so, it
turns out, is the plan of transporting partitions along a bijection of the
underlying set.  The definition of `partitionWeight` takes an arbitrary
`Finset α`, while `partialBell` takes a natural number, so one expects to need a
transport lemma saying the weight depends on `s` only through `#s`.  It is not
needed.  Strong induction on `#s` supplies it for free: in the recurrence the
residual sets are the `s \ t`, whose cardinalities are strictly smaller, so the
induction hypothesis already delivers `partialBell x #(s \ t) k` and the
cardinality dependence is all that survives.  Removing the transport lemma
removes the single hardest piece of the development, and it is what makes the
"choose the block containing the last element" argument a five-goal
`Finset.sum_nbij'` rather than a study of `Finset.image` under injectivity.

Two further points of technique.  The block containing a given element is
obtained without any choice principle as `blockOf P a = (P.filter (a ∈ ·)).sup id`
— the filter is a singleton, so its supremum *is* the block.  And Mathlib's
`Finpartition` is deliberately not used as the index type: it has no
`insert`-decomposition, no induction principle, and its `Fintype` instance
carries an in-source warning that it takes double-exponential time.  A
`Finset.filter` of `s.powerset.powerset` is a `Finset` outright, and the
bijection can be written on it directly.  `isSetPartition_iff_exists_finpartition`
records that the two notions agree.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section Definitions

variable {α : Type*} [DecidableEq α]

/-- `IsSetPartition s P` says that the finset of blocks `P` is a partition of the
finset `s`: every block is nonempty, distinct blocks are disjoint, and the blocks
cover `s`.  Disjointness is phrased as `B ∩ C = ∅` rather than as `Disjoint B C`
so that the predicate is decidable, which is what lets `setPartitions` be an
honest `Finset.filter`. -/
def IsSetPartition (s : Finset α) (P : Finset (Finset α)) : Prop :=
  (∀ B ∈ P, B ≠ ∅) ∧ (∀ B ∈ P, ∀ C ∈ P, B ≠ C → B ∩ C = ∅) ∧ P.sup id = s

/-- `IsSetPartition` is decidable, so partitions can be selected by `Finset.filter`. -/
instance instDecidableIsSetPartition (s : Finset α) (P : Finset (Finset α)) :
    Decidable (IsSetPartition s P) := by
  unfold IsSetPartition
  infer_instance

/-- Blocks of a partition are nonempty. -/
theorem IsSetPartition.ne_empty {s : Finset α} {P : Finset (Finset α)} {B : Finset α}
    (hP : IsSetPartition s P) (hB : B ∈ P) : B ≠ ∅ := hP.1 B hB

/-- The blocks of a partition cover the underlying finset. -/
theorem IsSetPartition.sup_eq {s : Finset α} {P : Finset (Finset α)}
    (hP : IsSetPartition s P) : P.sup id = s := hP.2.2

/-- Every block of a partition of `s` is a subset of `s`. -/
theorem IsSetPartition.subset {s : Finset α} {P : Finset (Finset α)} {B : Finset α}
    (hP : IsSetPartition s P) (hB : B ∈ P) : B ⊆ s := by
  have h : id B ≤ P.sup id := Finset.le_sup (f := id) hB
  rw [hP.2.2] at h
  exact h

/-- The blocks of a partition are pairwise disjoint, in Mathlib's
`Set.PairwiseDisjoint` phrasing. -/
theorem IsSetPartition.pairwiseDisjoint {s : Finset α} {P : Finset (Finset α)}
    (hP : IsSetPartition s P) : (P : Set (Finset α)).PairwiseDisjoint id := by
  intro B hB C hC hBC
  simp only [Function.onFun, id_eq]
  exact Finset.disjoint_iff_inter_eq_empty.mpr
    (hP.2.1 B (Finset.mem_coe.mp hB) C (Finset.mem_coe.mp hC) hBC)

/-- Each element of `s` lies in exactly one block. -/
theorem IsSetPartition.existsUnique_block {s : Finset α} {P : Finset (Finset α)} {a : α}
    (hP : IsSetPartition s P) (ha : a ∈ s) : ∃! B, B ∈ P ∧ a ∈ B := by
  rw [← hP.2.2, Finset.mem_sup] at ha
  obtain ⟨B, hB, haB⟩ := ha
  refine ⟨B, ⟨hB, haB⟩, ?_⟩
  rintro C ⟨hC, haC⟩
  by_contra hne
  have hCB : C ∩ B = ∅ := hP.2.1 C hC B hB hne
  have hmem : a ∈ C ∩ B := Finset.mem_inter.mpr ⟨haC, haB⟩
  rw [hCB] at hmem
  simp at hmem

/-- The block of `P` containing `a`.  No choice principle is involved: the blocks
containing `a` form a singleton, so the supremum of that filter *is* the block. -/
def blockOf (P : Finset (Finset α)) (a : α) : Finset α :=
  (P.filter fun B => a ∈ B).sup id

/-- `blockOf` picks out the block it is supposed to. -/
theorem blockOf_eq {s : Finset α} {P : Finset (Finset α)} {B : Finset α} {a : α}
    (hP : IsSetPartition s P) (hB : B ∈ P) (haB : a ∈ B) : blockOf P a = B := by
  have hfil : (P.filter fun C => a ∈ C) = {B} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Finset.mem_filter.mpr ⟨hB, haB⟩, ?_⟩
    intro C hC
    rw [Finset.mem_filter] at hC
    by_contra hne
    have hCB : C ∩ B = ∅ := hP.2.1 C hC.1 B hB hne
    have hmem : a ∈ C ∩ B := Finset.mem_inter.mpr ⟨hC.2, haB⟩
    rw [hCB] at hmem
    simp at hmem
  unfold blockOf
  rw [hfil, Finset.sup_singleton]
  rfl

/-- For `a` in the underlying set, `blockOf P a` is a block of `P` and contains `a`. -/
theorem blockOf_mem {s : Finset α} {P : Finset (Finset α)} {a : α}
    (hP : IsSetPartition s P) (ha : a ∈ s) : blockOf P a ∈ P ∧ a ∈ blockOf P a := by
  obtain ⟨B, ⟨hB, haB⟩, -⟩ := hP.existsUnique_block ha
  rw [blockOf_eq hP hB haB]
  exact ⟨hB, haB⟩

/-- Deleting one block from a partition leaves a cover of the complement of that
block. -/
theorem IsSetPartition.sup_erase {s : Finset α} {P : Finset (Finset α)} {A : Finset α}
    (hP : IsSetPartition s P) (hA : A ∈ P) : (P.erase A).sup id = s \ A := by
  ext y
  simp only [Finset.mem_sup, Finset.mem_erase, Finset.mem_sdiff, id_eq]
  constructor
  · rintro ⟨B, ⟨hBA, hB⟩, hyB⟩
    refine ⟨hP.subset hB hyB, ?_⟩
    intro hyA
    have hBA' : B ∩ A = ∅ := hP.2.1 B hB A hA hBA
    have hmem : y ∈ B ∩ A := Finset.mem_inter.mpr ⟨hyB, hyA⟩
    rw [hBA'] at hmem
    simp at hmem
  · rintro ⟨hys, hyA⟩
    rw [← hP.2.2, Finset.mem_sup] at hys
    obtain ⟨B, hB, hyB⟩ := hys
    refine ⟨B, ⟨?_, hB⟩, hyB⟩
    rintro rfl
    exact hyA hyB

/-- Mathlib's `Finpartition s` and `IsSetPartition s` describe the same objects.
`Finpartition` is not used as the index type below because it offers no
`insert`-decomposition, no induction principle, and a `Fintype` instance whose
own source comment warns that it takes double-exponential time. -/
theorem isSetPartition_iff_exists_finpartition (s : Finset α) (P : Finset (Finset α)) :
    IsSetPartition s P ↔ ∃ F : Finpartition s, F.parts = P := by
  constructor
  · intro hP
    refine ⟨⟨P, ?_, hP.2.2, ?_⟩, rfl⟩
    · rw [Finset.supIndep_iff_pairwiseDisjoint]
      exact hP.pairwiseDisjoint
    · intro hbot
      exact hP.1 ⊥ hbot Finset.bot_eq_empty
  · rintro ⟨F, rfl⟩
    refine ⟨?_, ?_, F.sup_parts⟩
    · intro B hB hBe
      rw [hBe] at hB
      exact F.bot_notMem (by rwa [Finset.bot_eq_empty])
    · intro B hB C hC hBC
      have hd := F.supIndep.pairwiseDisjoint hB hC hBC
      simp only [Function.onFun, id_eq] at hd
      exact Finset.disjoint_iff_inter_eq_empty.mp hd

/-- The finset of all partitions of `s` into exactly `k` blocks.  Every block is a
subset of `s`, so the whole block set lives in `s.powerset.powerset`. -/
def setPartitions (s : Finset α) (k : ℕ) : Finset (Finset (Finset α)) :=
  s.powerset.powerset.filter fun P => IsSetPartition s P ∧ P.card = k

/-- Membership in `setPartitions`, with the ambient `powerset.powerset` condition
discharged. -/
theorem mem_setPartitions {s : Finset α} {P : Finset (Finset α)} {k : ℕ} :
    P ∈ setPartitions s k ↔ IsSetPartition s P ∧ P.card = k := by
  unfold setPartitions
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_powerset]
  intro B hB
  rw [Finset.mem_powerset]
  exact h.1.subset hB

/-- The empty set has exactly one partition into `0` blocks, the empty block set. -/
theorem setPartitions_empty_zero : setPartitions (∅ : Finset α) 0 = {∅} := by
  ext P
  rw [mem_setPartitions, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hcard⟩
    exact Finset.card_eq_zero.mp hcard
  · rintro rfl
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp

/-- The empty set has no partition into a positive number of blocks. -/
theorem setPartitions_empty_succ (k : ℕ) : setPartitions (∅ : Finset α) (k + 1) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_setPartitions] at hP
  obtain ⟨hpart, hcard⟩ := hP
  obtain ⟨B, hB⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
  exact hpart.ne_empty hB (Finset.subset_empty.mp (hpart.subset hB))

/-- A nonempty set has no partition into `0` blocks. -/
theorem setPartitions_zero_of_nonempty {s : Finset α} (hs : s.Nonempty) :
    setPartitions s 0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro P hP
  rw [mem_setPartitions] at hP
  obtain ⟨hpart, hcard⟩ := hP
  rw [Finset.card_eq_zero] at hcard
  subst hcard
  obtain ⟨a, ha⟩ := hs
  rw [← hpart.2.2] at ha
  simp at ha

/-- Adjoining a new element `a ∉ s` as a member of a fresh block `insert a t`,
where `t ⊆ s`, turns a partition of `s \ t` into `k` blocks into a partition of
`insert a s` into `k + 1` blocks.  This is the inverse direction of the block
recurrence. -/
theorem mem_setPartitions_insert {s : Finset α} {a : α} (ha : a ∉ s) {t : Finset α}
    (ht : t ⊆ s) {Q : Finset (Finset α)} {k : ℕ} (hQ : Q ∈ setPartitions (s \ t) k) :
    insert (insert a t) Q ∈ setPartitions (insert a s) (k + 1) := by
  rw [mem_setPartitions] at hQ ⊢
  obtain ⟨hpart, hcard⟩ := hQ
  have hQsub : ∀ B ∈ Q, B ⊆ s \ t := fun B hB => hpart.subset hB
  have hnotmem : insert a t ∉ Q := by
    intro hmem
    have hmem' := hQsub _ hmem (Finset.mem_insert_self a t)
    rw [Finset.mem_sdiff] at hmem'
    exact ha hmem'.1
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact Finset.insert_ne_empty a t
    · exact hpart.ne_empty hB
  · intro B hB C hC hBC
    rcases Finset.mem_insert.mp hB with rfl | hB <;>
      rcases Finset.mem_insert.mp hC with rfl | hC
    · exact absurd rfl hBC
    · rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter] at hy
      have hyC := hQsub _ hC hy.2
      rw [Finset.mem_sdiff] at hyC
      rcases Finset.mem_insert.mp hy.1 with rfl | hyt
      · exact ha hyC.1
      · exact hyC.2 hyt
    · rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [Finset.mem_inter] at hy
      have hyB := hQsub _ hB hy.1
      rw [Finset.mem_sdiff] at hyB
      rcases Finset.mem_insert.mp hy.2 with rfl | hyt
      · exact ha hyB.1
      · exact hyB.2 hyt
    · exact hpart.2.1 B hB C hC hBC
  · rw [Finset.sup_insert, hpart.2.2]
    simp only [id_eq]
    ext y
    simp only [Finset.sup_eq_union, Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff]
    have hts : y ∈ t → y ∈ s := fun h => ht h
    by_cases hyt : y ∈ t <;> tauto
  · rw [Finset.card_insert_of_notMem hnotmem, hcard]

end Definitions

section Weights

variable {α : Type*} [DecidableEq α] {R : Type*} [CommSemiring R]

/-- The total weight of the partitions of `s` into exactly `k` blocks, a block of
size `i` weighing `x i`.  This is the object `thm:bell-poly-partitions` claims is
`B_{n,k}`. -/
def partitionWeight (x : ℕ → R) (s : Finset α) (k : ℕ) : R :=
  ∑ P ∈ setPartitions s k, ∏ B ∈ P, x B.card

/-- `partitionWeight` unfolded. -/
theorem partitionWeight_def (x : ℕ → R) (s : Finset α) (k : ℕ) :
    partitionWeight x s k = ∑ P ∈ setPartitions s k, ∏ B ∈ P, x B.card := rfl

/-- **The block recurrence for the partition-weight sum.**  Splitting a partition
of `insert a s` on the block that contains the new element `a` — that block is
`insert a t` for a uniquely determined `t ⊆ s`, and what remains is a partition of
`s \ t` — gives

`W(insert a s, k+1) = ∑_{t ⊆ s} x_{|t|+1} · W(s \ t, k)`.

This is the combinatorial content of the whole module; everything else is
bookkeeping. -/
theorem partitionWeight_insert (x : ℕ → R) {s : Finset α} {a : α} (ha : a ∉ s) (k : ℕ) :
    partitionWeight x (insert a s) (k + 1) =
      ∑ t ∈ s.powerset, x (t.card + 1) * partitionWeight x (s \ t) k := by
  simp only [partitionWeight_def, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun P => (⟨(blockOf P a).erase a, P.erase (blockOf P a)⟩ :
      Σ _ : Finset α, Finset (Finset α)))
    (fun y => insert (insert a y.1) y.2) ?_ ?_ ?_ ?_ ?_
  · -- the forward map lands in the sigma
    intro P hP
    rw [mem_setPartitions] at hP
    obtain ⟨hpart, hcard⟩ := hP
    obtain ⟨hA, haA⟩ := blockOf_mem hpart (Finset.mem_insert_self a s)
    have hersub : (blockOf P a).erase a ⊆ s := by
      intro y hy
      rw [Finset.mem_erase] at hy
      rcases Finset.mem_insert.mp (hpart.subset hA hy.2) with h | h
      · exact absurd h hy.1
      · exact h
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    refine ⟨hersub, ?_⟩
    rw [mem_setPartitions]
    refine ⟨⟨fun B hB => hpart.ne_empty (Finset.mem_of_mem_erase hB),
      fun B hB C hC hBC => hpart.2.1 B (Finset.mem_of_mem_erase hB) C
        (Finset.mem_of_mem_erase hC) hBC, ?_⟩, ?_⟩
    · rw [hpart.sup_erase hA]
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨hy1, hy2⟩
        rcases hy1 with rfl | hy1
        · exact absurd haA hy2
        · exact ⟨hy1, fun h => hy2 h.2⟩
      · rintro ⟨hy1, hy2⟩
        refine ⟨Or.inr hy1, fun h => hy2 ⟨?_, h⟩⟩
        rintro rfl
        exact ha hy1
    · have hc : (P.erase (blockOf P a)).card = P.card - 1 := Finset.card_erase_of_mem hA
      omega
  · -- the backward map lands in the partitions of `insert a s`
    rintro ⟨t, Q⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hy
    exact mem_setPartitions_insert ha hy.1 hy.2
  · -- backward ∘ forward = id
    intro P hP
    rw [mem_setPartitions] at hP
    obtain ⟨hA, haA⟩ := blockOf_mem hP.1 (Finset.mem_insert_self a s)
    show insert (insert a ((blockOf P a).erase a)) (P.erase (blockOf P a)) = P
    rw [Finset.insert_erase haA, Finset.insert_erase hA]
  · -- forward ∘ backward = id
    rintro ⟨t, Q⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hy
    obtain ⟨ht, hQ⟩ := hy
    have hpart : IsSetPartition (insert a s) (insert (insert a t) Q) :=
      (mem_setPartitions.mp (mem_setPartitions_insert ha ht hQ)).1
    have hblock : blockOf (insert (insert a t) Q) a = insert a t :=
      blockOf_eq hpart (Finset.mem_insert_self _ _) (Finset.mem_insert_self a t)
    have hat : a ∉ t := fun h => ha (ht h)
    have hnotmem : insert a t ∉ Q := by
      intro hmem
      have hmem' := (mem_setPartitions.mp hQ).1.subset hmem (Finset.mem_insert_self a t)
      rw [Finset.mem_sdiff] at hmem'
      exact ha hmem'.1
    show (⟨(blockOf (insert (insert a t) Q) a).erase a,
        (insert (insert a t) Q).erase (blockOf (insert (insert a t) Q) a)⟩ :
        Σ _ : Finset α, Finset (Finset α)) = ⟨t, Q⟩
    simp only [hblock, Finset.erase_insert hat, Finset.erase_insert hnotmem]
  · -- the weights match: peel off the block containing `a`
    intro P hP
    rw [mem_setPartitions] at hP
    obtain ⟨hA, haA⟩ := blockOf_mem hP.1 (Finset.mem_insert_self a s)
    have hcardA : ((blockOf P a).erase a).card + 1 = (blockOf P a).card := by
      have h1 : ((blockOf P a).erase a).card = (blockOf P a).card - 1 :=
        Finset.card_erase_of_mem haA
      have h2 : 0 < (blockOf P a).card := Finset.card_pos.mpr ⟨a, haA⟩
      omega
    show ∏ B ∈ P, x B.card
        = x (((blockOf P a).erase a).card + 1) * ∏ B ∈ P.erase (blockOf P a), x B.card
    rw [hcardA]
    exact (Finset.mul_prod_erase P (fun B => x B.card) hA).symm

/-- A sum over the powerset whose summand depends only on the cardinality of the
subset collapses to a binomially weighted sum over cardinalities.  This is what
turns the recurrence of `partitionWeight_insert` into the recurrence defining
`partialBell`. -/
theorem sum_powerset_card_mul (s : Finset α) (g : ℕ → R) :
    ∑ t ∈ s.powerset, g t.card
      = ∑ i ∈ Finset.range (s.card + 1), (s.card.choose i : R) * g i := by
  rw [Finset.sum_powerset]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_powersetCard, nsmul_eq_mul]

/-- **`partialBell` is the weighted count of set partitions**
(`thm:bell-poly-partitions`, first half).  The weight sum has the same initial
data and the same block recurrence as `partialBell`, so the two agree.

Note that no transport lemma is needed: strong induction on `#s` supplies the
cardinality-only dependence for free, because the residual sets `s \ t` appearing
in the recurrence are strictly smaller. -/
theorem partitionWeight_eq_partialBell (x : ℕ → R) :
    ∀ (n : ℕ) (s : Finset α), s.card = n → ∀ k : ℕ,
      partitionWeight x s k = partialBell x n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      intro s hs k
      have hsempty : s = ∅ := Finset.card_eq_zero.mp hs
      subst hsempty
      cases k with
      | zero =>
        rw [partitionWeight_def, setPartitions_empty_zero, Finset.sum_singleton,
          Finset.prod_empty, partialBell_zero_zero]
      | succ k =>
        rw [partitionWeight_def, setPartitions_empty_succ, Finset.sum_empty,
          partialBell_zero_succ]
    | succ m =>
      intro s hs k
      have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
      cases k with
      | zero =>
        rw [partitionWeight_def, setPartitions_zero_of_nonempty hsne, Finset.sum_empty,
          partialBell_succ_zero]
      | succ j =>
        obtain ⟨a, ha⟩ := hsne
        have hins : insert a (s.erase a) = s := Finset.insert_erase ha
        have hane : a ∉ s.erase a := Finset.notMem_erase a s
        have hcard : (s.erase a).card = m := by
          rw [Finset.card_erase_of_mem ha]; omega
        have key : ∑ t ∈ (s.erase a).powerset,
              x (t.card + 1) * partitionWeight x (s.erase a \ t) j
            = ∑ t ∈ (s.erase a).powerset,
              x (t.card + 1) * partialBell x (m - t.card) j := by
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [Finset.mem_powerset] at ht
          have hct : (s.erase a \ t).card = m - t.card := by
            rw [Finset.card_sdiff_of_subset ht, hcard]
          rw [ih (s.erase a \ t).card (by omega) (s.erase a \ t) rfl j, hct]
        rw [← hins, partitionWeight_insert x hane j, key,
          sum_powerset_card_mul (s.erase a) (fun i => x (i + 1) * partialBell x (m - i) j),
          hcard, partialBell_succ_succ]

/-- **The weighted-partition interpretation of `partialBell`**
(`thm:bell-poly-partitions`): `B_{n,k}` is the total weight of the partitions of
an `n`-element labelled set into exactly `k` blocks, a block of size `i` carrying
weight `x i`. -/
theorem partialBell_eq_sum_setPartitions (x : ℕ → R) (s : Finset α) (k : ℕ) :
    partialBell x s.card k = ∑ P ∈ setPartitions s k, ∏ B ∈ P, x B.card := by
  rw [← partitionWeight_def]
  exact (partitionWeight_eq_partialBell x s.card s rfl k).symm

end Weights

section Range

variable {R : Type*} [CommSemiring R]

/-- `thm:bell-poly-partitions` on the standard `n`-element labelled set
`{0, 1, …, n-1}`. -/
theorem partialBell_eq_sum_setPartitions_range (x : ℕ → R) (n k : ℕ) :
    partialBell x n k = ∑ P ∈ setPartitions (Finset.range n) k, ∏ B ∈ P, x B.card := by
  have h := partialBell_eq_sum_setPartitions x (Finset.range n) k
  rwa [Finset.card_range] at h

end Range

section Complete

variable {α : Type*} [DecidableEq α] {R : Type*} [CommSemiring R]

/-- The number of blocks of a partition, summed by size, recovers the size of the
underlying set. -/
theorem card_eq_sum_card_of_isSetPartition {s : Finset α} {P : Finset (Finset α)}
    (hP : IsSetPartition s P) : s.card = ∑ B ∈ P, B.card := by
  conv_lhs => rw [← hP.2.2]
  rw [Finset.sup_eq_biUnion, Finset.card_biUnion hP.pairwiseDisjoint]
  rfl

/-- A partition of `s` has at most `#s` blocks, since the blocks are nonempty and
disjoint. -/
theorem card_le_card_of_isSetPartition {s : Finset α} {P : Finset (Finset α)}
    (hP : IsSetPartition s P) : P.card ≤ s.card := by
  rw [card_eq_sum_card_of_isSetPartition hP, Finset.card_eq_sum_ones P]
  exact Finset.sum_le_sum fun B hB =>
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (hP.ne_empty hB))

/-- The finset of *all* partitions of `s`, of any number of blocks. -/
def allSetPartitions (s : Finset α) : Finset (Finset (Finset α)) :=
  s.powerset.powerset.filter (IsSetPartition s)

/-- Membership in `allSetPartitions`. -/
theorem mem_allSetPartitions {s : Finset α} {P : Finset (Finset α)} :
    P ∈ allSetPartitions s ↔ IsSetPartition s P := by
  unfold allSetPartitions
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_powerset]
  intro B hB
  rw [Finset.mem_powerset]
  exact h.subset hB

/-- Grading all partitions of `s` by their number of blocks, which never exceeds
`#s`. -/
theorem allSetPartitions_eq_biUnion (s : Finset α) :
    allSetPartitions s = (Finset.range (s.card + 1)).biUnion fun k => setPartitions s k := by
  ext P
  rw [Finset.mem_biUnion, mem_allSetPartitions]
  constructor
  · intro hP
    exact ⟨P.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_card_of_isSetPartition hP)),
      mem_setPartitions.mpr ⟨hP, rfl⟩⟩
  · rintro ⟨k, -, hk⟩
    exact (mem_setPartitions.mp hk).1

/-- The total weight of all partitions of `s`, graded by block count. -/
theorem sum_allSetPartitions (x : ℕ → R) (s : Finset α) :
    ∑ P ∈ allSetPartitions s, ∏ B ∈ P, x B.card
      = ∑ k ∈ Finset.range (s.card + 1), partitionWeight x s k := by
  have hdisj : (↑(Finset.range (s.card + 1)) : Set ℕ).PairwiseDisjoint
      fun k => setPartitions s k := by
    intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hi hj
    rw [mem_setPartitions] at hi hj
    exact hij (hi.2.symm.trans hj.2)
  simp only [partitionWeight_def]
  rw [allSetPartitions_eq_biUnion, Finset.sum_biUnion hdisj]

/-- **The complete Bell polynomial is the total weight of all partitions**
(`thm:bell-poly-partitions`, second half). -/
theorem bell_complete_eq_sum_allSetPartitions (x : ℕ → R) (n : ℕ) :
    Bell.complete x n
      = ∑ P ∈ allSetPartitions (Finset.range n), ∏ B ∈ P, x B.card := by
  rw [sum_allSetPartitions, Finset.card_range, bell_complete_eq_sum_partialBell]
  exact Finset.sum_congr rfl fun k _ =>
    (partitionWeight_eq_partialBell x n (Finset.range n) (Finset.card_range n) k).symm

end Complete

section Stirling

variable {α : Type*} [DecidableEq α]

/-- **Stirling numbers of the second kind count set partitions.**  Mathlib defines
`Nat.stirlingSecond` by its recurrence and states the counting interpretation only
in a docstring — `Mathlib/Combinatorics/Enumerative/Bell.lean` even carries an
explicit `TODO` recording that the counting property is unproved.  Taking all
weights equal to `1` in `partitionWeight_eq_partialBell` and applying
`partialBell_one` supplies the proof for the second-kind numbers. -/
theorem card_setPartitions (s : Finset α) (k : ℕ) :
    (setPartitions s k).card = Nat.stirlingSecond s.card k := by
  have h := partitionWeight_eq_partialBell (R := ℕ) (fun _ => 1) s.card s rfl k
  rw [partitionWeight_def, partialBell_one] at h
  simpa using h

/-- The number of partitions of `{0, 1, …, n-1}` into exactly `k` blocks is
`Nat.stirlingSecond n k`. -/
theorem card_setPartitions_range (n k : ℕ) :
    (setPartitions (Finset.range n) k).card = Nat.stirlingSecond n k := by
  have h := card_setPartitions (Finset.range n) k
  rwa [Finset.card_range] at h

end Stirling

end Fabius
