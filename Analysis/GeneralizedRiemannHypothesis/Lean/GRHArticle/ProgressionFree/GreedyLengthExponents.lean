import GRHArticle.ProgressionFree.IntegerSharedDeletion

/-!
# Greedy exponent sets for every progression length

Scan the exponents in increasing order. The test at exponent `n` searches
positive steps and checks whether all preceding terms of a progression
ending at `n` were accepted.
-/

namespace GRHArticle.ProgressionFree

/-- Executable membership test for the greedy exponent sequence. -/
def greedyLengthKeep (k n : ℕ) : Bool :=
  !((List.range (n+1)).any fun d ↦
    if h : 0 < d ∧ (k-1)*d ≤ n then
      (List.range (k-1)).attach.all fun i ↦ greedyLengthKeep k (n-(k-1-i.val)*d)
    else false)
termination_by n
decreasing_by
  have hi := List.mem_range.mp i.property
  have hd : 0 < (k-1-i.val)*d := Nat.mul_pos (by omega) h.1
  have hn : 0 < n := lt_of_lt_of_le (Nat.mul_pos (by omega) h.1) h.2
  exact Nat.sub_lt hn hd

/-- The article's greedy (k)-term-progression-free exponent set (G_k). -/
def greedyLengthExponents (k : ℕ) : Set ℕ :=
  {n | greedyLengthKeep k n = true}

/-- Every rejected exponent has a positive-step greedy witness ending at it. -/
theorem not_mem_greedyLengthExponents_iff {k n : ℕ} (hk : 2 ≤ k) :
    n ∉ greedyLengthExponents k ↔ ∃ d : ℕ, 0 < d ∧ (k-1)*d ≤ n ∧
      ∀ i < k-1, n-(k-1-i)*d ∈ greedyLengthExponents k := by
  change ¬ greedyLengthKeep k n = true ↔ _
  rw [greedyLengthKeep]
  have hBool (l : Bool) : (¬ (!l) = true) ↔ l = true := by cases l <;> decide
  rw [hBool, List.any_eq_true]
  constructor
  · rintro ⟨d, hd, htest⟩
    split at htest
    case isTrue h =>
      refine ⟨d,h.1,h.2, fun i hi ↦ ?_⟩
      exact List.all_eq_true.mp htest ⟨i, List.mem_range.mpr hi⟩ (List.mem_attach _ _)
    case isFalse => contradiction
  · rintro ⟨d, hd, hbound, hprev⟩
    have hdN : d ≤ n := (Nat.le_mul_of_pos_left _ (by omega : 0 < k-1)).trans hbound
    refine ⟨d, List.mem_range.mpr (Nat.lt_succ_of_le hdN), ?_⟩
    rw [dif_pos ⟨hd,hbound⟩]
    exact List.all_eq_true.mpr fun i _ ↦ hprev i.val (List.mem_range.mp i.property)

/-- All exponents up to (k-2) survive the greedy test. -/
theorem mem_greedyLengthExponents_of_lt {k n : ℕ} (hk : 2 ≤ k) (hn : n < k-1) :
    n ∈ greedyLengthExponents k := by
  by_contra h
  obtain ⟨d, hd, hbound, _⟩ := (not_mem_greedyLengthExponents_iff hk).mp h
  exact (not_le_of_gt hn) ((Nat.le_mul_of_pos_right _ hd).trans hbound)

/-- The first rejected exponent is (k-1). -/
theorem not_mem_greedyLengthExponents_pred {k : ℕ} (hk : 2 ≤ k) :
    k-1 ∉ greedyLengthExponents k := by
  apply (not_mem_greedyLengthExponents_iff hk).mpr
  refine ⟨1, by decide, by simp, fun i hi ↦ ?_⟩
  simpa only [mul_one, show k-1-(k-1-i) = i by omega] using
    mem_greedyLengthExponents_of_lt hk hi

private theorem positive_step_not_greedy {k : ℕ} (hk : 2 ≤ k)
    (x : Fin k → ℕ) (u d : ℤ) (hd : 0 < d)
    (hmem : ∀ i, x i ∈ greedyLengthExponents k)
    (hx : ∀ i, (x i : ℤ) = u + (i.val : ℤ)*d) : False := by
  let j : Fin k := ⟨0, by omega⟩
  let l : Fin k := ⟨k-1, by omega⟩
  have hu : 0 ≤ u := by
    have h0 : (x j : ℤ) = u := by simpa [j] using hx j
    exact h0 ▸ Nat.cast_nonneg (x j)
  let D := d.toNat
  have hD : (D : ℤ) = d := Int.toNat_of_nonneg hd.le
  have hDpos : 0 < D := by exact_mod_cast (hD.symm ▸ hd)
  have hl : (x l : ℤ) = u + ((k-1 : ℕ) : ℤ)*d := hx l
  have hbound : (k-1)*D ≤ x l := by
    exact_mod_cast (show ((k-1 : ℕ) : ℤ)*(D : ℤ) ≤ (x l : ℤ) by rw [hD,hl]; linarith)
  apply (not_mem_greedyLengthExponents_iff hk).mpr ⟨D,hDpos,hbound,?_⟩ (hmem l)
  intro i hi
  let t : Fin k := ⟨i, by omega⟩
  have ht : (x t : ℤ) = u + (i : ℤ)*d := hx t
  have he : x t + (k-1-i)*D = x l := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [Nat.cast_sub hi.le, hD, ht, hl]
    ring
  rw [← he, Nat.add_sub_cancel]
  exact hmem t

/-- The greedy exponent rule excludes arbitrary signed progressions of its
chosen length. Reversing a negative-step string gives the positive-step
witness ruled out by its last term. -/
theorem kTermAPFree_greedyLengthExponents {k : ℕ} (hk : 2 ≤ k) :
    KTermAPFree k (greedyLengthExponents k) := by
  intro x u d hmem hx
  rcases lt_trichotomy d 0 with hd | hd | hd
  · exfalso
    apply positive_step_not_greedy hk (fun i ↦ x i.rev)
      (u+((k-1 : ℕ) : ℤ)*d) (-d) (by omega) (fun i ↦ hmem i.rev)
    intro i
    have hi := i.isLt
    have hle : i.val ≤ k-1 := by omega
    have hv : (i.rev.val : ℤ) = ((k-1 : ℕ) : ℤ)-(i.val : ℤ) := by
      rw [← Nat.cast_sub hle]
      congr 1
      simp only [Fin.val_rev]
      omega
    rw [hx i.rev,hv]
    ring
  · exact hd
  · exact (positive_step_not_greedy hk x u d hd hmem hx).elim

/-- The article's integer greedy exponent-rule product (mathcal G_k). -/
def integerGreedyLengthSet (k : ℕ) : Set ℕ :=
  integerIndependentExponentSet (greedyLengthExponents k)

theorem kTermGPFree_integerGreedyLengthSet {k : ℕ} (hk : 2 ≤ k) :
    KTermGPFree k (integerGreedyLengthSet k) :=
  kTermGPFree_integerIndependentExponentSet hk (kTermAPFree_greedyLengthExponents hk)

/-- The actual shared-deletion construction based on the greedy exponent rule. -/
def integerGreedyLengthExchange (k marker : ℕ) (B : Finset ℕ) : Set ℕ :=
  integerSharedDeletionSet k (greedyLengthExponents k) marker B

theorem kTermGPFree_integerGreedyLengthExchange {k : ℕ} (hk : 3 ≤ k)
    (marker : ℕ) (B : Finset ℕ) : KTermGPFree k (integerGreedyLengthExchange k marker B) :=
  kTermGPFree_integerSharedDeletionSet hk (kTermAPFree_greedyLengthExponents (by omega))
    (mem_greedyLengthExponents_of_lt (by omega) (by omega))
    (by simpa only [show k-2+1 = k-1 by omega] using not_mem_greedyLengthExponents_pred (k := k) (by omega))
    marker B

end GRHArticle.ProgressionFree
