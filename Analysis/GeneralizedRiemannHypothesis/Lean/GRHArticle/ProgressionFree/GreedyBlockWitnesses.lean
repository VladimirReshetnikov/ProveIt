import GRHArticle.ProgressionFree.GreedyLengthExponents

/-!
# Greedy witnesses in a block of prime exponents

Each rejected exponent completes a progression with smaller accepted
exponents. Aligning these witnesses across all coordinates gives one
progression through an excluded vector and its proper divisors in exponent
coordinates.
-/

namespace GRHArticle.ProgressionFree

/-- Absence of any affine progression with a nonzero integral step vector. -/
def KTermVectorAPFree {ι : Type*} (k : ℕ) (F : Set (ι → ℕ)) : Prop :=
  ∀ (x : Fin k → ι → ℕ) (a d : ι → ℤ), (∀ i, x i ∈ F) →
    (∀ i p, (x i p : ℤ) = a p + (i.val : ℤ)*d p) → ∀ p, d p = 0

/-- The accepted independent greedy patterns in a block of coordinates. -/
def greedyExponentPatterns (ι : Type*) (k : ℕ) : Set (ι → ℕ) :=
  {x | ∀ p, x p ∈ greedyLengthExponents k}

theorem kTermVectorAPFree_greedyExponentPatterns (ι : Type*) {k : ℕ} (hk : 2 ≤ k) :
    KTermVectorAPFree k (greedyExponentPatterns ι k) := by
  intro x a d hmem hx p
  exact kTermAPFree_greedyLengthExponents hk (fun i ↦ x i p) (a p) (d p)
    (fun i ↦ hmem i p) (fun i ↦ hx i p)

private theorem exists_greedyPredecessorStep {k : ℕ} (hk : 2 ≤ k) (a : ℕ) :
    ∃ d : ℕ, (d = 0 ↔ a ∈ greedyLengthExponents k) ∧
      (k-1)*d ≤ a ∧ ∀ j < k-1, a-(k-1-j)*d ∈ greedyLengthExponents k := by
  by_cases ha : a ∈ greedyLengthExponents k
  · exact ⟨0, by simp [ha], by simp, fun j _ ↦ by simpa using ha⟩
  · obtain ⟨d,hd,hle,hprev⟩ := (not_mem_greedyLengthExponents_iff hk).mp ha
    exact ⟨d, by simp [hd.ne',ha], hle, hprev⟩

/-- A permitted vector outside the greedy rule forces some strictly smaller
greedy predecessor to be omitted. This is the witness used in the
light-block reciprocal-mass comparison. -/
theorem exists_missing_greedyBlockWitness {ι : Type*} {k : ℕ} (hk : 2 ≤ k)
    {F : Set (ι → ℕ)} (hF : KTermVectorAPFree k F) {v : ι → ℕ}
    (hv : v ∈ F) (hvG : v ∉ greedyExponentPatterns ι k) :
    ∃ t ∈ greedyExponentPatterns ι k \ F, t ≤ v ∧ t ≠ v := by
  classical
  choose step hs using fun p : ι ↦ exists_greedyPredecessorStep hk (v p)
  obtain ⟨q,hq⟩ : ∃ q : ι, step q ≠ 0 := by
    by_contra! h
    exact hvG (fun q ↦ (hs q).1.mp (h q))
  let x (i : Fin k) (p : ι) := v p-(k-1-i.val)*step p
  let a (p : ι) : ℤ := (v p : ℤ)-((k-1 : ℕ) : ℤ)*(step p : ℤ)
  have hAffine (i : Fin k) (p : ι) :
      (x i p : ℤ) = a p + (i.val : ℤ)*(step p : ℤ) := by
    have hi := i.isLt
    have hle : i.val ≤ k-1 := by omega
    have hp : (k-1-i.val)*step p ≤ v p :=
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans (hs p).2.1
    dsimp only [a,x]
    rw [Nat.cast_sub hp, Nat.cast_mul, Nat.cast_sub hle]
    ring
  have hmiss : ∃ i : Fin k, i.val < k-1 ∧ x i ∉ F := by
    by_contra! h
    have hm (i : Fin k) : x i ∈ F := by
      by_cases hi : i.val < k-1
      · exact h i hi
      · have he : k-1-i.val = 0 := by omega
        have hx : x i = v := by funext p; simp [x,he]
        exact hx.symm ▸ hv
    have h := hF x a (fun p ↦ (step p : ℤ)) hm hAffine q
    exact hq (by exact_mod_cast h)
  obtain ⟨i,hi,hif⟩ := hmiss
  refine ⟨x i, ⟨fun p ↦ (hs p).2.2 i.val hi, hif⟩, fun p ↦ Nat.sub_le _ _, ?_⟩
  have hstep := Nat.mul_pos (show 0 < k-1-i.val by omega) (Nat.pos_of_ne_zero hq)
  have hvpos := lt_of_lt_of_le (Nat.mul_pos (show 0 < k-1 by omega) (Nat.pos_of_ne_zero hq))
    (hs q).2.1
  exact fun he ↦ (Nat.sub_lt hvpos hstep).ne (congrFun he q)

end GRHArticle.ProgressionFree
