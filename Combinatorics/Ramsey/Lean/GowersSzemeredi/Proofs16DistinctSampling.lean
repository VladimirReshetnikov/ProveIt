import GowersSzemeredi.Proofs16Interpolation

/-! # Distinct anchors in the sampling step of Lemma 16.10

Sampling twice from a class does not imply sampling two distinct elements.
The printed binomial estimate cannot hold for singleton classes, even when
they meet its stated size threshold. This file records that obstruction
using exact finite counts and rational arithmetic.

`section16SampleHasDistinctPair_singleton`,
`section16_distinct_sampling_budget`,
`section16_printed_distinct_sampling_counterexample`,
`section16_singleton_failure_probability` and `section16_singleton_failure_set`
are in `Proofs16DistinctSamplingSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace LeanProofs.GowersSzemeredi

def section16SampleHasDistinctPair {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α) : Prop :=
  ∃ i j, sample i ∈ C ∧ sample j ∈ C ∧ sample i ≠ sample j

def section16MissingSamples {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α) (r : Nat) : Finset (Fin r → α) :=
  Finset.univ.filter (fun sample => ∀ i, sample i ∉ C)

theorem section16MissingSamples_card {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α) (r : Nat) :
    (section16MissingSamples C r).card = (Fintype.card α - C.card) ^ r := by
  have heq : section16MissingSamples C r = Fintype.piFinset (fun _ : Fin r => Cᶜ) := by
    ext sample
    simp [section16MissingSamples, Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset_const, Finset.card_compl]

/-- Hitting two disjoint parts guarantees distinct anchors. The union
bound therefore gives a valid replacement for the two-hit estimate. -/
theorem section16_distinct_sampling_split_bound {α : Type*}
    [Fintype α] [DecidableEq α] (C A B : Finset α) (r : Nat)
    (hA : A ⊆ C) (hB : B ⊆ C) (hdisj : Disjoint A B) :
    (Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair C sample)).card ≤
      (Fintype.card α - A.card) ^ r + (Fintype.card α - B.card) ^ r := by
  have hsub : (Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair C sample)) ⊆
      section16MissingSamples A r ∪ section16MissingSamples B r := by
    intro sample hs
    have hfail := (Finset.mem_filter.mp hs).2
    by_cases ha : ∀ i, sample i ∉ A
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
    · push Not at ha
      obtain ⟨i, hi⟩ := ha
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      apply hfail
      refine ⟨i, j, hA hi, hB hj, ?_⟩
      exact fun heq => Finset.disjoint_left.mp hdisj hi (heq.symm ▸ hj)
  calc
    _ ≤ (section16MissingSamples A r ∪ section16MissingSamples B r).card :=
      Finset.card_le_card hsub
    _ ≤ (section16MissingSamples A r).card + (section16MissingSamples B r).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [section16MissingSamples_card, section16MissingSamples_card]

/-- Splitting the class into two nearly equal parts yields a bound that
counts repeated draws correctly. The bound is useful once |C| >= 2. -/
theorem section16_distinct_sampling_half_bound {α : Type*}
    [Fintype α] [DecidableEq α] (C : Finset α) (r : Nat) :
    (Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair C sample)).card ≤
      2 * (Fintype.card α - C.card / 2) ^ r := by
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq (Nat.div_le_self C.card 2)
  have hdisj : Disjoint A (C \ A) :=
    Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha)
  have hbound := section16_distinct_sampling_split_bound C A (C \ A) r hA
    Finset.sdiff_subset hdisj
  rw [Finset.card_sdiff_of_subset hA, hcard] at hbound
  have hhalf : C.card / 2 ≤ C.card - C.card / 2 := by omega
  have hpow : (Fintype.card α - (C.card - C.card / 2)) ^ r ≤
      (Fintype.card α - C.card / 2) ^ r := by
    gcongr
  omega

theorem section16_distinct_sampling_probability_bound {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (C : Finset α) (r : Nat) :
    ((Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair C sample)).card : ℝ) /
      Fintype.card (Fin r → α) ≤
      2 * (((Fintype.card α - C.card / 2 : Nat) : ℝ) / Fintype.card α) ^ r := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcount : ((Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair C sample)).card : ℝ) ≤
      2 * ((Fintype.card α - C.card / 2 : Nat) : ℝ) ^ r := by
    exact_mod_cast section16_distinct_sampling_half_bound C r
  rw [Fintype.card_pi_const, Nat.cast_pow]
  calc
    _ ≤ (2 * ((Fintype.card α - C.card / 2 : Nat) : ℝ) ^ r) /
        (Fintype.card α : ℝ) ^ r :=
      (div_le_div_iff_of_pos_right (pow_pos hn r)).mpr hcount
    _ = _ := by rw [div_pow]; ring

/-- An elementary geometric-decay estimate, avoiding logarithmic constants. -/
theorem section16_pow_mul_linear_le_one {x : ℝ} (hx : 0 ≤ x)
    (r : Nat) : x ^ r * (1 + r * (1 - x)) ≤ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : x * (1 + (r + 1 : ℝ) * (1 - x)) ≤ 1 + r * (1 - x) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r + 1 by positivity) (sq_nonneg (1 - x))]
    calc
      _ = x ^ r * (x * (1 + (r + 1 : ℝ) * (1 - x))) := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one, mul_assoc]
      _ ≤ x ^ r * (1 + r * (1 - x)) := mul_le_mul_of_nonneg_left hstep (pow_nonneg hx r)
      _ ≤ 1 := ih

end LeanProofs.GowersSzemeredi
