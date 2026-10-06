import GowersSzemeredi.Proofs16Interpolation

/-! # Distinct anchors in the sampling step of Lemma 16.10

Sampling twice from a class does not imply sampling two distinct elements.
The printed binomial estimate cannot hold for singleton classes, even when
they meet its stated size threshold. This file records that obstruction
using exact finite counts and rational arithmetic.
-/
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
      intro heq
      exact Finset.disjoint_left.mp hdisj hi (heq.symm ▸ hj)
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
  have hdisj : Disjoint A (C \ A) := by
    exact Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha)
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

/-- A corrected sampling budget: a class of at least two elements and
density at least sigma/q has failure probability at most sigma once
r*sigma^2 >= 6*q. Singleton classes must be treated separately. -/
theorem section16_distinct_sampling_budget {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (C : Finset α) (q r : Nat) (σ : ℝ) (hσ : 0 < σ) (hC : 2 ≤ C.card)
    (hsize : σ * Fintype.card α ≤ (q : ℝ) * C.card)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ ^ 2) :
    ((Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair C sample)).card : ℝ) /
      Fintype.card (Fin r → α) ≤ σ := by
  let n : ℝ := Fintype.card α
  -- Use the cast of the natural-number floor, not real division.
  let d0 : ℝ := (C.card / 2 : Nat)
  let x : ℝ := (n - d0) / n
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hd : 0 ≤ d0 := by positivity
  have hdn : C.card / 2 ≤ Fintype.card α :=
    (Nat.div_le_self _ _).trans (Finset.card_le_univ C)
  have hdle : d0 ≤ n := by dsimp [d0, n]; exact_mod_cast hdn
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hdle) hn.le
  have hthird : C.card ≤ 3 * (C.card / 2) := by omega
  have hc : (C.card : ℝ) ≤ 3 * d0 := by dsimp [d0]; exact_mod_cast hthird
  have hdensity : σ * n ≤ 3 * (q : ℝ) * d0 := by
    have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    dsimp [n]
    nlinarith [hsize]
  have hprod : 2 * σ * n ≤ (r : ℝ) * σ ^ 2 * d0 := by
    have hm := mul_le_mul_of_nonneg_right hr hd
    nlinarith [hdensity]
  have hprod' : 2 * n ≤ (r : ℝ) * σ * d0 := by
    exact le_of_mul_le_mul_left
      (show σ * (2 * n) ≤ σ * ((r : ℝ) * σ * d0) by nlinarith [hprod]) hσ
  have hratio : 2 ≤ (r : ℝ) * σ * (d0 / n) := by
    apply (le_div_iff₀ hn).mpr at hprod'
    simpa [mul_div_assoc] using hprod'
  have hone : 1 - x = d0 / n := by
    dsimp [x]
    field_simp
    ring
  have hpow := section16_pow_mul_linear_le_one hx r
  rw [hone] at hpow
  have hbudget : 2 ≤ σ * (1 + (r : ℝ) * (d0 / n)) := by nlinarith [hratio]
  have hfinal : 2 * x ^ r ≤ σ := by
    have h1 := mul_le_mul_of_nonneg_left hpow hσ.le
    have h2 := mul_le_mul_of_nonneg_left hbudget (pow_nonneg hx r)
    nlinarith [h1, h2]
  apply (section16_distinct_sampling_probability_bound C r).trans
  simpa [x, n, d0, Nat.cast_sub hdn] using hfinal

theorem section16_distinct_sampling_ceil_budget {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (C : Finset α) (q : Nat) (σ : ℝ) (hσ : 0 < σ) (hC : 2 ≤ C.card)
    (hsize : σ * Fintype.card α ≤ (q : ℝ) * C.card) :
    ((Finset.univ.filter (fun sample : Fin ⌈6 * (q : ℝ) / σ ^ 2⌉₊ → α =>
      ¬ section16SampleHasDistinctPair C sample)).card : ℝ) /
      Fintype.card (Fin ⌈6 * (q : ℝ) / σ ^ 2⌉₊ → α) ≤ σ := by
  apply section16_distinct_sampling_budget C q _ σ hσ hC hsize
  exact (div_le_iff₀ (sq_pos_of_pos hσ)).mp (Nat.le_ceil _)

theorem section16SampleHasDistinctPair_singleton {α : Type*} [DecidableEq α]
    {r : Nat} (a : α) (sample : Fin r → α) :
    ¬ section16SampleHasDistinctPair {a} sample := by
  rintro ⟨i, j, hi, hj, hne⟩
  exact hne ((Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm)

/-- Every sample misses a pair of distinct elements of a singleton,
regardless of its length or the ambient finite space. -/
theorem section16_singleton_failure_set {α : Type*} [Fintype α] [DecidableEq α]
    (r : Nat) (a : α) :
    Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair {a} sample) = Finset.univ := by
  classical
  ext sample
  simp [section16SampleHasDistinctPair_singleton]

/-- Exact failure probability in the uniform finite sample space. -/
theorem section16_singleton_failure_probability {α : Type*}
    [Fintype α] [DecidableEq α] (r : Nat) (a : α) :
    ((Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair {a} sample)).card : ℚ) /
      Fintype.card (Fin r → α) = 1 := by
  classical
  letI : Nonempty α := ⟨a⟩
  rw [section16_singleton_failure_set, Finset.card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- With q=1, sigma=1/4, |J|=4, and r=ceil(q*sigma^(-2))=16,
a singleton meets the non-small-class threshold. Its true failure
probability is one, whereas the printed expression is below sigma. -/
theorem section16_printed_distinct_sampling_counterexample :
    (({(0 : Fin 4)} : Finset (Fin 4)).card : ℚ) = (1 / 4 : ℚ) * 4 / 1 ∧
    (⌈(1 : ℚ) * (1 / 4 : ℚ) ^ (-2 : Int)⌉₊ = 16) ∧
    (((Finset.univ.filter (fun sample : Fin 16 → Fin 4 =>
      ¬ section16SampleHasDistinctPair {0} sample)).card : ℚ) /
      Fintype.card (Fin 16 → Fin 4) = 1) ∧
    ((1 - (1 / 4 : ℚ)) ^ 16 + 16 * (1 / 4 : ℚ) *
      (1 - (1 / 4 : ℚ)) ^ 15 < 1 / 4) := by
  refine ⟨by norm_num, by norm_num, section16_singleton_failure_probability 16 0, ?_⟩
  norm_num

end LeanProofs.GowersSzemeredi
