import GowersSzemeredi.Proofs16DistinctSampling

/-! Declarations of `Proofs16DistinctSampling` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LeanProofs.GowersSzemeredi

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
  ext sample
  simp [section16SampleHasDistinctPair_singleton]

/-- Exact failure probability in the uniform finite sample space. -/
theorem section16_singleton_failure_probability {α : Type*}
    [Fintype α] [DecidableEq α] (r : Nat) (a : α) :
    ((Finset.univ.filter (fun sample : Fin r → α =>
      ¬ section16SampleHasDistinctPair {a} sample)).card : ℚ) /
      Fintype.card (Fin r → α) = 1 := by
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
