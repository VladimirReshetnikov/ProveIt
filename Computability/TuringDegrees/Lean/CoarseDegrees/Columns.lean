import CoarseDegrees.Density
import Mathlib.Computability.Partrec
import Mathlib.Computability.RE

/-!
# Dyadic columns

The partition of `ℕ` underlying the dyadic code `R(A)` of the synthesis (Section 6) and of
research report 10 (Theorem 1.4).  `col n` is the exponent of `2` in `n + 1`, so that the
`k`-th column is `{n : col n = k}`; it is defined by bounded minimization, which makes it
computable.

The facts the coarse track needs are the exact tail count `|{n < N : 2^K ∣ n+1}| = ⌊N/2^K⌋`
and its consequence: a set meeting every column in a bounded set has density zero.
Everything here is proved.
-/

noncomputable section

open Filter Topology
open scoped Classical

namespace CoarseDegrees

/-- Some power of two beyond `n + 1` fails to divide it. -/
theorem col_exists (n : ℕ) : ∃ j, ¬ (2 ^ (j + 1) ∣ (n + 1)) := by
  refine ⟨n, fun hd => ?_⟩
  have h1 : 2 ^ (n + 1) ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hd
  have h2 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  omega

/-- The index of the dyadic column of `n`: the exponent of `2` in `n + 1`. -/
def col (n : ℕ) : ℕ := Nat.find (col_exists n)

theorem col_spec (n : ℕ) : ¬ (2 ^ (col n + 1) ∣ (n + 1)) := Nat.find_spec (col_exists n)

theorem pow_col_dvd (n : ℕ) : 2 ^ (col n) ∣ (n + 1) := by
  rcases Nat.eq_zero_or_pos (col n) with h | h
  · rw [h]
    simp
  · have hlt : col n - 1 < col n := by omega
    have := Nat.find_min (col_exists n) (m := col n - 1) hlt
    rw [Nat.sub_add_cancel h] at this
    exact not_not.mp this

/-- The tail `{n : 2^K ∣ n+1}` is the union of the columns from `K` on. -/
theorem pow_dvd_iff_le_col {K n : ℕ} : 2 ^ K ∣ (n + 1) ↔ K ≤ col n := by
  constructor
  · intro hd
    by_contra hlt
    exact col_spec n (dvd_trans (pow_dvd_pow 2 (by omega)) hd)
  · intro hle
    exact dvd_trans (pow_dvd_pow 2 hle) (pow_col_dvd n)

theorem col_lt_iff {K n : ℕ} : col n < K ↔ ¬ (2 ^ K ∣ (n + 1)) := by
  rw [pow_dvd_iff_le_col]
  omega

/-- `col` is computable: the search is bounded by `n`. -/
theorem computable_col : Computable col := by
  have hP : ComputablePred (fun p : ℕ × ℕ => ¬ (2 ^ (p.2 + 1) ∣ (p.1 + 1))) := by
    have hd : PrimrecPred (fun p : ℕ × ℕ => 2 ^ (p.2 + 1) ∣ (p.1 + 1)) := by
      have : PrimrecPred (fun p : ℕ × ℕ => (p.1 + 1) % 2 ^ (p.2 + 1) = 0) :=
        Primrec.eq.comp
          (Primrec.nat_mod.comp (Primrec.succ.comp Primrec.fst)
            ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
              (Primrec.succ.comp Primrec.snd)))
          (Primrec.const 0)
      exact this.of_eq fun p => by rw [Nat.dvd_iff_mod_eq_zero]
    exact (PrimrecPred.computablePred hd).not
  exact Computable.find hP col_exists

/-- **The exact tail count.** -/
theorem card_tail (K N : ℕ) :
    ((Finset.range N).filter (fun n => 2 ^ K ∣ (n + 1))).card = N / 2 ^ K := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Nat.succ_div]
    by_cases h : 2 ^ K ∣ (N + 1)
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih, if_pos h]
    · rw [if_neg h, ih, if_neg h, add_zero]

/-- **A set meeting every column in a bounded set has density zero.** -/
theorem densityZero_of_bounded_columns {E : Set ℕ}
    (h : ∀ k, ∃ M, ∀ n ∈ E, col n = k → n < M) : DensityZero E := by
  -- a uniform bound for the columns below `K`
  have hbdd : ∀ K, ∃ M, ∀ n ∈ E, col n < K → n < M := by
    intro K
    induction K with
    | zero => exact ⟨0, by intro n _ hlt; omega⟩
    | succ K ih =>
      obtain ⟨M₁, hM₁⟩ := ih
      obtain ⟨M₂, hM₂⟩ := h K
      refine ⟨max M₁ M₂, fun n hn hlt => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
      · exact lt_of_lt_of_le (hM₁ n hn hlt') (le_max_left _ _)
      · exact lt_of_lt_of_le (hM₂ n hn heq) (le_max_right _ _)
  rw [DensityZero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 / ε) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨M, hM⟩ := hbdd K
  refine ⟨max 1 (Nat.ceil (2 * (M:ℝ) / ε) + 1), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  -- the counting split
  have hsplit : count E N ≤ M + N / 2 ^ K := by
    have hsub : (Finset.range N).filter (· ∈ E) ⊆
        ((Finset.range N).filter (fun n => n < M)) ∪
          ((Finset.range N).filter (fun n => 2 ^ K ∣ (n + 1))) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      by_cases hc : col n < K
      · exact Or.inl ⟨hn.1, hM n hn.2 hc⟩
      · exact Or.inr ⟨hn.1, pow_dvd_iff_le_col.mpr (by omega)⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((Finset.range N).filter (fun n => n < M))
      ((Finset.range N).filter (fun n => 2 ^ K ∣ (n + 1)))
    have h3 : ((Finset.range N).filter (fun n => n < M)).card ≤ M := by
      refine le_trans (Finset.card_le_card (fun x hx => ?_)) (by simp : (Finset.range M).card ≤ M)
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact hx.2
    rw [card_tail] at h2
    unfold count
    omega
  -- the estimate
  have hcast : ((count E N : ℝ)) ≤ (M : ℝ) + (N : ℝ) / 2 ^ K := by
    have hdiv : ((N / 2 ^ K : ℕ) : ℝ) ≤ (N : ℝ) / 2 ^ K := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 ^ K)]
      have := Nat.div_mul_le_self N (2 ^ K)
      calc ((N / 2 ^ K : ℕ) : ℝ) * 2 ^ K = (((N / 2 ^ K) * 2 ^ K : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (N : ℝ) := by exact_mod_cast this
    have : ((count E N : ℝ)) ≤ (M : ℝ) + ((N / 2 ^ K : ℕ) : ℝ) := by exact_mod_cast hsplit
    linarith
  have hMN : (M : ℝ) < (N : ℝ) * (ε / 2) := by
    have h1 : (Nat.ceil (2 * (M:ℝ) / ε) : ℝ) + 1 ≤ N := by
      have : (Nat.ceil (2 * (M:ℝ) / ε) + 1 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast this
    have h2 : 2 * (M : ℝ) / ε ≤ Nat.ceil (2 * (M:ℝ) / ε) := Nat.le_ceil _
    have h3 : 2 * (M : ℝ) / ε < N := by linarith
    rw [div_lt_iff₀ hε] at h3
    linarith
  have hpow : (N : ℝ) / 2 ^ K < (N : ℝ) * (ε / 2) := by
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    rw [div_lt_iff₀ h2K]
    have hKa : 2 / ε < 2 ^ K := hK
    rw [div_lt_iff₀ hε] at hKa
    nlinarith
  have hfinal : (count E N : ℝ) / N < ε := by
    rw [div_lt_iff₀ hNpos]
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hfinal

end CoarseDegrees
