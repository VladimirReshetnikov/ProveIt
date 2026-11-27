import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

/-!
# Strassmann's theorem for series on a closed unit ball

The coefficient sequences here tend to zero. Evaluation and division are
defined by convergent sums in a complete ultrametric normed field.
-/

open Filter Topology
open scoped BigOperators

namespace GRHArticle.SingularModuli

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Evaluate a coefficient series at a point of the closed unit ball. -/
noncomputable def seriesValue (a : ℕ → K) (x : K) : K :=
  ∑' n : ℕ, a n * x ^ n

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_term_le {x : K} (hx : ‖x‖ ≤ 1) (c : K) (n : ℕ) :
    ‖c * x ^ n‖ ≤ ‖c‖ := by
  rw [norm_mul, norm_pow]
  have h := pow_le_one₀ (n := n) (norm_nonneg x) hx
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (norm_nonneg c)

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem tendsto_tail {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ a (m + n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.add_comm] using ha.comp (tendsto_add_atTop_nat m)

/-- Coefficients tending to zero give a summable evaluation series on the entire closed unit ball. -/
theorem summable_seriesTerms {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {x : K}
    (hx : ‖x‖ ≤ 1) : Summable (fun n : ℕ ↦ a n * x ^ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, NormedAddCommGroup.tendsto_atTop]
  rw [NormedAddCommGroup.tendsto_atTop] at ha
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa only [sub_zero] using (norm_term_le hx (a n) n).trans_lt (by simpa using hN n hn)

omit [CompleteSpace K] in
private theorem norm_tsum_lt_of_forall_lt {u : ℕ → K} (hu : Summable u) {C : ℝ} (hC : 0 < C)
    (h : ∀ j, ‖u j‖ < C) : ‖∑' j, u j‖ < C := by
  have hlim : (∑' j, u j) ∈ Metric.ball (0 : K) C := by
    refine (IsUltrametricDist.isClosed_ball 0 C).mem_of_tendsto hu.hasSum
      (Eventually.of_forall fun s ↦ ?_)
    let B := IsUltrametricDist.ball_openAddSubgroup K hC
    change ∑ j ∈ s, u j ∈ B
    exact B.toAddSubgroup.sum_mem fun j _ ↦ by
      change u j ∈ Metric.ball (0 : K) C
      simpa only [Metric.mem_ball, dist_zero_right] using h j
  simpa only [Metric.mem_ball, dist_zero_right] using hlim

private theorem seriesValue_split {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {x : K}
    (hx : ‖x‖ ≤ 1) :
    seriesValue a x = a 0 + x * seriesValue (fun n ↦ a (n + 1)) x := by
  have hsucc (n : ℕ) : a (n + 1) * x ^ (n + 1) = x * (a (n + 1) * x ^ n) := by
    rw [pow_succ]
    ring
  simpa only [seriesValue, Finset.sum_range_one, pow_zero, mul_one, hsucc, tsum_mul_left] using
    ((summable_seriesTerms ha hx).sum_add_tsum_nat_add 1).symm

/-- The coefficients obtained by dividing by `X - r`, with remainder `seriesValue a r`. -/
noncomputable def linearQuotient (a : ℕ → K) (r : K) (n : ℕ) : K :=
  seriesValue (fun k ↦ a (n + 1 + k)) r

omit [CompleteSpace K] in
theorem tendsto_linearQuotient {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {r : K}
    (hr : ‖r‖ ≤ 1) : Tendsto (linearQuotient a r) atTop (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_atTop] at ha ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  simp only [sub_zero, linearQuotient, seriesValue]
  refine (IsUltrametricDist.norm_tsum_le_of_forall_le ?_).trans_lt (half_lt_self hε)
  intro k
  exact (norm_term_le hr (a (n + 1 + k)) k).trans (by simpa using (hN _ (by omega)).le)

private theorem linearQuotient_split {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {r : K}
    (hr : ‖r‖ ≤ 1) (n : ℕ) :
    linearQuotient a r n = a (n + 1) + r * linearQuotient a r (n + 1) := by
  unfold linearQuotient
  rw [seriesValue_split (tendsto_tail ha (n + 1)) hr]
  simp only [Nat.add_left_comm, Nat.add_comm]

/-- Division by a linear factor with exact remainder, evaluated on the closed unit ball. -/
theorem seriesValue_divide_linear {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {r x : K}
    (hr : ‖r‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    seriesValue a x = seriesValue a r + (x - r) * seriesValue (linearQuotient a r) x := by
  let b := linearQuotient a r
  have hb := tendsto_linearQuotient ha hr
  have hb₁ : Tendsto (fun n : ℕ ↦ b (n + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hb
  have hterms : (fun n : ℕ ↦ a (n + 1) * x ^ n) =
      (fun n : ℕ ↦ b n * x ^ n - r * (b (n + 1) * x ^ n)) := by
    funext n
    rw [show b n = a (n + 1) + r * b (n + 1) from linearQuotient_split ha hr n]
    ring
  have hshift : seriesValue (fun n ↦ a (n + 1)) x =
      seriesValue b x - r * seriesValue (fun n ↦ b (n + 1)) x := by
    simp only [seriesValue]
    rw [hterms, Summable.tsum_sub (summable_seriesTerms hb hx)
      (Summable.mul_left r (summable_seriesTerms hb₁ hx)), tsum_mul_left]
  have hroot : seriesValue a r = a 0 + r * b 0 := by
    simpa only [b, linearQuotient, Nat.zero_add, Nat.add_comm 1] using seriesValue_split ha hr
  change seriesValue a x = seriesValue a r + (x - r) * seriesValue b x
  rw [seriesValue_split ha hx, hshift, hroot, seriesValue_split hb hx]
  ring

/-- The norm at index `n` is positive, maximal, and strictly greater than every later norm. -/
structure LastMaximalIndex (a : ℕ → K) (n : ℕ) : Prop where
  norm_pos : 0 < ‖a n‖
  norm_le : ∀ k, ‖a k‖ ≤ ‖a n‖
  norm_lt : ∀ ⦃k⦄, n < k → ‖a k‖ < ‖a n‖

omit [CompleteSpace K] in
private theorem norm_linearQuotient_le {a : ℕ → K} {r : K} (hr : ‖r‖ ≤ 1) {n : ℕ}
    {C : ℝ} (h : ∀ k, ‖a (n + 1 + k)‖ ≤ C) : ‖linearQuotient a r n‖ ≤ C :=
  IsUltrametricDist.norm_tsum_le_of_forall_le fun k ↦
    (norm_term_le hr (a (n + 1 + k)) k).trans (h k)

private theorem norm_linearQuotient_lt {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {r : K}
    (hr : ‖r‖ ≤ 1) {n : ℕ} {C : ℝ} (hC : 0 < C) (h : ∀ k, ‖a (n + 1 + k)‖ < C) :
    ‖linearQuotient a r n‖ < C :=
  norm_tsum_lt_of_forall_lt (summable_seriesTerms (tendsto_tail ha (n + 1)) hr) hC
    (fun k ↦ (norm_term_le hr (a (n + 1 + k)) k).trans_lt (h k))

/-- The analytic quotient lowers the last maximal index by one. -/
theorem linearQuotient_lastMaximalIndex {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {r : K}
    (hr : ‖r‖ ≤ 1) {m : ℕ} (hm : LastMaximalIndex a (m + 1)) :
    LastMaximalIndex (linearQuotient a r) m := by
  have hlt (n : ℕ) (hn : m < n) : ‖linearQuotient a r n‖ < ‖a (m + 1)‖ :=
    norm_linearQuotient_lt ha hr hm.norm_pos (fun k ↦ hm.norm_lt (by omega))
  have hsmall : ‖r * linearQuotient a r (m + 1)‖ < ‖a (m + 1)‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr).trans_lt (hlt _ (by omega))
  have heq : ‖linearQuotient a r m‖ = ‖a (m + 1)‖ := by
    rw [linearQuotient_split ha hr m, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne',
      max_eq_left hsmall.le]
  refine ⟨by simpa only [heq] using hm.norm_pos, ?_, ?_⟩
  · intro n
    rw [heq]
    exact norm_linearQuotient_le hr (fun k ↦ hm.norm_le (n + 1 + k))
  · intro n hn
    rw [heq]
    exact hlt n hn

private theorem seriesValue_ne_zero_of_lastMaximalIndex_zero {a : ℕ → K}
    (ha : Tendsto a atTop (𝓝 0)) (h0 : LastMaximalIndex a 0) {x : K} (hx : ‖x‖ ≤ 1) :
    seriesValue a x ≠ 0 := by
  have hlt : ‖linearQuotient a x 0‖ < ‖a 0‖ :=
    norm_linearQuotient_lt ha hx h0.norm_pos (fun k ↦ h0.norm_lt (by omega))
  have hsmall : ‖x * linearQuotient a x 0‖ < ‖a 0‖ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hlt
  have hsplit : seriesValue a x = a 0 + x * linearQuotient a x 0 := by
    simpa only [linearQuotient, Nat.zero_add, Nat.add_comm 1] using seriesValue_split ha hx
  apply norm_pos_iff.mp
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsmall.ne', max_eq_left hsmall.le]
  exact h0.norm_pos

/-- Strassmann's bound on the number of distinct roots in the closed unit ball. -/
theorem card_seriesRoots_le_lastMaximalIndex {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0))
    {m : ℕ} (hm : LastMaximalIndex a m) (roots : Finset K)
    (hroots : ∀ x ∈ roots, ‖x‖ ≤ 1 ∧ seriesValue a x = 0) : roots.card ≤ m := by
  classical
  induction m generalizing a roots with
  | zero =>
      have h : roots = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦
        seriesValue_ne_zero_of_lastMaximalIndex_zero ha hm (hroots x hx).1 (hroots x hx).2
      simp [h]
  | succ m ih =>
      rcases roots.eq_empty_or_nonempty with h | ⟨r, hr⟩
      · simp [h]
      have hroot := hroots r hr
      have hrest : ∀ x ∈ roots.erase r,
          ‖x‖ ≤ 1 ∧ seriesValue (linearQuotient a r) x = 0 := by
        intro x hx
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
        obtain ⟨hxnorm, hxroot⟩ := hroots x hmem
        have hzero : (x - r) * seriesValue (linearQuotient a r) x = 0 := by
          simpa only [hroot.2, zero_add] using
            (seriesValue_divide_linear ha hroot.1 hxnorm).symm.trans hxroot
        exact ⟨hxnorm, (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)⟩
      have hcount := ih (tendsto_linearQuotient ha hroot.1)
        (linearQuotient_lastMaximalIndex ha hroot.1 hm) (roots.erase r) hrest
      rw [Finset.card_erase_of_mem hr] at hcount
      omega

/-- Extended cardinal form of Strassmann, including finiteness of the full root set. -/
theorem encard_seriesRoots_le_lastMaximalIndex {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0))
    {m : ℕ} (hm : LastMaximalIndex a m) :
    {x : K | ‖x‖ ≤ 1 ∧ seriesValue a x = 0}.encard ≤ m := by
  let Z : Set K := {x : K | ‖x‖ ≤ 1 ∧ seriesValue a x = 0}
  change Z.encard ≤ m
  apply le_of_not_gt
  intro h
  have hsucc : ((m + 1 : ℕ) : ℕ∞) ≤ Z.encard := by
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.coe_add_one_le_iff.mpr h
  obtain ⟨S, hSZ, hS⟩ := Set.exists_subset_encard_eq hsucc
  have hSf := Set.finite_of_encard_eq_coe hS
  have hcount := card_seriesRoots_le_lastMaximalIndex ha hm hSf.toFinset (fun x hx ↦
    hSZ (hSf.mem_toFinset.mp hx))
  rw [hSf.encard_eq_coe_toFinset_card] at hS
  have heq : hSf.toFinset.card = m + 1 := by exact_mod_cast hS
  omega

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- If every coefficient beyond `N` has norm below that of one nonzero coefficient
in the prefix, the last maximal index lies within that prefix. -/
theorem exists_lastMaximalIndex_of_cutoff {a : ℕ → K} {i N : ℕ}
    (hi : i ≤ N) (hpos : 0 < ‖a i‖) (hcut : ∀ ⦃k⦄, N < k → ‖a k‖ < ‖a i‖) :
    ∃ m ≤ N, LastMaximalIndex a m := by
  classical
  let s := Finset.range (N + 1)
  have hi' : i ∈ s := Finset.mem_range.mpr (by omega)
  obtain ⟨j, hj, hmax⟩ := s.exists_mem_eq_sup' ⟨i, hi'⟩ (fun n ↦ ‖a n‖)
  have hle (k : ℕ) (hk : k ∈ s) : ‖a k‖ ≤ ‖a j‖ := by
    rw [← hmax]
    exact Finset.le_sup' (fun n : ℕ ↦ ‖a n‖) hk
  have hlate (k : ℕ) (hk : k ∉ s) : N < k :=
    lt_of_not_ge fun hkn ↦ hk (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
  let t := s.filter (fun k ↦ ‖a k‖ = ‖a j‖)
  have ht : t.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩
  let m := t.max' ht
  obtain ⟨hm, hnorm⟩ := Finset.mem_filter.mp (Finset.max'_mem t ht)
  refine ⟨m, Nat.le_of_lt_succ (Finset.mem_range.mp hm), ?_⟩
  have hpos' : 0 < ‖a m‖ := by rw [hnorm]; exact hpos.trans_le (hle i hi')
  refine ⟨hpos', ?_, ?_⟩
  · intro k
    rw [hnorm]
    by_cases hk : k ∈ s
    · exact hle k hk
    exact (hcut (hlate k hk)).le.trans (hle i hi')
  · intro k hmk
    rw [hnorm]
    by_cases hk : k ∈ s
    · refine lt_of_le_of_ne (hle k hk) ?_
      intro heq
      exact (not_le_of_gt hmk) (Finset.le_max' t k (Finset.mem_filter.mpr ⟨hk, heq⟩))
    exact (hcut (hlate k hk)).trans_le (hle i hi')

/-- Strassmann's bound in the coefficient-cutoff form used for sparse polynomials. -/
theorem encard_seriesRoots_le_of_cutoff {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {i N : ℕ}
    (hi : i ≤ N) (hpos : 0 < ‖a i‖) (hcut : ∀ ⦃k⦄, N < k → ‖a k‖ < ‖a i‖) :
    {x : K | ‖x‖ ≤ 1 ∧ seriesValue a x = 0}.encard ≤ N := by
  obtain ⟨m, hmN, hm⟩ := exists_lastMaximalIndex_of_cutoff hi hpos hcut
  exact (encard_seriesRoots_le_lastMaximalIndex ha hm).trans (by exact_mod_cast hmN)

end GRHArticle.SingularModuli
