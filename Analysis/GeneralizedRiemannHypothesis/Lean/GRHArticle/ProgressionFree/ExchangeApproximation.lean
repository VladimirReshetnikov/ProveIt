import GRHArticle.ProgressionFree.DensityBounds
import GRHArticle.ProgressionFree.DigitPatternDensity
import Mathlib.NumberTheory.PrimeCounting

/-!
# Uniform approximation of one-digit rules

The rules share the same high digits at the affected primes and the same
Rankin constraints outside those primes. This gives a uniform counting-error
estimate for any choice of the ternary cap.
-/

open Filter
open scoped BigOperators Topology

namespace GRHArticle.ProgressionFree

def exchangeAffected (marker : ℕ) (S : Finset ℕ) (o : Option ↥S) : ℕ :=
  o.elim marker Subtype.val

def exchangeRough (marker : ℕ) (S : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  Nat.primesLE Y \ insert marker S

private theorem affected_mem (marker : ℕ) (S : Finset ℕ) (o : Option ↥S) :
    exchangeAffected marker S o = marker ∨ exchangeAffected marker S o ∈ S := by
  cases o with
  | none => exact Or.inl rfl
  | some p => exact Or.inr p.property

theorem exchangeAffected_prime {marker : ℕ} {S : Finset ℕ}
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (o : Option ↥S) :
    (exchangeAffected marker S o).Prime := by
  cases o with
  | none => exact hm
  | some p => exact hS p.val p.property

private theorem exchangeAffected_injective {marker : ℕ} {S : Finset ℕ}
    (hm : marker ∉ S) : Function.Injective (exchangeAffected marker S) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      change marker = b.val at hab
      exact (hm (hab.symm ▸ b.property)).elim
  | some a =>
    cases b with
    | none =>
      change a.val = marker at hab
      exact (hm (hab ▸ a.property)).elim
    | some b => exact congrArg some (Subtype.ext hab)

theorem exchangeRough_prime {marker Y : ℕ} {S : Finset ℕ}
    (q : ↥(exchangeRough marker S Y)) : q.val.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp q.property).1

theorem exchangePrimeCoordinates_injective {marker Y : ℕ} {S : Finset ℕ}
    (hm : marker ∉ S) :
    Function.Injective (Sum.elim (exchangeAffected marker S)
      (Subtype.val : ↥(exchangeRough marker S Y) → ℕ)) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (exchangeAffected_injective hm hab)
    | inr b =>
      change exchangeAffected marker S a = b.val at hab
      exact ((Finset.mem_sdiff.mp b.property).2
        (Finset.mem_insert.mpr (hab ▸ affected_mem marker S a))).elim
  | inr a =>
    cases b with
    | inl b =>
      change a.val = exchangeAffected marker S b at hab
      exact ((Finset.mem_sdiff.mp a.property).2
        (Finset.mem_insert.mpr (hab.symm ▸ affected_mem marker S b))).elim
    | inr b => exact congrArg Sum.inr (Subtype.ext hab)

/-- Positive integers with the specified affected residue cap and the Rankin
rule on all of the remaining ternary digits. -/
def digitRuleSet (marker : ℕ) (S : Finset ℕ) (C : Set (ZMod 3 × (↥S → ZMod 3))) : Set ℕ :=
  {n | n ≠ 0 ∧ digitVectorOf (fun o => n.factorization (exchangeAffected marker S o)) ∈ C ∧
    ∀ p : ℕ, p.Prime →
      if p = marker ∨ p ∈ S then n.factorization p / 3 ∈ greedyExponents
      else n.factorization p ∈ greedyExponents}

theorem digitRuleSet_exchanged (marker : ℕ) (S : Finset ℕ) :
    digitRuleSet marker S (exchangedDigitCap ↥S) = exchangedRankinSet marker S := rfl

private theorem binary_cast_iff (n : ℕ) :
    ((n : ZMod 3) = 0 ∨ (n : ZMod 3) = 1) ↔ n % 3 ≤ 1 := by
  have h₀ : (0 : ZMod 3).val = 0 := by decide
  have h₁ : (1 : ZMod 3).val = 1 := by decide
  constructor
  · rintro (h | h)
    · have hval := congrArg ZMod.val h
      rw [ZMod.val_natCast, h₀] at hval
      omega
    · have hval := congrArg ZMod.val h
      rw [ZMod.val_natCast, h₁] at hval
      omega
  · intro h
    have hv : n % 3 = 0 ∨ n % 3 = 1 := by omega
    rcases hv with h | h
    · exact Or.inl (ZMod.val_injective 3 (by rw [ZMod.val_natCast, h₀, h]))
    · exact Or.inr (ZMod.val_injective 3 (by rw [ZMod.val_natCast, h₁, h]))

/-- The original Rankin rule is the binary-cap member of the same family. -/
theorem digitRuleSet_binary {marker : ℕ} {S : Finset ℕ}
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) :
    digitRuleSet marker S (binaryDigitCap ↥S) = rankinSet := by
  ext n
  constructor
  · rintro ⟨hn, hcap, hrest⟩
    refine ⟨hn, fun p hp => ?_⟩
    by_cases hsel : p = marker ∨ p ∈ S
    · have hquo : n.factorization p / 3 ∈ greedyExponents := by
        simpa only [if_pos hsel] using hrest p hp
      apply (mem_greedyExponents_iff _).mpr
      refine ⟨?_, hquo⟩
      rcases hsel with rfl | hp
      · exact (binary_cast_iff _).mp hcap.1
      · exact (binary_cast_iff _).mp (hcap.2 ⟨p, hp⟩)
    · simpa only [if_neg hsel] using hrest p hp
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_, ?_⟩
    · exact ⟨(binary_cast_iff _).mpr ((mem_greedyExponents_iff _).mp (h marker hm)).1,
        fun p => (binary_cast_iff _).mpr
          ((mem_greedyExponents_iff _).mp (h p.val (hS p.val p.property))).1⟩
    · intro p hp
      by_cases hsel : p = marker ∨ p ∈ S
      · simpa only [if_pos hsel] using ((mem_greedyExponents_iff _).mp (h p hp)).2
      · simpa only [if_neg hsel] using h p hp

private theorem two_le_of_not_greedy {k : ℕ} (hk : k ∉ greedyExponents) : 2 ≤ k := by
  by_contra h
  have hsmall : k = 0 ∨ k = 1 := by omega
  rcases hsmall with rfl | rfl
  · exact hk zero_mem_greedyExponents
  · exact hk one_mem_greedyExponents

private theorem digitRule_errorEvent {marker Y L : ℕ} {S : Finset ℕ}
    (C : Set (ZMod 3 × (↥S → ZMod 3)))
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hmY : marker ≤ Y) (hSY : ∀ p ∈ S, p ≤ Y) :
    let T := finiteDigitRuleSet (exchangeAffected marker S) (Subtype.val :
      ↥(exchangeRough marker S Y) → ℕ) C L
    (digitRuleSet marker S C \ T) ∪ (T \ digitRuleSet marker S C) ⊆
      {n | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p ^ 2 ∣ n} ∪ {n | ∃ p ∈ Nat.primesLE Y, p ^ (3 * L) ∣ n} := by
  intro T n hn
  rcases hn with h | h
  · obtain ⟨hd, ht⟩ := h
    apply Or.inr
    by_contra hlarge
    have hsmall (p : ℕ) (hp : p ∈ Nat.primesLE Y) : n.factorization p < 3 * L := by
      by_contra h
      exact hlarge ⟨p, hp, ((Nat.prime_of_mem_primesLE hp).pow_dvd_iff_le_factorization hd.1).mpr
        (Nat.le_of_not_gt h)⟩
    apply ht
    refine ⟨hd.1, hd.2.1, ?_, ?_⟩
    · intro o
      have ho := affected_mem marker S o
      have hp := exchangeAffected_prime hm hS o
      have hle : exchangeAffected marker S o ≤ Y := by
        rcases ho with h | h
        · rw [h]
          exact hmY
        · exact hSY _ h
      have ho := affected_mem marker S o
      have hbound := hsmall _ (Nat.mem_primesLE.mpr ⟨hle, hp⟩)
      refine mem_greedyExponentsBelow.mpr ⟨?_, by omega⟩
      simpa only [if_pos ho] using hd.2.2 _ hp
    · intro q
      have hq := Finset.mem_sdiff.mp q.property
      have hnot : ¬(q.val = marker ∨ q.val ∈ S) := fun h => hq.2 (Finset.mem_insert.mpr h)
      refine mem_greedyExponentsBelow.mpr ⟨?_, hsmall _ hq.1⟩
      simpa only [if_neg hnot] using hd.2.2 q.val (exchangeRough_prime q)
  · obtain ⟨ht, hd⟩ := h
    apply Or.inl
    by_contra hlarge
    apply hd
    refine ⟨ht.1, ht.2.1, fun p hp => ?_⟩
    by_cases hsel : p = marker ∨ p ∈ S
    · rw [if_pos hsel]
      rcases hsel with rfl | hmem
      · exact (mem_greedyExponentsBelow.mp (ht.2.2.1 none)).1
      · exact (mem_greedyExponentsBelow.mp (ht.2.2.1 (some ⟨p, hmem⟩))).1
    · rw [if_neg hsel]
      by_cases hle : p ≤ Y
      · have hmem : p ∈ exchangeRough marker S Y := Finset.mem_sdiff.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hle, hp⟩, fun h => hsel (Finset.mem_insert.mp h)⟩
        exact (mem_greedyExponentsBelow.mp (ht.2.2.2 ⟨p, hmem⟩)).1
      · by_contra hnot
        exact hlarge ⟨p, lt_of_not_ge hle, hp, (hp.pow_dvd_iff_le_factorization ht.1).mpr
          (two_le_of_not_greedy hnot)⟩

/-- Uniform counting error of a one-digit rule with prime cutoff `Y` and
exponent cutoff `3L`. -/
theorem abs_densityUpTo_digitRule_sub_trunc_le {marker Y L : ℕ} {S : Finset ℕ}
    (C : Set (ZMod 3 × (↥S → ZMod 3))) (N : ℕ)
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hmY : marker ≤ Y) (hSY : ∀ p ∈ S, p ≤ Y)
    (hY : 0 < Y) :
    |densityUpTo (digitRuleSet marker S C) N - densityUpTo (finiteDigitRuleSet
      (exchangeAffected marker S) (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C L) N| ≤
      1 / (Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ (3 * L) := by
  let E := {n : ℕ | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p ^ 2 ∣ n}
  let F := {n : ℕ | ∃ p ∈ Nat.primesLE Y, p ^ (3 * L) ∣ n}
  calc
    _ ≤ densityUpTo (E ∪ F) N := densityUpTo_abs_sub_le_of_symmDiff_subset N
      (digitRule_errorEvent C hm hS hmY hSY)
    _ ≤ densityUpTo E N + densityUpTo F N := densityUpTo_union_le E F N
    _ ≤ _ := by
      apply add_le_add (densityUpTo_largePrimeSquare_le Y N hY)
      simpa only [F, Nat.cast_pow] using
        densityUpTo_divisibleByOneOf_le (Nat.primesLE Y) (fun p => p ^ (3 * L)) N
          (fun p hp => pow_pos (Nat.prime_of_mem_primesLE hp).pos _)

private theorem tendsto_threePow_prime_tail (Y : ℕ) :
    Tendsto (fun L : ℕ => ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ (3 * L)) atTop (𝓝 0) := by
  have hpow (p : ℕ) (hp : p ∈ Nat.primesLE Y) :
      Tendsto (fun L : ℕ => 1 / (p : ℝ) ^ (3 * L)) atTop (𝓝 0) := by
    have hr : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    have hnon : 0 ≤ 1 / (p : ℝ) := by positivity
    have hu : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ (by linarith only [hr]), one_mul]
      exact hr
    have huc : (1 / (p : ℝ)) ^ 3 < 1 := pow_lt_one₀ hnon hu (by decide)
    simpa only [← pow_mul, one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (pow_nonneg hnon 3) huc
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Nat.primesLE Y) hpow

theorem exists_digitRule_cutoffs (marker : ℕ) (S : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y L : ℕ, 0 < Y ∧ 0 < L ∧ marker ≤ Y ∧ (∀ p ∈ S, p ≤ Y) ∧
      1 / (Y : ℝ) + ∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ (3 * L) ≤ ε := by
  have hε₂ : 0 < ε / 2 := by positivity
  have hYev : ∀ᶠ Y : ℕ in atTop, 1 / (Y : ℝ) < ε / 2 :=
    (tendsto_order.mp tendsto_one_div_atTop_nhds_zero_nat).2 (ε / 2) hε₂
  obtain ⟨Y, hYlarge, hYε⟩ :=
    ((eventually_ge_atTop (max marker (S.sup id) + 1)).and hYev).exists
  have hS (p : ℕ) (hp : p ∈ S) : p ≤ S.sup id := Finset.le_sup (f := id) hp
  have hLε' : ∀ᶠ L : ℕ in atTop, (∑ p ∈ Nat.primesLE Y, 1 / (p : ℝ) ^ (3 * L)) < ε / 2 :=
    (tendsto_order.mp (tendsto_threePow_prime_tail Y)).2 (ε / 2) hε₂
  obtain ⟨L, hL, hLε⟩ := ((eventually_gt_atTop (0 : ℕ)).and hLε').exists
  exact ⟨Y, L, by omega, hL, by omega, fun p hp => by have := hS p hp; omega,
    by linarith only [hYε, hLε]⟩

/-- Every fixed cap rule has a natural density. -/
theorem exists_hasNaturalDensity_digitRuleSet {marker : ℕ} {S : Finset ℕ}
    (C : Set (ZMod 3 × (↥S → ZMod 3)))
    (hm : marker.Prime) (hS : ∀ p ∈ S, p.Prime) (hdisj : marker ∉ S) :
    ∃ d, HasNaturalDensity (digitRuleSet marker S C) d := by
  apply exists_hasNaturalDensity_of_uniform_approximation
  intro ε hε
  obtain ⟨Y, L, hY, _, hmY, hSY, hbound⟩ := exists_digitRule_cutoffs marker S hε
  refine ⟨_, _, hasNaturalDensity_finiteDigitRuleSet (exchangeAffected marker S)
    (Subtype.val : ↥(exchangeRough marker S Y) → ℕ) C L (exchangePrimeCoordinates_injective hdisj)
    (exchangeAffected_prime hm hS) exchangeRough_prime, ?_⟩
  intro N
  exact (abs_densityUpTo_digitRule_sub_trunc_le C N hm hS hmY hSY hY).trans hbound

end GRHArticle.ProgressionFree
