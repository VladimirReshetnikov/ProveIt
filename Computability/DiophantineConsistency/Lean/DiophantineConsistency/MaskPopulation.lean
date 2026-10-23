import DiophantineConsistency.LowMaskCoding
import DiophantineConsistency.ReducedRankCarry

/-! # Exact binary populations of the sparse source masks -/

namespace DiophantineConsistency.MaskPopulation

open Jones1982 Finset LowMaskCoding
open scoped BigOperators

theorem population_ofDigits (t : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, x < 2 ^ t) :
    σ 2 (Nat.ofDigits (2 ^ t) L) = (L.map (σ 2)).sum := by
  induction L with
  | nil => simp only [Nat.ofDigits_nil, σ_two_zero, List.map_nil, List.sum_nil]
  | cons a L ih =>
    have ha := hL a (by simp)
    have hl : ∀ x ∈ L, x < 2 ^ t := fun x hx => hL x (by simp [hx])
    rw [Nat.ofDigits_cons]
    have he : a + 2 ^ t * Nat.ofDigits (2 ^ t) L =
        Nat.ofDigits (2 ^ t) L * 2 ^ t + a := by ring
    rw [he, lemma_2_5 ha, ih hl]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem population_pow_sub_pow {k t : ℕ} (hkt : k ≤ t) :
    σ 2 (2 ^ t - 2 ^ k) = t - k := by
  have he : 2 ^ t - 2 ^ k = (2 ^ (t - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hkt]
  rw [he, mul_comm, lemma_2_4_σ, σ_two_pow_sub_one]

private theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem sum_support {S : Finset ℕ} {n : ℕ} (hS : S ⊆ range n) (f : ℕ → ℕ) :
    (∑ j ∈ range n, if j ∈ S then f j else 0) = ∑ j ∈ S, f j := by
  have hf : (range n).filter (fun j => j ∈ S) = S := by
    ext j
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hj => hS hj)
  rw [← Finset.sum_filter, hf]

/-- An additive form avoids hiding either exact subtraction in a mask. -/
theorem low_mask_population {k t n : ℕ} (ht : 1 ≤ t) (hkt : k ≤ t)
    (S : Finset ℕ) (hS : S ⊆ range n) :
    σ 2 (mask (2 ^ t) (2 ^ k) n S) + S.card * k = n * t := by
  have hb : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hbB : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hkt
  have hB : 1 < 2 ^ t := Nat.one_lt_two_pow_iff.mpr (by omega)
  rw [← ofDigits_maskList hb hbB hS,
    population_ofDigits t _ (fun x hx => maskList_lt hb hB.le hx)]
  simp only [maskList, List.map_map]
  rw [sum_map_range]
  have hd (j : ℕ) : σ 2 (maskDigit (2 ^ t) (2 ^ k) S j) +
      (if j ∈ S then k else 0) = t := by
    by_cases hj : j ∈ S
    · simp only [maskDigit, if_pos hj, population_pow_sub_pow hkt]
      omega
    · simp only [maskDigit, if_neg hj, σ_two_pow_sub_one, add_zero]
  have he : (∑ j ∈ range n, (σ 2 (maskDigit (2 ^ t) (2 ^ k) S j) +
      (if j ∈ S then k else 0))) = n * t := by
    simp_rw [hd]
    simp
  rw [Finset.sum_add_distrib, sum_support hS] at he
  simpa using he

def sparseList (d n : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range n).map (fun j => if j ∈ S then d else 0)

theorem ofDigits_sparseList (B d n : ℕ) (S : Finset ℕ) (hS : S ⊆ range n) :
    Nat.ofDigits B (sparseList d n S) = d * ∑ j ∈ S, B ^ j := by
  rw [sparseList, ofDigits_map_range]
  simp_rw [ite_mul, zero_mul]
  rw [sum_support hS, Finset.mul_sum]

theorem sparseList_lt {B d n : ℕ} {S : Finset ℕ} (hd : d < B)
    {x : ℕ} (hx : x ∈ sparseList d n S) : x < B := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  split_ifs <;> omega

def highMask (B : ℕ) (S : Finset ℕ) : ℕ := (B - 2) * ∑ j ∈ S, B ^ j

theorem high_mask_population {t n : ℕ} (ht : 1 ≤ t)
    (S : Finset ℕ) (hS : S ⊆ range n) :
    σ 2 (highMask (2 ^ t) S) = S.card * (t - 1) := by
  have hB : 2 ≤ 2 ^ t := by
    have h := Nat.one_lt_two_pow_iff.mpr (by omega : t ≠ 0)
    omega
  have hd : 2 ^ t - 2 < 2 ^ t := by omega
  rw [highMask, ← ofDigits_sparseList (2 ^ t) (2 ^ t - 2) n S hS,
    population_ofDigits t _ (fun x hx => sparseList_lt hd hx)]
  simp only [sparseList, List.map_map]
  rw [sum_map_range]
  simp only [Function.comp_apply, apply_ite, σ_two_zero]
  rw [sum_support hS]
  have hpop : σ 2 (2 ^ t - 2) = t - 1 := by
    simpa only [pow_one] using population_pow_sub_pow ht
  simp only [hpop, Finset.sum_const, smul_eq_mul]

theorem low_mask_lt {k t n : ℕ} (ht : 1 ≤ t) (hkt : k ≤ t)
    (S : Finset ℕ) (hS : S ⊆ range n) : mask (2 ^ t) (2 ^ k) n S < (2 ^ t) ^ n := by
  have hb : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hbB : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hkt
  have hB : 1 < 2 ^ t := Nat.one_lt_two_pow_iff.mpr (by omega)
  rw [← ofDigits_maskList hb hbB hS]
  simpa only [maskList_length] using Nat.ofDigits_lt_base_pow_length hB
    (fun x hx => maskList_lt hb hB.le hx : ∀ x ∈ maskList (2 ^ t) (2 ^ k) n S, x < 2 ^ t)

def packedMask (B b n : ℕ) (low high : Finset ℕ) : ℕ :=
  highMask B high * B ^ n + mask B b n low

theorem packed_population {k t n highLen : ℕ} (ht : 1 ≤ t) (hkt : k ≤ t)
    (low high : Finset ℕ) (hlow : low ⊆ range n) (hhigh : high ⊆ range highLen) :
    σ 2 (packedMask (2 ^ t) (2 ^ k) n low high) + low.card * k + high.card =
      (n + high.card) * t := by
  have hlowLt := low_mask_lt ht hkt low hlow
  have hpow : (2 ^ t : ℕ) ^ n = 2 ^ (t * n) := by rw [pow_mul]
  rw [hpow] at hlowLt
  have hpop : σ 2 (packedMask (2 ^ t) (2 ^ k) n low high) =
      σ 2 (highMask (2 ^ t) high) + σ 2 (mask (2 ^ t) (2 ^ k) n low) := by
    rw [packedMask, hpow, lemma_2_5 hlowLt]
  have hlo := low_mask_population ht hkt low hlow
  have hhi : σ 2 (highMask (2 ^ t) high) + high.card = high.card * t := by
    rw [high_mask_population ht high hhigh]
    calc
      high.card * (t - 1) + high.card = high.card * (t - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel ht]
  calc
    _ = (σ 2 (mask (2 ^ t) (2 ^ k) n low) + low.card * k) +
        (σ 2 (highMask (2 ^ t) high) + high.card) := by rw [hpop]; omega
    _ = n * t + high.card * t := by rw [hlo, hhi]
    _ = _ := by ring

theorem split116_mask_population {kappa k highLen : ℕ} (hkappa : 2 ≤ kappa)
    (low high : Finset ℕ) (hlow : low ⊆ range 117) (hhigh : high ⊆ range highLen)
    (h31 : low.card = 31) (h22 : high.card = 22) :
    σ 2 (packedMask (2 ^ (kappa + 2 * k)) (2 ^ k) 117 low high) =
      139 * (kappa + 2 * k) - 31 * k - 22 := by
  have h := packed_population (by omega : 1 ≤ kappa + 2 * k)
    (by omega : k ≤ kappa + 2 * k) low high hlow hhigh
  rw [h31, h22] at h
  omega

/-- The calibrated shorter rank now needs no supplied population equation:
the literal source-mask digits determine it. -/
theorem split116_binomial_iff {kappa k highLen S : ℕ} (hkappa : 2 ≤ kappa)
    (low high : Finset ℕ) (hlow : low ⊆ range 117) (hhigh : high ⊆ range highLen)
    (h31 : low.card = 31) (h22 : high.card = 22)
    (hS : S < 2 ^ (k + 2279 * (kappa + 2 * k))) :
    let T := packedMask (2 ^ (kappa + 2 * k)) (2 ^ k) 117 low high
    (2 ^ ((8 * kappa - 11) + k + 1201 * (kappa + 2 * k))) ^ 2 ∣
      (2 * ReducedRankCarry.rank (2 ^ (k + 2279 * (kappa + 2 * k))) S T).choose
        (ReducedRankCarry.rank (2 ^ (k + 2279 * (kappa + 2 * k))) S T) ↔
      τ 2 S T = 0 := by
  apply ReducedRankCarry.split116_calibrated_iff hkappa hS
  exact split116_mask_population hkappa low high hlow hhigh h31 h22

end DiophantineConsistency.MaskPopulation
