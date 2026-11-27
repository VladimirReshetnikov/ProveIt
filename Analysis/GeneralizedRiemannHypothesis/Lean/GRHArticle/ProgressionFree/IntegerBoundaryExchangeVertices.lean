import GRHArticle.ProgressionFree.IntegerBoundaryExchangeReplacement

/-!
# The finite smooth search domain and its scaled weights
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def powersValue (t : ℕ × ℕ × ℕ) : ℕ :=
  2^t.1 * 3^t.2.1 * 5^t.2.2

/-- The enumerated 5-smooth positive integers through one million. -/
def integerExchangeVertexList : List ℕ :=
  (((List.range 20).product ((List.range 13).product (List.range 9))).map powersValue).filter
    (· ≤ 1000000)

def integerExchangeVertices : Finset ℕ := integerExchangeVertexList.toFinset

private theorem mem_exchangeVertexList {n : ℕ} :
    n ∈ integerExchangeVertexList ↔ ∃ i j k : ℕ,
      i < 20 ∧ j < 13 ∧ k < 9 ∧ 2^i * 3^j * 5^k = n ∧ n ≤ 1000000 := by
  simp only [integerExchangeVertexList, List.mem_filter, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨⟨⟨i,j,k⟩,h,he⟩,hn⟩
    have ⟨hi,hjk⟩ := List.mem_product.mp h
    have ⟨hj,hk⟩ := List.mem_product.mp hjk
    exact ⟨i,j,k,List.mem_range.mp hi,List.mem_range.mp hj,List.mem_range.mp hk,he,hn⟩
  · rintro ⟨i,j,k,hi,hj,hk,he,hn⟩
    exact ⟨⟨(i,j,k), List.mem_product.mpr
      ⟨List.mem_range.mpr hi,List.mem_product.mpr ⟨List.mem_range.mpr hj,List.mem_range.mpr hk⟩⟩,
      he⟩,hn⟩

private theorem smooth_six_eq_powers {n : ℕ} (h : n ∈ Nat.smoothNumbers 6) :
    n = 2^(n.factorization 2) * 3^(n.factorization 3) * 5^(n.factorization 5) := by
  have hs : (n.factorization.support : Finset ℕ) ⊆ {2,3,5} := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpPrime, hpDvd, _⟩ := hp
    have hm := (Nat.mem_primeFactorsList_iff_dvd h.1 hpPrime).mpr hpDvd
    have hp6 := h.2 p hm
    interval_cases p
    · exact ((by decide : ¬ Nat.Prime 0) hpPrime).elim
    · exact ((by decide : ¬ Nat.Prime 1) hpPrime).elim
    · decide
    · decide
    · exact ((by decide : ¬ Nat.Prime 4) hpPrime).elim
    · decide
  calc
    n = ∏ p ∈ n.factorization.support, p^(n.factorization p) :=
      (Nat.prod_factorization_pow_eq_self h.1).symm
    _ = ∏ p ∈ ({2,3,5} : Finset ℕ), p^(n.factorization p) := by
      apply prod_subset hs
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]
    _ = _ := by
      rw [prod_insert (by decide), prod_insert (by decide), prod_singleton, mul_assoc]

private theorem smooth_six_powers (i j k : ℕ) :
    (2^i * 3^j * 5^k : ℕ) ∈ Nat.smoothNumbers 6 := by
  have hpow (p a : ℕ) (hp : p ∈ Nat.smoothNumbers 6) : p^a ∈ Nat.smoothNumbers 6 := by
    induction a with
    | zero =>
      simpa only [pow_zero] using
        (Nat.mem_smoothNumbers_of_lt (m := 1) (n := 6) (by decide) (by decide))
    | succ a ih =>
      rw [pow_succ]
      exact Nat.mul_mem_smoothNumbers ih hp
  exact Nat.mul_mem_smoothNumbers
    (Nat.mul_mem_smoothNumbers (hpow 2 i (Nat.mem_smoothNumbers_of_lt (by decide) (by decide)))
      (hpow 3 j (Nat.mem_smoothNumbers_of_lt (by decide) (by decide))))
    (hpow 5 k (Nat.mem_smoothNumbers_of_lt (by decide) (by decide)))

theorem mem_integerExchangeVertices {n : ℕ} :
    n ∈ integerExchangeVertices ↔ n ∈ Nat.smoothNumbers 6 ∧ n ≤ 1000000 := by
  simp only [integerExchangeVertices, List.mem_toFinset, mem_exchangeVertexList]
  constructor
  · rintro ⟨i,j,k,hi,hj,hk,rfl,hN⟩
    exact ⟨smooth_six_powers i j k, hN⟩
  · rintro ⟨hs, hn⟩
    let i := n.factorization 2
    let j := n.factorization 3
    let k := n.factorization 5
    have he : 2^i * 3^j * 5^k = n := (smooth_six_eq_powers hs).symm
    have h2 : 2^i ≤ n := by
      rw [← he]
      exact (Nat.le_mul_of_pos_right _ (by positivity)).trans (Nat.le_mul_of_pos_right _ (by positivity))
    have h3 : 3^j ≤ n := by
      rw [← he]
      exact (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_mul_of_pos_right _ (by positivity))
    have h5 : 5^k ≤ n := by
      rw [← he]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    refine ⟨i,j,k,?_,?_,?_,he,hn⟩
    · by_contra! hi
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hi
      have hd : 1000000 < (2:ℕ)^20 := by decide
      omega
    · by_contra! hj
      have hh := Nat.pow_le_pow_right (by decide : 0 < 3) hj
      have hd : 1000000 < (3:ℕ)^13 := by decide
      omega
    · by_contra! hk
      have hh := Nat.pow_le_pow_right (by decide : 0 < 5) hk
      have hd : 1000000 < (5:ℕ)^9 := by decide
      omega

theorem integerExchangeReplacement_subset_vertices :
    integerExchangeReplacement ⊆ integerExchangeVertices :=
  fun _ hn ↦ mem_integerExchangeVertices.mpr (integerExchangeReplacement_smooth _ hn)

def integerExchangeBaseScale : ℕ := 108839116800000000

def integerExchangeScale : ℕ := integerExchangeBaseScale * 10000000

def integerExchangeCapacity (n : ℕ) : ℕ :=
  integerExchangeBaseScale / n * (if n ∈ integerExchangeReplacement then 9175659 else 10000000)

/-- The boundary-charged reciprocal weight of a vertex. -/
noncomputable def integerExchangeVertexWeight (n : ℕ) : ℝ :=
  (1 - if n ∈ integerExchangeReplacement then integerExchangeCharge else 0)/(n:ℝ)

private theorem dvd_integerExchangeBaseScale {n : ℕ}
    (hn : n ∈ integerExchangeVertices) : n ∣ integerExchangeBaseScale := by
  simp only [integerExchangeVertices, List.mem_toFinset, mem_exchangeVertexList] at hn
  obtain ⟨i,j,k,hi,hj,hk,rfl,_⟩ := hn
  change 2^i * 3^j * 5^k ∣ 2^19 * 3^12 * 5^8
  exact mul_dvd_mul (mul_dvd_mul (pow_dvd_pow _ (by omega)) (pow_dvd_pow _ (by omega)))
    (pow_dvd_pow _ (by omega))

theorem integerExchangeCapacity_readback {n : ℕ} (hn : n ∈ integerExchangeVertices) :
    (integerExchangeCapacity n : ℝ) / integerExchangeScale = integerExchangeVertexWeight n := by
  have hn₀ : (n:ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_zero_of_mem_smoothNumbers (mem_integerExchangeVertices.mp hn).1)
  have hD : (integerExchangeBaseScale:ℝ) ≠ 0 := by norm_num [integerExchangeBaseScale]
  have hdiv : ((integerExchangeBaseScale/n : ℕ):ℝ) = (integerExchangeBaseScale:ℝ)/n := by
    apply (eq_div_iff hn₀).mpr
    exact_mod_cast Nat.div_mul_cancel (dvd_integerExchangeBaseScale hn)
  unfold integerExchangeCapacity integerExchangeScale integerExchangeVertexWeight integerExchangeCharge
  push_cast
  rw [hdiv]
  split_ifs <;> field_simp <;> ring

private theorem powersValue_injective : Function.Injective powersValue := by
  have hfac (i j k : ℕ) : (2^i * 3^j * 5^k : ℕ).factorization =
      Finsupp.single 2 i + Finsupp.single 3 j + Finsupp.single 5 k := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      (show Nat.Prime 2 by decide).factorization_pow,
      (show Nat.Prime 3 by decide).factorization_pow,
      (show Nat.Prime 5 by decide).factorization_pow]
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  have hh := congrArg Nat.factorization h
  change (2^i * 3^j * 5^k : ℕ).factorization = (2^i' * 3^j' * 5^k' : ℕ).factorization at hh
  rw [hfac, hfac] at hh
  have hi := congrArg (fun f : ℕ →₀ ℕ ↦ f 2) hh
  have hj := congrArg (fun f : ℕ →₀ ℕ ↦ f 3) hh
  have hk := congrArg (fun f : ℕ →₀ ℕ ↦ f 5) hh
  simp at hi hj hk
  simp [hi,hj,hk]

private theorem integerExchangeVertexList_nodup : integerExchangeVertexList.Nodup :=
  ((List.nodup_range.product (List.nodup_range.product List.nodup_range)).map
    powersValue_injective).filter _

theorem integerExchangeVertices_card : integerExchangeVertices.card = 507 := by
  rw [integerExchangeVertices, List.toFinset_card_of_nodup integerExchangeVertexList_nodup]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem integerExchangeVertices_capacity :
    ∑ n ∈ integerExchangeVertices, integerExchangeCapacity n = 3827045130769211139120000 := by
  rw [integerExchangeVertices, List.sum_toFinset _ integerExchangeVertexList_nodup]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem integerExchangeVertices_reciprocal :
    (∑ n ∈ integerExchangeVertices, (n:ℝ)⁻¹) =
      15/4 - (12000753838363:ℝ)/108839116800000000 := by
  have h : (∑ n ∈ integerExchangeVertices, (n:ℚ)⁻¹) =
      15/4 - (12000753838363:ℚ)/108839116800000000 := by
    rw [integerExchangeVertices, List.sum_toFinset _ integerExchangeVertexList_nodup]
    decide +kernel
  have hc := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  push_cast at hc
  exact hc

end GRHArticle.ProgressionFree
