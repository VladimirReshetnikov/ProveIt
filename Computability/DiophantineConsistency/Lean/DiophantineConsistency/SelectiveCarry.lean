import DiophantineConsistency.SelectiveQuadraticCoding
import DiophantineConsistency.MultiTargetCarry

/-!
# Carry and packing interfaces for selective quadratic sources

These statements use an arbitrary finite polynomial support span and arbitrary
selected targets. They do not retain the former full-Sidon positions. Numerical
range hypotheses remain explicit, including the bounds needed before any
digit decoding. Full-polynomial evaluation is proved, without truncation.
-/

namespace DiophantineConsistency.SelectiveCarry

open Polynomial Finset Jones1982
open SidonPositions (PairIndex)
open SelectiveQuadraticCoding MultiTargetCarry
open scoped BigOperators

/-- The complete selective quadratic product. -/
noncomputable def rowProduct {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) (E : Fin r → ℕ) : ℤ[X] :=
  encoded w u ^ 2 * combined w s a E

theorem combined_degree_le {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (E : Fin r → ℕ) (D : ℕ)
    (hD : ∀ k p, p ∈ s k → E k - pairWeight w p ≤ D) :
    (combined w s a E).natDegree ≤ D := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [combined, complementary, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro p hp
  have hd := hD k p hp
  exact if_neg (by omega)

/-- Every coefficient outside the actual product span is zero. -/
theorem coeff_rowProduct_eq_zero {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) (E : Fin r → ℕ) (W D : ℕ)
    (hw : ∀ i, w i ≤ W)
    (hD : ∀ k p, p ∈ s k → E k - pairWeight w p ≤ D)
    {n : ℕ} (hn : D + 2 * W < n) : (rowProduct w s a u E).coeff n = 0 := by
  classical
  rw [rowProduct, combined, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k _
  rw [complementary, Finset.mul_sum]
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [encoded_square]
  simp only [Finset.sum_mul, finsetSum_coeff, monomial_mul_monomial]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hi := hw i
  have hj := hw j
  have hd := hD k p hp
  rw [coeff_monomial, if_neg (by omega)]

theorem rowProduct_degree_lt {m r : ℕ} (w : Fin (m + 1) → ℕ)
    (s : Fin r → Finset (PairIndex m)) (a : Fin r → PairIndex m → ℤ)
    (u : Fin (m + 1) → ℤ) (E : Fin r → ℕ) (W D : ℕ)
    (hw : ∀ i, w i ≤ W)
    (hD : ∀ k p, p ∈ s k → E k - pairWeight w p ≤ D) :
    (rowProduct w s a u E).natDegree < D + 2 * W + 1 := by
  have h : (rowProduct w s a u E).natDegree ≤ D + 2 * W := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact coeff_rowProduct_eq_zero w s a u E W D hw hD hn
  omega

/-- The digit word is the full polynomial value plus the geometric bias. -/
theorem doubled_shifted_polynomial_cast (p : ℤ[X]) {t n : ℕ} (ht : 1 ≤ t)
    (hd : p.natDegree < n) (hb : ∀ i < n, |p.coeff i| < 2 ^ (t - 1)) :
    ((2 * shiftedValue t n p.coeff : ℕ) : ℤ) =
      2 * p.eval (2 ^ t) + (2 ^ t : ℤ) * ∑ i ∈ range n, (2 ^ t : ℤ) ^ i := by
  push_cast
  rw [shiftedValue_cast t n p.coeff hb]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← eval_eq_sum_range' hd]
  have hpow : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  ring

theorem shiftedValue_lt {t n : ℕ} (ht : 1 ≤ t) (h : ℕ → ℤ)
    (hb : ∀ i < n, |h i| < 2 ^ (t - 1)) : shiftedValue t n h < (2 ^ t) ^ n := by
  have hbase : 1 < 2 ^ t := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) ht
    norm_num at hp
    omega
  rw [shiftedValue]
  have hd : ∀ x ∈ (List.range n).map (fun i => (h i + 2 ^ (t - 1)).toNat), x < 2 ^ t := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    have hpos : 0 ≤ h i + 2 ^ (t - 1) := by
      have := (abs_lt.mp (hb i hi')).1
      linarith
    rw [Int.toNat_lt hpos]
    have hpow : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    push_cast
    have := (abs_lt.mp (hb i hi')).2
    linarith
  simpa using Nat.ofDigits_lt_base_pow_length hbase hd

theorem selectedMask_lt {t n : ℕ} (ht : 1 ≤ t) (positions : Finset ℕ) :
    selectedMask t n positions < (2 ^ t) ^ n := by
  have hbase : 1 < 2 ^ t := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) ht
    norm_num at hp
    omega
  rw [selectedMask]
  apply (Nat.ofDigits_lt_base_pow_length hbase ?_).trans_le (by simp)
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  have hhalf : 2 ^ (t - 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2 ^ (t - 1) := by positivity
  split <;> omega

/-- The literal high word and mask fit inside the article's `4 B^n` block. -/
theorem doubled_blocks_lt {t n : ℕ} (ht : 1 ≤ t) (positions : Finset ℕ)
    (h : ℕ → ℤ) (hb : ∀ i < n, |h i| < 2 ^ (t - 1)) :
    2 * shiftedValue t n h < 4 * (2 ^ t) ^ n ∧
      2 * selectedMask t n positions < 4 * (2 ^ t) ^ n := by
  have hs := shiftedValue_lt ht h hb
  have hm := selectedMask_lt (n := n) ht positions
  have hp : 0 < (2 ^ t) ^ n := by positivity
  omega

/-- The selected targets recover each separate residual, without row cancellation. -/
theorem tau_selected_rows_iff {r t n : ℕ} (ht : 1 ≤ t)
    (p : ℤ[X]) (E : Fin r → ℕ) (values : Fin r → ℤ)
    (hE : ∀ k, E k < n) (hc : ∀ k, p.coeff (E k) = 2 * values k)
    (hb : ∀ i < n, |p.coeff i| < 2 ^ (t - 1)) :
    τ 2 (2 * shiftedValue t n p.coeff)
      (2 * selectedMask t n (univ.image E)) = 0 ↔ ∀ k, values k = 0 := by
  rw [tau_doubled_selected_iff ht (univ.image E)
    (fun i hi => by obtain ⟨k, _, rfl⟩ := mem_image.mp hi; exact hE k) p.coeff hb]
  constructor
  · intro h k
    have hk := h (E k) (mem_image.mpr ⟨k, mem_univ _, rfl⟩)
    rw [hc k] at hk
    omega
  · intro h i hi
    obtain ⟨k, _, rfl⟩ := mem_image.mp hi
    rw [hc k, h k, mul_zero]

def packTwo (L a b : ℕ) : ℕ := a + b * L

theorem packTwo_lt {L H a b : ℕ} (ha : a < L) (hb : b < H) : packTwo L a b < L * H := by
  unfold packTwo
  calc a + b * L < L + b * L := Nat.add_lt_add_right ha _
    _ = (b + 1) * L := by ring
    _ ≤ H * L := Nat.mul_le_mul_right _ hb
    _ = L * H := by ring

/-- Binary carry decomposition needs only the two low-digit bounds. -/
theorem tau_packTwo_iff {ell a c : ℕ} (ha : a < 2 ^ ell) (hc : c < 2 ^ ell)
    (b d : ℕ) :
    τ 2 (packTwo (2 ^ ell) a b) (packTwo (2 ^ ell) c d) = 0 ↔
      τ 2 a c = 0 ∧ τ 2 b d = 0 := by
  exact (lemma_2_10 ha hc).symm

/-- Range bounds are proved before applying central-binomial decoding. -/
theorem central_blocks_iff {ell h a b c d : ℕ}
    (ha : a < 2 ^ ell) (hc : c < 2 ^ ell) (hb : b < 2 ^ h) (hd : d < 2 ^ h) :
    (2 ^ (ell + h)) ^ 2 ∣
      (2 * centralCode (2 ^ (ell + h)) (packTwo (2 ^ ell) a b)
        (packTwo (2 ^ ell) c d)).choose
        (centralCode (2 ^ (ell + h)) (packTwo (2 ^ ell) a b)
          (packTwo (2 ^ ell) c d)) ↔ τ 2 a c = 0 ∧ τ 2 b d = 0 := by
  have hs : packTwo (2 ^ ell) a b < 2 ^ (ell + h) := by
    rw [pow_add]
    exact packTwo_lt ha hb
  have ht : packTwo (2 ^ ell) c d < 2 ^ (ell + h) := by
    rw [pow_add]
    exact packTwo_lt hc hd
  exact (lemma_2_16 hs ht rfl).symm.trans (tau_packTwo_iff ha hc b d)

/-- Match the division-free rank polynomial used in package 52. -/
theorem centralCode_factorization {N : ℕ} (hN : 1 ≤ N) (S T : ℕ) :
    (centralCode N S T : ℤ) =
      (N - 1 : ℤ) * (((S : ℤ) + T + 1) * N + T + 1) := by
  have h1 : N ≤ N ^ 2 := by nlinarith
  have h2 : 1 ≤ N ^ 2 := by nlinarith
  rw [centralCode]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
  ring

end DiophantineConsistency.SelectiveCarry
