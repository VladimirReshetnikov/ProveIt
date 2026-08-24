import ExponentialIdentities.TwoBaseIntegerExponent.TerminalFactorialIndependence
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Exact top-slice tail-sum rigidity

For a prime `p` with `A < 2p`, the falling factorial `(A)_K = A.descFactorial K` contains
at most one multiple of `p`, namely the factor equal to `p` itself, which occurs exactly
when `p` lies in the window `(A - K, A]`.  Hence `v_p((A)_K) = 1` inside the window and
`0` below it — *exactly*, with no error terms.

Consequently, for a nested family of windows `K 0 < K 1 < ⋯ < K (s-1) ≤ A` (one slice of
the two-parameter factorial family, common top `A`) and a prime `p` in the annulus
between windows `k-1` and `k`, the valuation of the signed product
`∏ l (A)_{K l} ^ (c l)` is exactly the tail sum `∑_{l ≥ k} c l`
(`top_slice_tail_sum`).  If the product is an integer, every such tail sum must be
nonnegative wherever the annulus contains a prime — the exact partial rigidity recorded
in the unified report's session log for the two-parameter transport family.
-/

namespace LeanProofs.TwoBaseIntegerExponent.TopSlice

open Finset

/-- A prime dividing none of the factors divides no finite product. -/
theorem not_dvd_prod {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (h : ∀ i ∈ s, ¬ p ∣ f i) : ¬ p ∣ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.one_lt.ne'  -- p ∣ 1 → p = 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · exact h a (Finset.mem_insert_self a s) h1
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) h1

/-- **Window valuation, exact.**  For `A < 2p` and `p` in the window `(A - K, A]`, the
falling factorial `(A)_K` has `p`-adic valuation exactly one: the unique multiple of `p`
among its factors is the factor `p` itself. -/
theorem padicValNat_descFactorial_eq_one {A K p : ℕ} [hp : Fact p.Prime]
    (hKA : K ≤ A) (hlo : A - K < p) (hhi : p ≤ A) (h2p : A < 2 * p) :
    padicValNat p (A.descFactorial K) = 1 := by
  have hu0 : A - p ∈ range K := Finset.mem_range.mpr (by omega)
  rw [Nat.descFactorial_eq_prod_range, ← Finset.mul_prod_erase _ _ hu0,
    show A - (A - p) = p by omega]
  have hrest : ¬ p ∣ ∏ i ∈ (range K).erase (A - p), (A - i) := by
    apply not_dvd_prod hp.out
    intro i hi hdvd
    obtain ⟨hine, hiK⟩ := Finset.mem_erase.mp hi
    have hiK' : i < K := Finset.mem_range.mp hiK
    obtain ⟨m, hm⟩ := hdvd
    rcases m with _ | m
    · omega
    · rcases m with _ | m
      · omega
      · have hexp : p * (m + 1 + 1) = p * m + 2 * p := by ring
        omega
  have hrest0 : ∏ i ∈ (range K).erase (A - p), (A - i) ≠ 0 := by
    intro h0
    exact hrest (h0 ▸ dvd_zero p)
  rw [padicValNat.mul (Nat.Prime.pos hp.out).ne' hrest0,
    padicValNat.self hp.out.one_lt,
    padicValNat.eq_zero_of_not_dvd hrest]

/-- **Below-window vanishing, exact.**  For `A < 2p` and `p ≤ A - K`, no factor of
`(A)_K` is divisible by `p`. -/
theorem padicValNat_descFactorial_eq_zero {A K p : ℕ} (hp : p.Prime)
    (hKA : K ≤ A) (hbelow : p ≤ A - K) (h2p : A < 2 * p) :
    padicValNat p (A.descFactorial K) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rw [Nat.descFactorial_eq_prod_range]
  apply not_dvd_prod hp
  intro i hi hdvd
  have hiK : i < K := Finset.mem_range.mp hi
  obtain ⟨m, hm⟩ := hdvd
  rcases m with _ | m
  · omega
  · rcases m with _ | m
    · omega
    · have hexp : p * (m + 1 + 1) = p * m + 2 * p := by ring
      omega

/-- **Exact top-slice tail sum.**  For nested windows `K 0 < ⋯ < K (s-1) ≤ A` with a
common top `A` and a prime `p` in the annulus above the windows `l < k` and inside the
windows `l ≥ k` (with `A < 2p`), the `p`-adic valuation of the signed factorial product
is exactly the coefficient tail sum `∑_{l ∈ [k, s)} c l`.  Integrality therefore forces
every realizable tail sum of the top slice to be nonnegative. -/
theorem top_slice_tail_sum {A s k p : ℕ} [hp : Fact p.Prime] {K : ℕ → ℕ} {c : ℕ → ℤ}
    (hks : k < s) (hKA : ∀ l, l < s → K l ≤ A)
    (hKmono : ∀ l m, l < m → m < s → K l < K m)
    (hhi : p ≤ A) (h2p : A < 2 * p)
    (hwin : A - K k < p)
    (hbelow : ∀ l, l < k → p ≤ A - K l) :
    padicValRat p (∏ l ∈ range s, ((A.descFactorial (K l) : ℚ)) ^ (c l))
      = ∑ l ∈ Finset.Ico k s, c l := by
  have hpos : ∀ l, l < s → 0 < A.descFactorial (K l) := fun l hl =>
    Nat.descFactorial_pos.mpr (hKA l hl)
  have hne : ∀ l ∈ range s, ((A.descFactorial (K l) : ℚ)) ^ (c l) ≠ 0 := by
    intro l hl
    exact zpow_ne_zero _ (by exact_mod_cast (hpos l (Finset.mem_range.mp hl)).ne')
  rw [LeanProofs.TwoBaseIntegerExponent.TerminalFactorial.padicValRat_prod _ _ hne]
  have hterm : ∀ l ∈ range s,
      padicValRat p (((A.descFactorial (K l) : ℚ)) ^ (c l))
        = if k ≤ l then c l else 0 := by
    intro l hl
    have hls : l < s := Finset.mem_range.mp hl
    rw [padicValRat.zpow]
    rcases Nat.lt_or_ge l k with hlk | hlk
    · rw [if_neg (by omega)]
      have h0 : padicValNat p (A.descFactorial (K l)) = 0 :=
        padicValNat_descFactorial_eq_zero hp.out (hKA l hls) (hbelow l hlk) h2p
      have : padicValRat p ((A.descFactorial (K l) : ℚ)) = 0 := by
        rw [padicValRat.of_nat, h0]
        norm_num
      rw [this, mul_zero]
    · rw [if_pos hlk]
      have hwl : A - K l < p := by
        rcases Nat.eq_or_lt_of_le hlk with heq | hlt
        · rw [← heq]; exact hwin
        · have := hKmono k l hlt hls
          omega
      have h1 : padicValNat p (A.descFactorial (K l)) = 1 :=
        padicValNat_descFactorial_eq_one (hKA l hls) hwl hhi h2p
      have : padicValRat p ((A.descFactorial (K l) : ℚ)) = 1 := by
        rw [padicValRat.of_nat, h1]
        norm_num
      rw [this, mul_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

end LeanProofs.TwoBaseIntegerExponent.TopSlice
