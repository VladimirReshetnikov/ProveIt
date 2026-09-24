import Mathlib.Tactic

/-!
# Jones 1978, §2: Lemmas 2.1, 2.2 and the Divisor Lemma

* **Lemma 2.1.** For positive integers `u, v` and an integer `w`:
  `u ∣ v ∧ 0 < w ↔ ∃ t ≥ 0, u v w = v + t u`.
* **Lemma 2.2** (Matijasevič). For integers `u ≠ 0`, `v`, `w`:
  `u ∣ v ∧ 0 < w ↔ ∃ t ≥ 0, u²(1 + v²) w = v² + (t + 1) u²`.
* **Divisor Lemma** (Matijasevič). If `s ∣ t₁ ⋯ tₙ` (`n ≥ 1`) then there are `p` and
  `i` with `p ∣ s`, `p ∣ tᵢ` and `s^(1/n) ≤ p`, i.e. `s ≤ pⁿ`.
-/

namespace Jones1978

/-- Lemma 2.1. -/
theorem lemma_2_1 {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (w : ℤ) :
    ((u : ℤ) ∣ v ∧ 0 < w) ↔ ∃ t : ℕ, (u : ℤ) * v * w = v + t * u := by
  constructor
  · rintro ⟨⟨k, hk⟩, hw⟩
    -- u v w - v = v (u w - 1) = u k (u w - 1) ≥ 0
    have hw1 : 1 ≤ w := hw
    have hk0 : 0 ≤ k := by
      have : (0 : ℤ) < u * k := hk ▸ (by exact_mod_cast hv)
      have hu' : (0 : ℤ) < u := by exact_mod_cast hu
      exact nonneg_of_mul_nonneg_right this.le hu'
    refine ⟨(k * (u * w - 1)).toNat, ?_⟩
    have hnn : 0 ≤ k * (u * w - 1) := by
      apply mul_nonneg hk0
      have hu' : (1 : ℤ) ≤ u := by exact_mod_cast hu
      nlinarith
    rw [Int.toNat_of_nonneg hnn, hk]
    ring
  · rintro ⟨t, ht⟩
    have hu' : (0 : ℤ) < u := by exact_mod_cast hu
    have hv' : (0 : ℤ) < v := by exact_mod_cast hv
    constructor
    · have : (u : ℤ) ∣ u * v * w - t * u := ⟨v * w - t, by ring⟩
      rw [show (u : ℤ) * v * w - t * u = v by linarith] at this
      exact this
    · by_contra hw
      push Not at hw
      have h1 : (u : ℤ) * v * w ≤ 0 := by
        have := mul_nonneg hu'.le hv'.le
        nlinarith
      have h2 : (0 : ℤ) ≤ t * u := by positivity
      linarith

/-- Lemma 2.2. -/
theorem lemma_2_2 {u : ℤ} (hu : u ≠ 0) (v w : ℤ) :
    (u ∣ v ∧ 0 < w) ↔ ∃ t : ℕ, u ^ 2 * (1 + v ^ 2) * w = v ^ 2 + (t + 1) * u ^ 2 := by
  have hu2 : 0 < u ^ 2 := by positivity
  constructor
  · rintro ⟨⟨k, hk⟩, hw⟩
    -- u²(1+v²)w - v² - u² = u²(w - 1) + v²(u² w - 1) = u²((w-1) + k²(u² w - 1))
    refine ⟨((w - 1) + k ^ 2 * (u ^ 2 * w - 1)).toNat, ?_⟩
    have hnn : 0 ≤ (w - 1) + k ^ 2 * (u ^ 2 * w - 1) := by
      have h1 : 1 ≤ u ^ 2 := hu2
      have : 0 ≤ u ^ 2 * w - 1 := by nlinarith
      exact add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) this)
    rw [Int.toNat_of_nonneg hnn, hk]
    ring
  · rintro ⟨t, ht⟩
    constructor
    · have : u ^ 2 ∣ v ^ 2 := by
        have : u ^ 2 ∣ u ^ 2 * (1 + v ^ 2) * w - (t + 1) * u ^ 2 :=
          ⟨(1 + v ^ 2) * w - (t + 1), by ring⟩
        rw [show u ^ 2 * (1 + v ^ 2) * w - (t + 1) * u ^ 2 = v ^ 2 by linarith] at this
        exact this
      exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).1 this
    · by_contra hw
      push Not at hw
      have h1 : u ^ 2 * (1 + v ^ 2) * w ≤ 0 := by
        have : 0 ≤ u ^ 2 * (1 + v ^ 2) := by positivity
        nlinarith
      have h2 : 0 < v ^ 2 + (t + 1) * u ^ 2 := by positivity
      linarith

/-- `gcd(s, ∏ tᵢ) ∣ ∏ gcd(s, tᵢ)`. -/
theorem gcd_prod_dvd_prod_gcd (s : ℕ) : ∀ (l : List ℕ), Nat.gcd s l.prod ∣ (l.map (Nat.gcd s)).prod
  | [] => by simp
  | t :: l => by
    simp only [List.prod_cons, List.map_cons]
    exact (gcd_mul_dvd_mul_gcd s t l.prod).trans
      (Nat.mul_dvd_mul_left _ (gcd_prod_dvd_prod_gcd s l))

/-- If every element of a nonempty list satisfies `a ^ N < s`, then `(∏ l)^N < s^length`. -/
theorem prod_pow_lt {s N : ℕ} : ∀ (l : List ℕ), l ≠ [] → (∀ a ∈ l, a ^ N < s) →
    l.prod ^ N < s ^ l.length
  | [], h, _ => absurd rfl h
  | [a], _, h => by simpa using h a (by simp)
  | a :: b :: l, _, h => by
    have ih := prod_pow_lt (b :: l) (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    rw [List.prod_cons, mul_pow, List.length_cons, pow_succ']
    exact mul_lt_mul'' ha ih (Nat.zero_le _) (Nat.zero_le _)

/-- If `s ≤ ∏ aᵢ` over a nonempty list, some `aᵢ` satisfies `s ≤ aᵢ ^ length`. -/
theorem exists_le_pow_of_le_prod {s : ℕ} (l : List ℕ) (hl : l ≠ []) (hs : s ≤ l.prod) :
    ∃ a ∈ l, s ≤ a ^ l.length := by
  by_contra hcon
  push Not at hcon
  have h1 := prod_pow_lt l hl hcon
  have h2 := Nat.pow_le_pow_left hs l.length
  omega

/-- The Divisor Lemma (list form): if `s ∣ ∏ l` with `l ≠ []`, then some `t ∈ l` and `p`
satisfy `p ∣ s`, `p ∣ t` and `s ≤ p ^ l.length`. -/
theorem divisor_lemma_list {s : ℕ} (l : List ℕ) (hl : l ≠ []) (hs : s ∣ l.prod) :
    ∃ t ∈ l, ∃ p, p ∣ s ∧ p ∣ t ∧ s ≤ p ^ l.length := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · -- `0 ∣ ∏ l` means some factor is `0`
    have h0 : l.prod = 0 := Nat.eq_zero_of_zero_dvd hs
    have hmem : (0 : ℕ) ∈ l := List.prod_eq_zero_iff.1 h0
    exact ⟨0, hmem, 0, dvd_refl 0, dvd_refl 0, Nat.zero_le _⟩
  have h1 : Nat.gcd s l.prod = s := Nat.gcd_eq_left hs
  have h2 := gcd_prod_dvd_prod_gcd s l
  rw [h1] at h2
  have hle : s ≤ (l.map (Nat.gcd s)).prod := by
    apply Nat.le_of_dvd _ h2
    apply List.prod_pos
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨t, -, rfl⟩ := hg
    exact Nat.gcd_pos_of_pos_left _ hpos
  obtain ⟨g, hg, hsg⟩ := exists_le_pow_of_le_prod (l.map (Nat.gcd s)) (by simpa using hl) hle
  rw [List.mem_map] at hg
  obtain ⟨t, ht, rfl⟩ := hg
  refine ⟨t, ht, Nat.gcd s t, Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _, ?_⟩
  simpa using hsg

theorem list_prod_range (t : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map t).prod = ∏ i ∈ Finset.range n, t i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ, ih]; simp

/-- The Divisor Lemma for `∏_{i < n} t i` with `n ≥ 1`. -/
theorem divisor_lemma {s n : ℕ} (hn : 0 < n) (t : ℕ → ℕ)
    (hs : s ∣ ∏ i ∈ Finset.range n, t i) :
    ∃ i < n, ∃ p, p ∣ s ∧ p ∣ t i ∧ s ≤ p ^ n := by
  have hprod : (List.range n).map t ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  have hs' : s ∣ ((List.range n).map t).prod := by
    rw [list_prod_range]; exact hs
  obtain ⟨u, hu, p, hp1, hp2, hp3⟩ := divisor_lemma_list _ hprod hs'
  rw [List.mem_map] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  rw [List.mem_range] at hi
  refine ⟨i, hi, p, hp1, hp2, ?_⟩
  simpa using hp3

end Jones1978
