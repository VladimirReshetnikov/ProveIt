import New.Derivatives.FormalGroup.ThetaProducts
import New.UpperBound.Size.ShortColumns

/-!
# Near pairs of `b`-places and the losses in the sharpness bound

This file studies places at a prime `p` that does not split in `K = ℚ(√-d)`, their partners, and the
`b`-places among them. A near pair is a `b`-place whose partner at an exponent `e < l₀ / 2` in `I_p`
is a `b`-place; `I_p` is the set of odd numbers, or of all `e ≥ 1` if `p = d`. For non-split `p ≤ k`
the `b`-places are sparse along the powers `(-p) ^ j` with `j < l₀`. For `p = d` there are no near
pairs. Writing `v` for the `p`-adic valuation, the file then bounds the losses in the sharpness
bound: for `p ≤ k` the terms of the sums `R_τ = D.partnerMinSum p τ` not coming from a near pair are
covered by `v(B)` for a product `B` of consecutive integers.

Notions from other files:
* `New.Data P`: the data over the parameters `P = (q₀, d)`, with the size parameters `b`, `x`, `x₁`,
  `k`, the exponent `s` and the group `D.Φ` of infinite places of the field `E`.
* `l₀ = New.l₀ D.towerExp`: the least power of `3` above `27 s`, where `2 ^ s = m ^ 22`.
* `D.bPlaces`, `D.weight`: the set of `b`-places and the weight `κ` of a place, equal to `b` at the
  `b`-places and to `a / x₁` elsewhere, where `a = x b`.
* `D.placeOfInt ν`: the place named by the integer `ν`; the partner of `τ` at the exponent `e` is
  `P.partner D.towerExp p e τ = D.placeOfInt (-p ^ e) * τ`.
* `P.placeClass`: the class of a place modulo a divisor of `q₁ = towerDeg s * q₀`.
* `chiK d`: the character `χ_K = (· / d)`; `p` does not split in `K` if `χ_K(p) ≠ 1`.
* `positivePartnerExponents d p`, `piPrimeValuation d p`, `gammaPrime d p`: the set `I_p`, which is
  empty if `p` splits, and the numbers `v(π_p)` and `γ_p = v(π_p) ∑_{e ∈ I_p} p⁻ᵉ`.

## Main definitions and results

* `New.Data.summable_posPart_sub_weight`: the series in the predicted valuation `S_p` converges.
* `New.Data.notMem_bPlaces_of_two_partners`: sparseness of the `b`-places along the powers of `-p`.
* `New.Data.IsNearPair.exponent_unique`, `New.Data.IsNearPair.eq_and_eq_of_partner_eq`,
  `New.Data.IsNearPair.end_ne_start`: for non-split `p ≤ k` no place occurs twice among the starts
  and ends of near pairs; two pairs that share a place contradict sparseness.
* `New.Data.lossProduct`: a product `B` of `n♯ = ⌈6 b / k⌉` consecutive integers, the last ones up
  to `l` if `n♯ ≤ l`, with `v(n♯!) ≤ v(B)` and `v(l!) ≤ v((l - n♯)₊!) + v(B)`.
* `New.Data.mul_sum_weight_sub_localPrimeSumTotal`: `γ_p |κ| - S_p = v(π_p) ∑ R_τ`, where `|κ|` is
  the sum of the weights.
* `New.Data.partnerMinSum_le`, `New.Data.error_le_padicValNat_lossProduct`: for `p ≤ k` the terms of
  `R_τ` other than that of a near pair are covered by `v(B)`.

## Relation to the literature

Legendre's formula for `v(n!)` is classical.
-/

open Finset Real Nat New.Parameters

namespace New.Data

variable {P : Parameters}

/-! ## Partners of places at a non-split prime

For `p = d` a place and its partner lie in different classes modulo `q₀`. For a non-split `p ≤ k`
the `b`-places are sparse along the powers of `-p`.
-/

/-- If the place `-p ^ e σ` has the same class modulo `q₀` as the place `σ`, then `p` is not the
prime `d` with `K = ℚ(√-d)`. The infinite places of `E` form the group `(ℤ/q₁)ˣ`. -/
lemma ne_d_of_placeClass_eq (D : Data P) {p e : ℕ} {σ : D.Φ}
    (h_class :
      P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp)) (D.placeOfInt (-p ^ e) * σ) =
        P.placeClass (P.q₀.dvd_mul_right (towerDeg D.towerExp)) σ) :
    p ≠ P.d := by
  -- For `p = d` the hypothesis says `-d ^ e = 1` modulo `q₀`, which `d_pow_ne_neg_one` excludes.
  rintro rfl
  have h_coprime_d_q₀ : IsCoprime (P.d : ℤ) P.q₀ :=
    (P.coprime_q₁_d 0).coprime_mul_right.symm.cast
  have h_eq_one : ((-(P.d : ℤ) ^ e : ℤ) : ZMod P.q₀) = 1 := by
    simpa [Units.ext_iff, placeClass_placeOfInt h_coprime_d_q₀.pow_left.neg_left] using h_class
  exact d_pow_ne_neg_one e (by simpa [neg_eq_iff_eq_neg] using h_eq_one)

/-- The series of `(y / p ^ e - κ(-p ^ e σ))⁺` over `e ∈ I_p = positivePartnerExponents P.d p` (the
odd numbers if `p` is inert, all `e ≥ 1` if `p = d`, none if `p` splits) converges; `κ = D.weight`
is the weight of a place. -/
lemma summable_posPart_sub_weight (D : Data P) (p : ℕ) [Fact p.Prime] (y : ℝ) (σ : D.Φ) :
    Summable fun e : ℕ ↦ if e ∈ positivePartnerExponents P.d p then
      (y / p ^ e - D.weight (D.placeOfInt (-p ^ e) * σ))⁺ else 0 := by
  -- Compare with the series of the norms of `y / p ^ e` over the same `e`.
  refine (hasSum_div_pow_positivePartnerExponents P.d p y).summable.norm.of_norm_bounded
    fun e ↦ ?_
  -- The bound at each `e` is `(y / p ^ e - κ)⁺ ≤ |y / p ^ e|`, as `κ ≥ 0`.
  split_ifs
  · rw [Real.norm_of_nonneg (posPart_nonneg _), posPart_def]
    exact sup_le ((sub_le_self _ (cast_nonneg _)).trans (le_norm_self _)) (norm_nonneg _)
  · simp

/-- Sparseness along the powers of `-p`: for a prime `p ≤ k = D.k` that does not split in
`K = ℚ(√-d)`, that is `χ_K(p) = chiK P.d p ≠ 1`, and `0 < i < j < l₀`, the places `σ`, `(-p) ^ i σ`,
`(-p) ^ j σ`, distinct or not, are not all `b`-places. -/
lemma notMem_bPlaces_of_two_partners (D : Data P) {p : ℕ} (hp : p.Prime)
    (h_nonsplit : chiK P.d p ≠ 1)
    (hk : p ≤ D.k) (σ : D.Φ) (i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j < l₀ D.towerExp)
    (hσ : σ ∈ D.bPlaces) (hσi : D.placeOfInt (-p) ^ i * σ ∈ D.bPlaces)
    (hσj : D.placeOfInt (-p) ^ j * σ ∈ D.bPlaces) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have h_not_dvd : ¬p ∣ P.q₁ 0 := fun h ↦ h_nonsplit (P.chiK_eq_one_of_dvd hp h)
  have h_coprime : IsCoprime (-p : ℤ) P.q₀ := (isCoprime_q₀_of_not_dvd h_not_dvd).neg_left
  -- The two ratios are `(-p) ^ i = ± p ^ i` and `(-p) ^ j = ± p ^ j`.
  -- Sparseness is stated modulo `ordCompl[p] q₁`, the part of `q₁` prime to `p`.
  have h_ratio (n : ℕ) :
      (P.placeClass (Nat.ordCompl_dvd (P.q₁ D.towerExp) p) (D.placeOfInt (-p) ^ n * σ / σ)).val =
        (((-1) ^ n : ℤˣ) : ℤ) * (p : ZMod (ordCompl[p] (P.q₁ D.towerExp))) ^ n := by
    simp [placeClass_placeOfInt h_coprime, neg_pow (Nat.cast p)]
  exact D.sparse p hp (hk.trans (Nat.le_mul_of_pos_right _ D.t_odd.pos)) i j hi hij hj
    ⟨σ, hσ, _, hσi, _, hσj, (-1) ^ i, (-1) ^ j, h_ratio i, h_ratio j⟩

/-! ## Near pairs -/

/-- `(τ, e)` is a near pair with start `τ` and end `-p ^ e τ`: the exponent `e` lies in `I_p` (odd
if `p` is inert, positive if `p = d`), `e < l₀ / 2`, and both places are `b`-places. -/
structure IsNearPair (D : Data P) (p : ℕ) (τ : D.Φ) (e : ℕ) : Prop where
  /-- The exponent lies in `I_p`. -/
  exponent_mem : e ∈ positivePartnerExponents P.d p
  /-- The exponent is less than `l₀ / 2`. -/
  two_mul_lt : 2 * e < l₀ D.towerExp
  /-- The start is a `b`-place. -/
  start_mem : τ ∈ D.bPlaces
  /-- The end is a `b`-place. -/
  end_mem : P.partner D.towerExp p e τ ∈ D.bPlaces


/-- For `p = d` there are no near pairs, as all `b`-places have the same class modulo `q₀`. -/
lemma IsNearPair.ne_d {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) : p ≠ P.d :=
  D.ne_d_of_placeClass_eq
    ((D.placeClass_of_mem_bPlaces _ h.end_mem).trans
      (D.placeClass_of_mem_bPlaces _ h.start_mem).symm)

/-- Near pairs occur only at inert primes, and their exponents are odd, as there are none for
`p = d`. -/
lemma IsNearPair.inert_and_odd {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) :
    chiK P.d p = -1 ∧ Odd e := by
  obtain ⟨-, h_mem⟩ := mem_positivePartnerExponents.1 h.exponent_mem
  exact (mem_partnerExponents.1 h_mem).resolve_left h.ne_d

lemma IsNearPair.inert {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) :
    chiK P.d p = -1 := h.inert_and_odd.1

lemma IsNearPair.odd {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) : Odd e :=
  h.inert_and_odd.2

lemma IsNearPair.pos {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) : 0 < e :=
  h.odd.pos

/-- The end `-p ^ e τ` of a near pair `(τ, e)` is `(-p) ^ e τ`, as `e` is odd. -/
lemma IsNearPair.partner_eq {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) :
    P.partner D.towerExp p e τ = D.placeOfInt (-p) ^ e * τ := by
  rw [partner, ← h.odd.neg_pow, placeOfInt_pow]

/-- The end of a near pair, written as `(-p) ^ e τ`, is a `b`-place. -/
lemma IsNearPair.pow_mul_mem {D : Data P} {p : ℕ} {τ : D.Φ} {e : ℕ} (h : D.IsNearPair p τ e) :
    D.placeOfInt (-p) ^ e * τ ∈ D.bPlaces := by
  simpa only [h.partner_eq] using h.end_mem

/-- For a prime `p ≤ D.k` that does not split in `K = ℚ(√-d)`, that is `χ_K(p) ≠ 1`, near pairs
`(τ, e)`, `(τ, e')` with the same start have the same exponent. -/
lemma IsNearPair.exponent_unique {D : Data P} {p : ℕ} {τ : D.Φ} {e e' : ℕ} (hp : p.Prime)
    (h_nonsplit : chiK P.d p ≠ 1) (hk : p ≤ D.k) (h : D.IsNearPair p τ e)
    (h' : D.IsNearPair p τ e') : e = e' := by
  by_contra hne
  wlog hlt : e < e' generalizing e e' with h_symm
  · exact h_symm h' h (Ne.symm hne) (by lia)
  -- For `e < e'` the `b`-places `τ`, `-p ^ e τ`, `-p ^ e' τ` are a triple that sparseness excludes.
  exact D.notMem_bPlaces_of_two_partners hp h_nonsplit hk τ e e' h.pos hlt
    (by linarith [h'.two_mul_lt]) h.start_mem h.pow_mul_mem h'.pow_mul_mem

/-- For a prime `p ≤ k = D.k` that does not split in `K = ℚ(√-d)`, two near pairs `(τ, e)`,
`(τ', e')` with the same end are equal. -/
lemma IsNearPair.eq_and_eq_of_partner_eq {D : Data P} {p : ℕ} {τ τ' : D.Φ} {e e' : ℕ} (hp : p.Prime)
    (h_nonsplit : chiK P.d p ≠ 1) (hk : p ≤ D.k) (h : D.IsNearPair p τ e)
    (h' : D.IsNearPair p τ' e')
    (h_end : P.partner D.towerExp p e τ = P.partner D.towerExp p e' τ') : τ = τ' ∧ e = e' := by
  suffices he : e = e' by
    subst he
    exact ⟨mul_left_cancel h_end, rfl⟩
  by_contra hne
  wlog hlt : e < e' generalizing τ τ' e e' with h_symm
  · exact h_symm h' h h_end.symm (Ne.symm hne) (by lia)
  -- For `e < e'` the places `τ'`, `τ = p ^ (e' - e) τ'`, `-p ^ e' τ'` are `b`-places.
  obtain rfl : τ = D.placeOfInt (-p) ^ (e' - e) * τ' := by
    apply mul_left_cancel (a := D.placeOfInt (-p) ^ e)
    rw [← h.partner_eq, h_end, h'.partner_eq, ← mul_assoc, pow_mul_pow_sub _ hlt.le]
  exact D.notMem_bPlaces_of_two_partners hp h_nonsplit hk τ' (e' - e) e' (Nat.sub_pos_of_lt hlt)
    (Nat.sub_lt h'.pos h.pos) (by linarith [h'.two_mul_lt]) h'.start_mem h.start_mem h'.pow_mul_mem

/-- For a prime `p ≤ D.k` that does not split in `K = ℚ(√-d)`, that is `χ_K(p) ≠ 1`, the end
`-p ^ e τ` of a near pair `(τ, e)` is not the start `τ'` of a near pair `(τ', e')`. -/
lemma IsNearPair.end_ne_start {D : Data P} {p : ℕ} {τ τ' : D.Φ} {e e' : ℕ} (hp : p.Prime)
    (h_nonsplit : chiK P.d p ≠ 1) (hk : p ≤ D.k) (h : D.IsNearPair p τ e)
    (h' : D.IsNearPair p τ' e') : P.partner D.towerExp p e τ ≠ τ' := by
  -- Otherwise `τ`, `-p ^ e τ`, `p ^ (e + e') τ` are `b`-places; note that `e, e'` are odd.
  rintro rfl
  have h_end : D.placeOfInt (-p) ^ (e' + e) * τ ∈ D.bPlaces := by
    simpa only [pow_add, mul_assoc, h.partner_eq] using h'.pow_mul_mem
  exact D.notMem_bPlaces_of_two_partners hp h_nonsplit hk τ e (e' + e) h.pos
    (lt_add_of_pos_left e h'.pos) (by linarith [h.two_mul_lt, h'.two_mul_lt]) h.start_mem
      h.pow_mul_mem h_end

end New.Data

/-! ## The losses allowed in the sharpness bound -/

namespace New

/-- The `p`-adic valuation is monotone for divisibility of nonzero natural numbers. -/
lemma padicValNat_mono_of_dvd {p : ℕ} [hp : Fact p.Prime] {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).1 (pow_padicValNat_dvd.trans hab)

/-- One step of Legendre's formula: for the `p`-adic valuation `v = padicValNat p`,
`v(n!) = ⌊n / p⌋ + v(⌊n / p⌋!)`. -/
lemma padicValNat_factorial_eq_div_add {p : ℕ} [Fact p.Prime] (n : ℕ) :
    padicValNat p n ! = n / p + padicValNat p (n / p)! := by
  rw [← padicValNat_mul_div_factorial, padicValNat_factorial_mul, add_comm]

/-- For a prime `p`, the first term of Legendre's formula gives `n / p - 1 ≤ v(n!)`, with
`v = padicValNat p` and `n / p` taken as real division. -/
lemma div_sub_one_le_padicValNat_factorial {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (n / p - 1 : ℝ) ≤ padicValNat p n ! := by
  grw [sub_one_lt_floor (n / p : ℝ), floor_div_eq_div, padicValNat_factorial_eq_div_add n,
    ← Nat.le_add_right]

namespace Data

variable {P : Parameters}

/-- The number `n♯ = ⌈6 b / k⌉` of factors given up at each place, for the numbers `b` and `k` of
the data `D`. -/
noncomputable def lossFactorCount (D : Data P) : ℕ := ⌈6 * D.b / D.k⌉₊

/-- The product `B = (l⁻ + 1) ⋯ (l⁻ + n♯)` of the `n♯` integers after `l⁻ = (l - n♯)₊`, where
`n♯ = D.lossFactorCount`. -/
noncomputable def lossProduct (D : Data P) (l : ℕ) : ℕ :=
  (l - D.lossFactorCount + 1).ascFactorial D.lossFactorCount

lemma lossProduct_ne_zero (D : Data P) (l : ℕ) : D.lossProduct l ≠ 0 := (ascFactorial_pos _ _).ne'

/-- `v(n♯!) ≤ v(B)` for the `p`-adic valuation `v = padicValNat p`, as the product
`B = D.lossProduct l` of `n♯ = D.lossFactorCount` consecutive integers is a multiple of `n♯!`. -/
lemma padicValNat_factorial_lossFactorCount_le (D : Data P) {p : ℕ} [Fact p.Prime] (l : ℕ) :
    padicValNat p D.lossFactorCount ! ≤ padicValNat p (D.lossProduct l) :=
  padicValNat_mono_of_dvd (factorial_dvd_ascFactorial _ _) (D.lossProduct_ne_zero l)

/-- `v(l!) ≤ v(l⁻!) + v(B)` with `v = padicValNat p`, for `l⁻ = (l - n♯)₊`, `n♯ = D.lossFactorCount`
and the product `B = D.lossProduct l` of the `n♯` integers after `l⁻`, as `l!` divides
`(l⁻ + n♯)! = l⁻! B`. -/
lemma padicValNat_factorial_le_add_lossProduct (D : Data P) {p : ℕ} [Fact p.Prime] (l : ℕ) :
    padicValNat p l ! ≤
      padicValNat p (l - D.lossFactorCount)! + padicValNat p (D.lossProduct l) := by
  rw [← padicValNat.mul (factorial_ne_zero _) (D.lossProduct_ne_zero l), lossProduct,
    factorial_mul_ascFactorial]
  exact padicValNat_mono_of_dvd (factorial_dvd_factorial le_tsub_add) (factorial_ne_zero _)

/-- `x ^ 42 ≤ n♯ = ⌈6 b / k⌉` for the numbers `x`, `b` and `k` of the data `D`, as `b` is far larger
than `x` and `k`. -/
lemma x_pow_le_lossFactorCount (D : Data P) : D.x ^ 42 ≤ D.lossFactorCount :=
  (D.le_of_hasLogBound : D.x ^ 42 ≤ (⌈6 * D.b / D.k⌉₊ : ℝ))

/-- Legendre's formula up to `O(log b)`: for `n ≤ 2 b` and `p ≥ 3`, the `p`-adic valuation
`v(n!) = padicValNat p n!` lies between `n / (p - 1) - (log b + 2)` and `n / (p - 1)`; here `b` is
the size parameter of the data `D` and `D.logB = log b`. -/
lemma padicValNat_factorial_mem_Icc_of_le (D : Data P) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {n : ℕ}
    (hn : n ≤ 2 * D.b) :
    (padicValNat p n ! : ℝ) ∈ Set.Icc (n / (p - 1) - (D.logB + 2)) (n / (p - 1) : ℝ) := by
  -- The number of digits of `n` in base `p ≥ e` is at most `⌈log b⌉ + 1`.
  have h_logB : 0 ≤ D.logB := (HasLogBound.pos D).le
  have h_digits : n < p ^ (⌈D.logB⌉₊ + 1) := by
    rify
    calc (n : ℝ) ≤ 2 * exp D.logB := hn -- by the definition of `b`
      _ < exp 1 * exp D.logB := mul_lt_mul_of_pos_right exp_one_gt_two (exp_pos _)
      _ ≤ exp 1 ^ (⌈D.logB⌉₊ + 1) := by grw [_root_.pow_succ', exp_one_pow, ← le_ceil]
      _ ≤ p ^ (⌈D.logB⌉₊ + 1) := by grw [exp_one_lt_three.le, ← hp3, cast_ofNat]
  refine Set.Icc_subset_Icc_left ?_ (padicValNat_factorial_mem_Icc h_digits)
  push_cast
  linarith [ceil_lt_add_one h_logB]

/-- For `p ≥ 3` and `n₁ + n₂ + n₃ ≤ 2 b`, the multinomial coefficient
`(n₁ + n₂ + n₃)! / (n₁! n₂! n₃!)` has valuation at most `3 (log b + 2)`.

This is a consequence of Legendre's formula for the `p`-adic valuation of factorials, applied
through two-sided bounds on `v(n!)` for `n ≤ 2 b`. -/
lemma padicValNat_factorial_add_add_le (D : Data P) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    {n₁ n₂ n₃ : ℕ} (hn : (n₁ + n₂ + n₃ : ℕ) ≤ 2 * D.b) :
    (padicValNat p (n₁ + n₂ + n₃)! : ℝ) ≤
      padicValNat p n₁ ! + padicValNat p n₂ ! + padicValNat p n₃ ! + 3 * (D.logB + 2) := by
  -- In Legendre's formula the main terms `n / (p - 1)` cancel.
  have h_lower {n : ℕ} (h_le : n ≤ n₁ + n₂ + n₃) :
      (n / (p - 1) - (D.logB + 2) : ℝ) ≤ padicValNat p n ! :=
    (D.padicValNat_factorial_mem_Icc_of_le hp3 ((cast_le.2 h_le).trans hn)).1
  have h_upper : (padicValNat p (n₁ + n₂ + n₃)! : ℝ) ≤ (n₁ + n₂ + n₃ : ℕ) / (p - 1) :=
    (D.padicValNat_factorial_mem_Icc_of_le hp3 hn).2
  rw [cast_add, cast_add, add_div, add_div] at h_upper
  linarith [h_lower (n := n₁) (by lia), h_lower (n := n₂) (by lia), h_lower (n := n₃) (by lia)]

/-- `n♯ / p - 1 ≤ v(n♯!) ≤ v(B)` for the `p`-adic valuation `v = padicValNat p`,
`n♯ = D.lossFactorCount` and the product `B = D.lossProduct l` of `n♯` consecutive integers. -/
lemma lossFactorCount_div_sub_one_le (D : Data P) {p : ℕ} [Fact p.Prime] (l : ℕ) :
    (D.lossFactorCount / p - 1 : ℝ) ≤ padicValNat p (D.lossProduct l) := by
  grw [div_sub_one_le_padicValNat_factorial, D.padicValNat_factorial_lossFactorCount_le l]

/-- The term `min (κ(τ) / p ^ e) (κ(-p ^ e τ))` for `e ∈ I_p = positivePartnerExponents P.d p`, and
`0` for the other `e`; `κ` is the weight of a place. -/
noncomputable def partnerMinTerm (D : Data P) (p : ℕ) (τ : D.Φ) (e : ℕ) : ℝ :=
  if e ∈ positivePartnerExponents P.d p then
    min (D.weight τ / p ^ e : ℝ) (D.weight (P.partner D.towerExp p e τ)) else 0

/-- The sum `R_τ` of `min (κ(τ) / p ^ e) (κ(-p ^ e τ))` over `e ∈ I_p` (the odd numbers if `p` is
inert, all `e ≥ 1` if `p = d`); `κ` is the weight of a place. -/
noncomputable def partnerMinSum (D : Data P) (p : ℕ) (τ : D.Φ) : ℝ :=
  ∑' e : ℕ, D.partnerMinTerm p τ e

lemma partnerMinTerm_nonneg (D : Data P) (p : ℕ) (τ : D.Φ) (e : ℕ) :
    0 ≤ D.partnerMinTerm p τ e := by
  unfold partnerMinTerm
  positivity

/-- Each term `D.partnerMinTerm p τ e` is at most `κ(τ) / p ^ e`, where `κ(τ) = D.weight τ` is the
weight of `τ`. -/
lemma partnerMinTerm_le_div (D : Data P) (p : ℕ) (τ : D.Φ) (e : ℕ) :
    D.partnerMinTerm p τ e ≤ D.weight τ / p ^ e := by
  unfold partnerMinTerm
  split_ifs
  · exact min_le_left _ _
  · positivity

lemma partnerMinSum_nonneg (D : Data P) {p : ℕ} (τ : D.Φ) : 0 ≤ D.partnerMinSum p τ :=
  tsum_nonneg (D.partnerMinTerm_nonneg p τ)

/-- The identity `γ_p |κ| - S_p = v(π_p) ∑ R_τ`, the last sum over the infinite places `τ` of `E`.
The weights are `κ = D.weight`, with sum `|κ|`. Then `S_p = D.localPrimeSumTotal p`, the predicted
valuation, is the sum over `τ` of `v(π_p) ∑ (κ(τ) / p ^ e - κ(-p ^ e τ))⁺` over `e ∈ I_p`, and
`R_τ = D.partnerMinSum p τ` is the sum of `min (κ(τ) / p ^ e) (κ(-p ^ e τ))` over the same `e`. -/
lemma mul_sum_weight_sub_localPrimeSumTotal (D : Data P) (p : ℕ) [Fact p.Prime] :
    gammaPrime P.d p * ∑ τ : D.Φ, (D.weight τ : ℝ) - D.localPrimeSumTotal p =
      piPrimeValuation P.d p * ∑ τ : D.Φ, D.partnerMinSum p τ := by
  -- At each place use `γ_p = v(π_p) ∑ p ^ (-e)`, the sum over `e ∈ I_p`, and
  -- `y - (y - z)₊ = min y z`.
  rw [localPrimeSumTotal, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun τ _ ↦ ?_
  have h_geom := hasSum_div_pow_positivePartnerExponents P.d p (D.weight τ : ℝ)
  have h_sub_posPart (y z : ℝ) : y - (y - z)⁺ = min y z := by grind [posPart_def]
  have h_min : D.partnerMinSum p τ = D.weight τ * gammaPrime P.d p / piPrimeValuation P.d p -
      ∑' e : ℕ, if e ∈ positivePartnerExponents P.d p then
        (D.weight τ / p ^ e - D.weight (D.placeOfInt (-p ^ e) * τ) : ℝ)⁺ else 0 := by
    rw [← h_geom.tsum_eq, ← h_geom.summable.tsum_sub (D.summable_posPart_sub_weight p _ τ)]
    exact tsum_congr fun e ↦ by simp [partnerMinTerm, partner, ite_sub_ite, h_sub_posPart]
  rw [h_min, localPrimeSum]
  field [(piPrimeValuation_pos P.d p).ne']

/-- Off the `b`-places the weight of a place is `a / x₁`. -/
lemma weight_of_notMem (D : Data P) {τ : D.Φ} (hτ : τ ∉ D.bPlaces) :
    (D.weight τ : ℝ) = D.a / D.x₁ := by
  rw [cast_weight, ite_eq_right hτ]

/-- A `b`-place has weight `a / x = b`, as `a = x b`. -/
lemma weight_of_mem (D : Data P) {τ : D.Φ} (hτ : τ ∈ D.bPlaces) : (D.weight τ : ℝ) = D.b := by
  rw [cast_weight, ite_eq_left hτ, cast_a, mul_div_cancel_left₀ _ (exp_ne_zero D.logX : D.x ≠ 0)]

lemma b_le_weight (D : Data P) {τ : D.Φ} (hτ : τ ∈ D.bPlaces) : D.b ≤ D.weight τ :=
  (D.weight_of_mem hτ).ge

/-- For any `n` and `e`, the term of `R_τ` with exponent `e + n` is at most `b / (p ^ n 2 ^ e)`, the
general term of a geometric series with sum `2 b / p ^ n`. The term at an exponent `i` is
`D.partnerMinTerm p τ i`. -/
lemma partnerMinTerm_add_le (D : Data P) {p : ℕ} [hp : Fact p.Prime] (τ : D.Φ) (n e : ℕ) :
    D.partnerMinTerm p τ (e + n) ≤ 2 * D.b / p ^ n / 2 / 2 ^ e := by
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp.out.two_le
  calc D.partnerMinTerm p τ (e + n) ≤ D.weight τ / p ^ (e + n) := D.partnerMinTerm_le_div p τ _
    _ ≤ D.b / (2 ^ e * p ^ n) := by
        grw [D.weight_le_b τ, pow_add, ← pow_le_pow_left₀ zero_le_two hp2 e]
    _ = 2 * D.b / p ^ n / 2 / 2 ^ e := by field

/-- The series of the terms `D.partnerMinTerm p τ e` over `e` converges, by comparison with a
geometric series. -/
lemma summable_partnerMinTerm (D : Data P) {p : ℕ} [Fact p.Prime] (τ : D.Φ) :
    Summable (D.partnerMinTerm p τ) :=
  (summable_geometric_two' _).of_nonneg_of_le (D.partnerMinTerm_nonneg p τ)
    (D.partnerMinTerm_add_le τ 0)

/-- Let `n ≥ l₀ / 2`, where `l₀ = l₀ D.towerExp` is the least power of `3` above `27 D.towerExp`.
Then the terms `D.partnerMinTerm p τ e`, `e ≥ n`, add up to at most `2 b / (k p)`. -/
lemma tsum_partnerMinTerm_add_le (D : Data P) {p : ℕ} [hp : Fact p.Prime] (τ : D.Φ) {n : ℕ}
    (hn : l₀ D.towerExp ≤ 2 * n) :
    ∑' e : ℕ, D.partnerMinTerm p τ (e + n) ≤ 2 * D.b / (D.k * p) := by
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp.out.two_le
  have hk_pos : (0 : ℝ) < D.k := mod_cast D.k_pos
  have h_towerExp_lt : D.towerExp < n := by linarith [mul_lt_l₀ D.towerExp]
  obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = n' + 1 := exists_eq_succ_of_ne_zero h_towerExp_lt.ne_bot
  have hk_le : (D.k : ℝ) ≤ p ^ n' :=
    calc (D.k : ℝ) ≤ 2 ^ D.towerExp := D.le_of_hasLogBound
      _ ≤ 2 ^ n' := pow_le_pow_right₀ one_le_two (Nat.le_of_lt_succ h_towerExp_lt)
      _ ≤ p ^ n' := pow_le_pow_left₀ zero_le_two hp2 n'
  calc ∑' e : ℕ, D.partnerMinTerm p τ (e + (n' + 1)) ≤ 2 * D.b / p ^ (n' + 1) :=
        hasSum_le (D.partnerMinTerm_add_le τ _)
          ((summable_nat_add_iff _).2 (D.summable_partnerMinTerm τ)).hasSum
          (hasSum_geometric_two' _)
    _ ≤ 2 * D.b / (D.k * p) := by grw [_root_.pow_succ, ← hk_le]

/-- If `e < l₀ / 2` and `(τ, e)` is not a near pair, then the term `D.partnerMinTerm p τ e` is at
most `a / x₁`. This term is `min (κ(τ) / p ^ e) (κ(-p ^ e τ))` if `e` lies in the set `I_p` and `0`
otherwise. -/
lemma partnerMinTerm_le_of_not_isNearPair (D : Data P) {p : ℕ} [hp : Fact p.Prime] {τ : D.Φ} {e : ℕ}
    (he : 2 * e < l₀ D.towerExp) (h_not_near : ¬D.IsNearPair p τ e) :
    D.partnerMinTerm p τ e ≤ D.a / D.x₁ := by
  by_cases h_start : τ ∈ D.bPlaces
  · unfold partnerMinTerm
    split_ifs with h_exponent
    · have h_end : P.partner D.towerExp p e τ ∉ D.bPlaces := fun h_mem ↦
        h_not_near ⟨h_exponent, he, h_start, h_mem⟩
      exact min_le_of_right_le (D.weight_of_notMem h_end).le
    · positivity
  · calc D.partnerMinTerm p τ e ≤ D.weight τ / p ^ e := D.partnerMinTerm_le_div p τ e
      _ ≤ D.weight τ := div_le_self (cast_nonneg _) (one_le_pow₀ (mod_cast hp.out.one_le))
      _ = D.a / D.x₁ := D.weight_of_notMem h_start

/-- Let `c ≥ 0`, and suppose that a near pair `(τ, e)` can occur only for `e = e₀`, and that
`κ(τ) / p ^ e₀ ≤ c + 1` if it occurs. Then `R_τ ≤ c + 1 + l₀ a / x₁ + 2 b / (k p)`: the term of the
near pair is at most `c + 1`, each other term with `e < l₀ / 2` at most `a / x₁`, and the rest add
up to at most `2 b / (k p)`. -/
lemma partnerMinSum_le (D : Data P) {p : ℕ} [Fact p.Prime] {τ : D.Φ} {e₀ : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h_near : ∀ e : ℕ, D.IsNearPair p τ e → e = e₀ ∧ (D.weight τ : ℝ) / p ^ e ≤ c + 1) :
    D.partnerMinSum p τ ≤ c + 1 + l₀ D.towerExp * (D.a / D.x₁) + 2 * D.b / (D.k * p) := by
  -- Cut the series at `n = ⌈l₀ / 2⌉`.
  obtain ⟨n, hn_lower, hn_upper⟩ : ∃ n : ℕ, l₀ D.towerExp ≤ 2 * n ∧ 2 * n ≤ l₀ D.towerExp + 1 :=
    ⟨(l₀ D.towerExp + 1) / 2, by lia, by lia⟩
  have h_term_le (e : ℕ) (he : e ∈ range n) :
      D.partnerMinTerm p τ e ≤ (if e = e₀ then c + 1 else 0) + D.a / D.x₁ := by
    by_cases h_pair : D.IsNearPair p τ e
    · obtain ⟨rfl, h_term⟩ := h_near e h_pair
      rw [ite_eq_left rfl]
      exact le_add_of_le_of_nonneg ((D.partnerMinTerm_le_div p τ e).trans h_term) (by positivity)
    · exact le_add_of_nonneg_of_le (by positivity)
        (D.partnerMinTerm_le_of_not_isNearPair (by grind) h_pair)
  have h_single : ∑ e ∈ range n, (if e = e₀ then c + 1 else 0) ≤ c + 1 := by
    simp [sum_ite_eq', apply_ite (· ≤ c + 1), add_nonneg hc zero_le_one]
  calc D.partnerMinSum p τ = ∑ e ∈ range n, D.partnerMinTerm p τ e + ∑' e : ℕ,
         D.partnerMinTerm p τ (e + n) :=
        ((D.summable_partnerMinTerm τ).sum_add_tsum_nat_add n).symm
    _ ≤ ∑ e ∈ range n, ((if e = e₀ then c + 1 else 0) + D.a / D.x₁) + 2 * D.b / (D.k * p) :=
        add_le_add (sum_le_sum h_term_le) (D.tsum_partnerMinTerm_add_le τ hn_lower)
    _ ≤ c + 1 + l₀ D.towerExp * (D.a / D.x₁) + 2 * D.b / (D.k * p) := by
        grw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, h_single,
          show n ≤ l₀ D.towerExp by lia]

/-- For a prime `p ≤ k` and any `l`, the errors at one place add up to at most
`3 b / (k p) ≤ n♯ / p - 1 ≤ v(B)`. There are three errors: `3 (log b + 2) + x ^ 42 + 1`, which is at
most the weight `a / x₁` off the `b`-places; `l₀` times that weight; and `2 b / (k p)`. -/
lemma error_le_padicValNat_lossProduct (D : Data P) {p : ℕ} [hp : Fact p.Prime] (hk : p ≤ D.k)
    (l : ℕ) :
    3 * (D.logB + 2) + D.x ^ 42 + 1 + l₀ D.towerExp * (D.a / D.x₁) + 2 * D.b / (D.k * p) ≤
      padicValNat p (D.lossProduct l) := by
  have hp_pos : (0 : ℝ) < p := mod_cast hp.out.pos
  have hk_pos : (0 : ℝ) < D.k := mod_cast D.k_pos
  have h_small : 3 * (D.logB + 2) + D.x ^ 42 + 1 ≤ D.a / D.x₁ := D.le_of_hasLogBound
  have h_one : (1 : ℝ) ≤ (l₀ D.towerExp + 1) * (D.a / D.x₁) :=
    one_le_mul_of_one_le_of_one_le (by simp) D.le_of_hasLogBound
  have h_gap : (l₀ D.towerExp + 1) * (D.a / D.x₁) ≤ D.b / (D.k * p) :=
    calc (l₀ D.towerExp + 1) * (D.a / D.x₁) ≤ (81 * D.towerExp + 1) * (D.a / D.x₁) := by
          grw [l₀_le_mul D.towerExp_ne_zero, cast_mul, cast_ofNat]
      _ ≤ D.b / (D.k * D.k) := D.le_of_hasLogBound
      _ ≤ D.b / (D.k * p) := by grw [hk]
  have h_length : 6 * (D.b / (D.k * p)) ≤ D.lossFactorCount / p := by
    grw [lossFactorCount, ← le_ceil, ← mul_div_assoc, div_div]
  calc 3 * (D.logB + 2) + D.x ^ 42 + 1 + l₀ D.towerExp * (D.a / D.x₁) + 2 * D.b / (D.k * p)
      ≤ 3 * (D.b / (D.k * p)) := by linarith [h_small, h_gap, mul_div_assoc 2 D.b (D.k * p)]
    _ ≤ D.lossFactorCount / p - 1 := by linarith [h_one, h_gap, h_length]
    _ ≤ padicValNat p (D.lossProduct l) := D.lossFactorCount_div_sub_one_le l

end Data

end New
