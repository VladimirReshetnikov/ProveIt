import DiophantineConsistency.ArithmeticWindowDigits
import DiophantineConsistency.ArithmeticBinomLegendre

/-! # Jones 1982, §2 (Lemmas 2.4, 2.7, 2.8, 2.10, 2.11, 2.15, 2.16) in every model of `𝗜𝚺₁`

The carry lemmas of `Jones1982` (`Diophantine/Paper1982/Carries.lean`), reproved at
arbitrary internal arguments of a model `V` of `𝗜𝚺₁`.  The external condition
`τ₂(a, b) = 0` is the bounded internal `ArithmeticBinaryCarry.NoCarry a b` (no binary
position carries two ones), the weight `σ` is `ArithmeticBinaryPopulation.population`,
and powers of two are `Exp.exp`.

* `noCarry_concat` (Lemma 2.10): for `S₁, T₁ < 2ᵏ`,
  `NoCarry S₁ T₁ ∧ NoCarry S₂ T₂ ↔ NoCarry (S₁ + S₂ 2ᵏ) (T₁ + T₂ 2ᵏ)`;
* `noCarry_three` (Lemma 2.11, three blocks), `noCarry_mul_exp`, `noCarry_two_mul` (Lemma 2.4);
* `lt_exp_iff_noCarry` (Lemma 2.7), `eq_zero_iff_noCarry_ones` (Lemma 2.7, `b = 1`),
  `eq_exp_iff_noCarry` (Lemma 2.8), `noCarry_block` (one digit of a radix-`2ᵗ` number);
* `exp_dvd_central_iff` (Lemma 2.15) from the internal Legendre formula;
* `noCarry_iff_sq_dvd_central` (Lemma 2.16): for `N = 2^α`, `S, T < N` and
  `R = S(N² − N) + (T + 1)(N² − 1)`, `NoCarry S T ↔ N² ∣ binom (2R) R`.

Every proof works bitwise through `fbit` or through the exact population identities
(`concatenate`, `complement`, `population_add_eq_iff`); no external Kummer theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelCarries
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticWindowDigits
  ArithmeticBinomPascal ArithmeticBinomLegendre
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Powers of two -/

/-- A standard power of a power of two is a power of two. -/
theorem pow_exp_exists (κ : V) (n : ℕ) : ∃ k : V, Exp.exp κ ^ n = Exp.exp k := by
  induction n with
  | zero => exact ⟨0, by rw [pow_zero, exp_zero]⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + κ, by rw [pow_succ, hk, exp_add]⟩

/-! ### Bits of a concatenation -/

/-- Bits below `k` of `S₁ + S₂ 2ᵏ` are bits of `S₁`. -/
theorem fbit_add_mul_exp_low (S₁ S₂ k i : V) (hi : i < k) :
    fbit (S₁ + S₂ * Exp.exp k) i = fbit S₁ i := by
  have hk : Exp.exp k = Exp.exp i * 2 * Exp.exp (k - (i+1)) := by
    have hj : i + 1 + (k - (i+1)) = k := add_tsub_cancel_of_le (lt_iff_succ_le.mp hi)
    conv_lhs => rw [← hj]
    rw [exp_add, exp_add, exp_one]
  rw [fbit_eq_div, fbit_eq_div, hk]
  exact div_mod_add_mul S₁ S₂ (Exp.exp i) 2 (Exp.exp (k - (i+1))) (exp_pos i) (by simp)

/-- Bits at `k + j` of `S₁ + S₂ 2ᵏ` (with `S₁ < 2ᵏ`) are bits of `S₂`. -/
theorem fbit_add_mul_exp_high (S₁ S₂ k j : V) (hS : S₁ < Exp.exp k) :
    fbit (S₁ + S₂ * Exp.exp k) (k + j) = fbit S₂ j := by
  rw [← fbit_div_exp, div_add_mul_self _ _ (exp_pos k), div_eq_zero_of_lt _ hS, zero_add]

/-- A number below `2ᵏ` has no bit at a position `≥ k`. -/
theorem fbit_eq_zero_of_lt_exp {S k i : V} (hS : S < Exp.exp k) (hi : k ≤ i) : fbit S i = 0 := by
  have h : S / Exp.exp i = 0 := div_eq_zero_of_lt _ (lt_of_lt_of_le hS (exp_monotone_le.mpr hi))
  rw [fbit_eq_div, h]
  simp

/-! ### Trivial carries -/

theorem noCarry_zero_left (x : V) : NoCarry 0 x := by
  rw [noCarry_iff]
  intro i
  rw [fbit_zero, zero_add]
  exact fbit_le_one x i

theorem noCarry_zero_right (x : V) : NoCarry x 0 :=
  (noCarry_comm _ _).mp (noCarry_zero_left x)

/-! ### Lemmas 2.10, 2.11, 2.4 -/

/-- **Lemma 2.10.** For `S₁, T₁ < 2ᵏ`:
`NoCarry S₁ T₁ ∧ NoCarry S₂ T₂ ↔ NoCarry (S₁ + S₂ 2ᵏ) (T₁ + T₂ 2ᵏ)`. -/
theorem noCarry_concat {k S₁ S₂ T₁ T₂ : V} (hS : S₁ < Exp.exp k) (hT : T₁ < Exp.exp k) :
    (NoCarry S₁ T₁ ∧ NoCarry S₂ T₂) ↔
      NoCarry (S₁ + S₂ * Exp.exp k) (T₁ + T₂ * Exp.exp k) := by
  simp only [noCarry_iff]
  constructor
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i < k
    · rw [fbit_add_mul_exp_low S₁ S₂ k i hi, fbit_add_mul_exp_low T₁ T₂ k i hi]
      exact h1 i
    · have hki : k ≤ i := not_lt.mp hi
      obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, (add_tsub_cancel_of_le hki).symm⟩
      rw [fbit_add_mul_exp_high S₁ S₂ k j hS, fbit_add_mul_exp_high T₁ T₂ k j hT]
      exact h2 j
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · by_cases hi : i < k
      · have h' := h i
        rwa [fbit_add_mul_exp_low S₁ S₂ k i hi, fbit_add_mul_exp_low T₁ T₂ k i hi] at h'
      · have hki : k ≤ i := not_lt.mp hi
        rw [fbit_eq_zero_of_lt_exp hS hki, fbit_eq_zero_of_lt_exp hT hki]
        simp
    · have h' := h (k + j)
      rwa [fbit_add_mul_exp_high S₁ S₂ k j hS, fbit_add_mul_exp_high T₁ T₂ k j hT] at h'

/-- **Lemma 2.11** for three blocks of sizes `2^{k₁}`, `2^{k₂}`. -/
theorem noCarry_three {k₁ k₂ S₁ S₂ S₃ T₁ T₂ T₃ : V}
    (hS₁ : S₁ < Exp.exp k₁) (hT₁ : T₁ < Exp.exp k₁)
    (hS₂ : S₂ < Exp.exp k₂) (hT₂ : T₂ < Exp.exp k₂) :
    (NoCarry S₁ T₁ ∧ NoCarry S₂ T₂ ∧ NoCarry S₃ T₃) ↔
      NoCarry (S₁ + S₂ * Exp.exp k₁ + S₃ * Exp.exp k₁ * Exp.exp k₂)
        (T₁ + T₂ * Exp.exp k₁ + T₃ * Exp.exp k₁ * Exp.exp k₂) := by
  have e1 : S₁ + S₂ * Exp.exp k₁ + S₃ * Exp.exp k₁ * Exp.exp k₂ =
      S₁ + (S₂ + S₃ * Exp.exp k₂) * Exp.exp k₁ := by ring
  have e2 : T₁ + T₂ * Exp.exp k₁ + T₃ * Exp.exp k₁ * Exp.exp k₂ =
      T₁ + (T₂ + T₃ * Exp.exp k₂) * Exp.exp k₁ := by ring
  rw [e1, e2, ← noCarry_concat hS₁ hT₁, ← noCarry_concat hS₂ hT₂]

/-- **Lemma 2.4.** Shifting both summands by `2ᵏ` does not change the carries. -/
theorem noCarry_mul_exp (k a b : V) :
    NoCarry (a * Exp.exp k) (b * Exp.exp k) ↔ NoCarry a b := by
  have h := noCarry_concat (k := k) (S₁ := 0) (T₁ := 0) (S₂ := a) (T₂ := b)
    (exp_pos k) (exp_pos k)
  simp only [zero_add] at h
  exact h.symm.trans ⟨fun h' => h'.2, fun h' => ⟨noCarry_zero_left 0, h'⟩⟩

theorem noCarry_two_mul (a b : V) : NoCarry (2 * a) (2 * b) ↔ NoCarry a b := by
  have h := noCarry_mul_exp 1 a b
  rw [exp_one, mul_comm a 2, mul_comm b 2] at h
  exact h

/-! ### Lemmas 2.7, 2.8 -/

/-- **Lemma 2.7.** For `s ≤ t` and `v < 2ᵗ`: `v < 2ˢ ↔ NoCarry (2ᵗ − 2ˢ) v`. -/
theorem lt_exp_iff_noCarry {s t v : V} (hst : s ≤ t) (hv : v < Exp.exp t) :
    v < Exp.exp s ↔ NoCarry (Exp.exp t - Exp.exp s) v := by
  have hZ : 0 < Exp.exp s := exp_pos s
  have hsplit : Exp.exp t = Exp.exp (t - s) * Exp.exp s := by
    rw [← exp_add, tsub_add_cancel_of_le hst]
  have hm : Exp.exp t - Exp.exp s = 0 + (Exp.exp (t - s) - 1) * Exp.exp s := by
    rw [zero_add, hsplit]
    have h1 : (Exp.exp (t - s) - 1) * Exp.exp s + Exp.exp s = Exp.exp (t - s) * Exp.exp s := by
      calc (Exp.exp (t - s) - 1) * Exp.exp s + Exp.exp s
          = ((Exp.exp (t - s) - 1) + 1) * Exp.exp s := by ring
        _ = Exp.exp (t - s) * Exp.exp s := by rw [tsub_add_cancel_of_le (one_le_exp _)]
    rw [← h1, add_tsub_cancel_right]
  have hv' : v = v % Exp.exp s + (v / Exp.exp s) * Exp.exp s := by
    have hd := div_add_mod v (Exp.exp s)
    calc v = Exp.exp s * (v / Exp.exp s) + v % Exp.exp s := hd.symm
      _ = v % Exp.exp s + (v / Exp.exp s) * Exp.exp s := by ring
  have hc := noCarry_concat (k := s) (S₁ := 0) (S₂ := Exp.exp (t - s) - 1)
    (T₁ := v % Exp.exp s) (T₂ := v / Exp.exp s) hZ (mod_lt _ hZ)
  rw [← hm, ← hv'] at hc
  rw [← hc, and_iff_right (noCarry_zero_left _)]
  have hq : v / Exp.exp s < Exp.exp (t - s) :=
    div_lt_of_lt_mul (by rw [← hsplit]; exact hv)
  constructor
  · intro h
    rw [div_eq_zero_of_lt _ h]
    exact noCarry_zero_right _
  · intro h
    have h0 : v / Exp.exp s = 0 := noCarry_ones (t - s) _ hq ((noCarry_comm _ _).mp h)
    rw [hv', h0, zero_mul, add_zero]
    exact mod_lt _ hZ

/-- **Lemma 2.7** with `b = 1`: for `v < 2ᴷ`, `v = 0 ↔ NoCarry (2ᴷ − 1) v`. -/
theorem eq_zero_iff_noCarry_ones {K v : V} (hv : v < Exp.exp K) :
    v = 0 ↔ NoCarry (Exp.exp K - 1) v := by
  constructor
  · rintro rfl
    exact noCarry_zero_right _
  · intro h
    exact noCarry_ones K v hv ((noCarry_comm _ _).mp h)

/-- **Lemma 2.8.** For `0 < x < 2·2^κ`: `x = 2^κ ↔ NoCarry x (2^κ − 1)`. -/
theorem eq_exp_iff_noCarry {κ x : V} (hx0 : 0 < x) (hx : x < 2 * Exp.exp κ) :
    x = Exp.exp κ ↔ NoCarry x (Exp.exp κ - 1) := by
  have hE : 0 < Exp.exp κ := exp_pos κ
  have hx' : x = x % Exp.exp κ + (x / Exp.exp κ) * Exp.exp κ := by
    have hd := div_add_mod x (Exp.exp κ)
    calc x = Exp.exp κ * (x / Exp.exp κ) + x % Exp.exp κ := hd.symm
      _ = x % Exp.exp κ + (x / Exp.exp κ) * Exp.exp κ := by ring
  have hm : Exp.exp κ - 1 = (Exp.exp κ - 1) + 0 * Exp.exp κ := by
    rw [zero_mul, add_zero]
  have hlt : Exp.exp κ - 1 < Exp.exp κ := tsub_lt_self hE (by simp)
  have hc := noCarry_concat (k := κ) (S₁ := x % Exp.exp κ) (S₂ := x / Exp.exp κ)
    (T₁ := Exp.exp κ - 1) (T₂ := 0) (mod_lt _ hE) hlt
  rw [← hx', ← hm] at hc
  rw [← hc, and_iff_left (noCarry_zero_right _)]
  constructor
  · intro h
    rw [h, Arithmetic.mod_self]
    exact noCarry_zero_left _
  · intro h
    have h0 : x % Exp.exp κ = 0 := noCarry_ones κ _ (mod_lt _ hE) h
    have hq : x / Exp.exp κ < 2 := div_lt_of_lt_mul hx
    have hq0 : x / Exp.exp κ ≠ 0 := by
      intro hq0
      rw [hx', h0, hq0] at hx0
      simp at hx0
    have hq1 : x / Exp.exp κ = 1 := by
      rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hq) with h' | h'
      · exact absurd h' hq0
      · exact h'
    rw [hx', h0, hq1, zero_add, one_mul]

/-- One radix-`2ᵗ` digit: for `c < 2ᵗ`,
`NoCarry X (c·(2ᵗ)^L) ↔ NoCarry (⌊X/(2ᵗ)^L⌋ mod 2ᵗ) c`. -/
theorem noCarry_block {t : V} (L : ℕ) (X c : V) (hc : c < Exp.exp t) :
    NoCarry X (c * Exp.exp t ^ L) ↔ NoCarry (X / Exp.exp t ^ L % Exp.exp t) c := by
  obtain ⟨K, hK⟩ := pow_exp_exists t L
  rw [hK]
  have hEK : 0 < Exp.exp K := exp_pos K
  have hB : 0 < Exp.exp t := exp_pos t
  have hX : X % Exp.exp K + (X / Exp.exp K) * Exp.exp K = X := by
    have hd := div_add_mod X (Exp.exp K)
    calc X % Exp.exp K + (X / Exp.exp K) * Exp.exp K
        = Exp.exp K * (X / Exp.exp K) + X % Exp.exp K := by ring
      _ = X := hd
  have h1 := noCarry_concat (k := K) (S₁ := X % Exp.exp K) (S₂ := X / Exp.exp K)
    (T₁ := 0) (T₂ := c) (mod_lt _ hEK) hEK
  rw [hX, zero_add] at h1
  rw [← h1, and_iff_right (noCarry_zero_right _)]
  have hQ : X / Exp.exp K % Exp.exp t + (X / Exp.exp K / Exp.exp t) * Exp.exp t =
      X / Exp.exp K := by
    have hd := div_add_mod (X / Exp.exp K) (Exp.exp t)
    calc X / Exp.exp K % Exp.exp t + (X / Exp.exp K / Exp.exp t) * Exp.exp t
        = Exp.exp t * (X / Exp.exp K / Exp.exp t) + X / Exp.exp K % Exp.exp t := by ring
      _ = X / Exp.exp K := hd
  have h2 := noCarry_concat (k := t) (S₁ := X / Exp.exp K % Exp.exp t)
    (S₂ := X / Exp.exp K / Exp.exp t) (T₁ := c) (T₂ := 0) (mod_lt _ hB) hc
  rw [hQ, zero_mul, add_zero] at h2
  rw [← h2, and_iff_left (noCarry_zero_right _)]

/-! ### Lemmas 2.15, 2.16 -/

/-- **Lemma 2.15.** `2^m ∣ binom (2R) R ↔ m ≤ σ(R)`. -/
theorem exp_dvd_central_iff (R m : V) :
    Exp.exp m ∣ binom (2*R) R ↔ m ≤ population R := by
  constructor
  · exact le_population_of_exp_dvd_central R m
  · intro h
    obtain ⟨d, hd⟩ : ∃ d, population R = m + d :=
      ⟨population R - m, (add_tsub_cancel_of_le h).symm⟩
    have h1 : Exp.exp m ∣ Exp.exp (population R) := ⟨Exp.exp d, by rw [hd, exp_add]⟩
    exact dvd_trans h1 (exp_population_dvd_central R)

/-- **Lemma 2.16.** For `N = 2^α`, `S, T < N` and `R = S(N² − N) + (T + 1)(N² − 1)`:
`NoCarry S T ↔ N² ∣ binom (2R) R`. -/
theorem noCarry_iff_sq_dvd_central {α S T R : V} (hS : S < Exp.exp α) (hT : T < Exp.exp α)
    (hR : R = S * (Exp.exp α ^ 2 - Exp.exp α) + (T + 1) * (Exp.exp α ^ 2 - 1)) :
    NoCarry S T ↔ Exp.exp α ^ 2 ∣ binom (2*R) R := by
  -- the complements `s' = N − 1 − S`, `t' = N − 1 − T`
  obtain ⟨s', hs'⟩ : ∃ s', Exp.exp α = S + s' + 1 := by
    have h1 : S + 1 ≤ Exp.exp α := lt_iff_succ_le.mp hS
    refine ⟨Exp.exp α - (S + 1), ?_⟩
    have h2 := add_tsub_cancel_of_le h1
    calc Exp.exp α = S + 1 + (Exp.exp α - (S + 1)) := h2.symm
      _ = S + (Exp.exp α - (S + 1)) + 1 := by ring
  obtain ⟨t', ht'⟩ : ∃ t', Exp.exp α = T + t' + 1 := by
    have h1 : T + 1 ≤ Exp.exp α := lt_iff_succ_le.mp hT
    refine ⟨Exp.exp α - (T + 1), ?_⟩
    have h2 := add_tsub_cancel_of_le h1
    calc Exp.exp α = T + 1 + (Exp.exp α - (T + 1)) := h2.symm
      _ = T + (Exp.exp α - (T + 1)) + 1 := by ring
  have hs'lt : s' < Exp.exp α := by
    rw [hs']
    exact lt_of_le_of_lt (le_add_left le_rfl) (lt_add_one _)
  have ht'lt : t' < Exp.exp α := by
    rw [ht']
    exact lt_of_le_of_lt (le_add_left le_rfl) (lt_add_one _)
  have htt : T + t' = S + s' := by
    have h : T + t' + 1 = S + s' + 1 := by rw [← ht', ← hs']
    exact add_right_cancel h
  -- `R = ((S + T) N + s') N + t'`
  have hX : (S + s' + 1) ^ 2 - (S + s' + 1) = (S + s') * (S + s') + (S + s') := by
    rw [show (S + s' + 1) ^ 2 = ((S + s') * (S + s') + (S + s')) + (S + s' + 1) by ring,
      add_tsub_cancel_right]
  have hY : (S + s' + 1) ^ 2 - 1 = (S + s') * (S + s') + 2 * (S + s') := by
    rw [show (S + s' + 1) ^ 2 = ((S + s') * (S + s') + 2 * (S + s')) + 1 by ring,
      add_tsub_cancel_right]
  have hR' : R = S * ((S + s') * (S + s') + (S + s')) +
      (T + 1) * ((S + s') * (S + s') + 2 * (S + s')) := by
    rw [hR, hs', hX, hY]
  have hRe : R = ((S + T) * Exp.exp α + s') * Exp.exp α + t' := by
    rw [hR', hs']
    apply add_right_cancel (b := T)
    calc S * ((S + s') * (S + s') + (S + s')) + (T + 1) * ((S + s') * (S + s') + 2 * (S + s')) + T
        = ((S + T) * (S + s' + 1) + s') * (S + s' + 1) + (S + s') := by ring
      _ = ((S + T) * (S + s' + 1) + s') * (S + s' + 1) + (T + t') := by rw [htt]
      _ = ((S + T) * (S + s' + 1) + s') * (S + s' + 1) + t' + T := by ring
  -- populations
  have hpR : population R = population (S + T) + population s' + population t' := by
    rw [hRe, ArithmeticBinaryPopulation.concatenate _ _ _ ht'lt,
      ArithmeticBinaryPopulation.concatenate _ _ _ hs'lt]
  have hcS : population S + population s' = α := by
    have h := ArithmeticBinaryPopulation.complement α S hS
    have e : Exp.exp α - 1 - S = s' := by
      rw [hs', add_tsub_cancel_right, add_tsub_cancel_left]
    rwa [e] at h
  have hcT : population T + population t' = α := by
    have h := ArithmeticBinaryPopulation.complement α T hT
    have e : Exp.exp α - 1 - T = t' := by
      rw [ht', add_tsub_cancel_right, add_tsub_cancel_left]
    rwa [e] at h
  have h2 : 2 * α = (population S + population T) + (population s' + population t') := by
    calc 2 * α = α + α := two_mul α
      _ = (population S + population s') + (population T + population t') := by rw [hcS, hcT]
      _ = (population S + population T) + (population s' + population t') := by ring
  rw [← population_add_eq_iff, ← exp_even, exp_dvd_central_iff, hpR, h2,
    show population (S + T) + population s' + population t' =
      population (S + T) + (population s' + population t') by ring,
    add_le_add_iff_right]
  constructor
  · intro h
    exact le_of_eq h.symm
  · intro h
    exact le_antisymm (population_subadditive S T) h

end DiophantineConsistency.ModelCarries
