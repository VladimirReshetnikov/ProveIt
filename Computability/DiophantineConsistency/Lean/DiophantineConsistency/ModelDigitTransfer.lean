import DiophantineConsistency.ModelCarries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Jones 1982, Lemmas 2.9 and 2.11 in every model of `𝗜𝚺₁`

Radix-`R` numbers with a *standard* number of digits, inside a model `V` of `𝗜𝚺₁`:
`dsum R f n = Σ_{i<n} f i · Rⁱ` (`f : ℕ → V`, `n : ℕ`).  Every block count used by Jones's
reduction (`3L`, `4L`, `8L`, `2L + 1` with `L = 5^(ν+1)`) is standard, so these finite sums
and meta-level induction on `n` suffice; the digits themselves are arbitrary model elements.

* `dsum_lt`, `dsum_lt_mul`, `dsum_digit`, `mod_pow_eq_dsum`: bounds, digit extraction and the
  digit expansion of `Y mod Rⁿ`;
* `noCarry_dsum_iff` (Lemma 2.11): for digits below `2^w`, no carry between two radix-`2^w`
  numbers iff no carry between corresponding digits;
* `noCarry_mask_iff` (Lemma 2.9 (iii)): `NoCarry Y (Σ_{i<k} (B − Z) Bⁱ)` iff the first `k`
  radix-`B` digits of `Y` are `< Z` (`Z = 2ˢ ≤ B = 2ᵗ`);
* `transfer_iff` (**Lemma 2.9**): for digits `yᵢ < Z` (`i ≤ m ≤ k`) and `2 Z^(m+1) ≤ B`,
  `Y = Σ yᵢ Bⁱ` iff `Y = Σ yᵢ Zⁱ + (B − Z)c` for some `c`, `Y < Z Bᵐ`, and the mask test;
* `noCarry_shifted_iff` (the digit test (4.9)–(4.11)): for digits `0 < dᵢ < 2^(κ+1)`,
  `NoCarry (2 Σ dᵢ Bⁱ) (2 (2^κ − 1) B^L) ↔ d_L = 2^κ`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ModelDigitTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticWindowDigits ModelCarries
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Standard-length digit sums -/

/-- `Σ_{i<n} f i · Rⁱ`. -/
def dsum (R : V) (f : ℕ → V) (n : ℕ) : V := ∑ i ∈ Finset.range n, f i * R ^ i

theorem dsum_zero (R : V) (f : ℕ → V) : dsum R f 0 = 0 := by
  unfold dsum
  exact Finset.sum_range_zero _

theorem dsum_succ (R : V) (f : ℕ → V) (n : ℕ) : dsum R f (n+1) = dsum R f n + f n * R ^ n := by
  unfold dsum
  exact Finset.sum_range_succ _ _

theorem dsum_congr (R : V) {f g : ℕ → V} (n : ℕ) (h : ∀ i < n, f i = g i) :
    dsum R f n = dsum R g n := by
  unfold dsum
  exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])

/-- Digits below `R` give a number below `Rⁿ`. -/
theorem dsum_lt (R : V) (f : ℕ → V) (n : ℕ) (hf : ∀ i < n, f i < R) : dsum R f n < R ^ n := by
  induction n with
  | zero =>
    rw [dsum_zero, pow_zero]
    simp
  | succ n ih =>
    rw [dsum_succ]
    have h1 : dsum R f n < R ^ n := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have h2 : f n + 1 ≤ R := lt_iff_succ_le.mp (hf n (Nat.lt_succ_self n))
    calc dsum R f n + f n * R ^ n < R ^ n + f n * R ^ n := add_lt_add_of_lt_of_le h1 le_rfl
      _ = (f n + 1) * R ^ n := by ring
      _ ≤ R * R ^ n := mul_le_mul_of_nonneg_right h2 (Arithmetic.zero_le _)
      _ = R ^ (n+1) := by ring

/-- Digits below `Z ≤ R` give a number below `Z Rⁿ` (`n + 1` digits). -/
theorem dsum_lt_mul {R Z : V} {f : ℕ → V} {n : ℕ} (hZR : Z ≤ R) (hf : ∀ i < n + 1, f i < Z) :
    dsum R f (n+1) < Z * R ^ n := by
  rw [dsum_succ]
  have h1 : dsum R f n < R ^ n :=
    dsum_lt R f n (fun i hi => lt_of_lt_of_le (hf i (Nat.lt_succ_of_lt hi)) hZR)
  have h2 : f n + 1 ≤ Z := lt_iff_succ_le.mp (hf n (Nat.lt_succ_self n))
  calc dsum R f n + f n * R ^ n < R ^ n + f n * R ^ n := add_lt_add_of_lt_of_le h1 le_rfl
    _ = (f n + 1) * R ^ n := by ring
    _ ≤ Z * R ^ n := mul_le_mul_of_nonneg_right h2 (Arithmetic.zero_le _)

/-- The `j`-th radix-`R` digit of `Σ_{i<n} f i Rⁱ` is `f j`. -/
theorem dsum_digit (R : V) (hR : 0 < R) (f : ℕ → V) (n : ℕ) (hf : ∀ i < n, f i < R) :
    ∀ j < n, dsum R f n / R ^ j % R = f j := by
  induction n with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    intro j hj
    have hf' : ∀ i < n, f i < R := fun i hi => hf i (Nat.lt_succ_of_lt hi)
    rw [dsum_succ]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjn | hjn
    · have e : f n * R ^ n = f n * (R ^ j * R * R ^ (n - (j+1))) := by
        rw [← pow_succ, ← pow_add, Nat.add_sub_of_le (show j + 1 ≤ n by omega)]
      rw [e, div_mod_add_mul _ _ _ _ _ (pow_pos hR j) hR]
      exact ih hf' j hjn
    · rw [hjn, div_add_mul_self _ _ (pow_pos hR n), div_eq_zero_of_lt _ (dsum_lt R f n hf'),
        zero_add]
      exact mod_eq_self_of_lt (hf n (Nat.lt_succ_self n))

/-- Positions at or above `n` of an `n`-digit number vanish. -/
theorem dsum_div_eq_zero (R : V) (hR : 0 < R) (f : ℕ → V) (n : ℕ) (hf : ∀ i < n, f i < R)
    (j : ℕ) (hj : n ≤ j) : dsum R f n / R ^ j = 0 :=
  div_eq_zero_of_lt _ (lt_of_lt_of_le (dsum_lt R f n hf)
    (pow_le_pow_right₀ (pos_iff_one_le.mp hR) hj))

/-- `Y mod Rⁿ` is the number formed by the first `n` radix-`R` digits of `Y`. -/
theorem mod_pow_eq_dsum (Y R : V) (hR : 0 < R) (n : ℕ) :
    Y % R ^ n = dsum R (fun i => Y / R ^ i % R) n := by
  induction n with
  | zero => rw [pow_zero, dsum_zero, Arithmetic.mod_one]
  | succ n ih =>
    rw [dsum_succ, ← ih, pow_succ, mod_mul_split Y (R ^ n) R (pow_pos hR n) hR]

/-! ### Lemma 2.11 -/

/-- **Lemma 2.11** (`n` standard): for digits below `2^w`, no carry between the two
radix-`2^w` numbers iff no carry between corresponding digits. -/
theorem noCarry_dsum_iff (w : V) (f g : ℕ → V) (n : ℕ)
    (hf : ∀ i < n, f i < Exp.exp w) (hg : ∀ i < n, g i < Exp.exp w) :
    NoCarry (dsum (Exp.exp w) f n) (dsum (Exp.exp w) g n) ↔ ∀ i < n, NoCarry (f i) (g i) := by
  induction n with
  | zero =>
    rw [dsum_zero, dsum_zero]
    exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => noCarry_zero_left 0⟩
  | succ n ih =>
    have hf' : ∀ i < n, f i < Exp.exp w := fun i hi => hf i (Nat.lt_succ_of_lt hi)
    have hg' : ∀ i < n, g i < Exp.exp w := fun i hi => hg i (Nat.lt_succ_of_lt hi)
    obtain ⟨k, hk⟩ := pow_exp_exists w n
    rw [dsum_succ, dsum_succ, hk]
    have h1 : dsum (Exp.exp w) f n < Exp.exp k := by rw [← hk]; exact dsum_lt _ f n hf'
    have h2 : dsum (Exp.exp w) g n < Exp.exp k := by rw [← hk]; exact dsum_lt _ g n hg'
    rw [← noCarry_concat h1 h2, ih hf' hg']
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi' | hi'
      · exact h i hi'
      · rw [hi']; exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

/-! ### The mask of Lemma 2.9 (iii) -/

/-- `Σ_{i<k} (B − Z) Bⁱ`. -/
def mask (B Z : V) (k : ℕ) : V := dsum B (fun _ => B - Z) k

/-- **Lemma 2.9 (iii)** blockwise: `NoCarry Y (mask B Z k)` iff the first `k` radix-`B` digits
of `Y` are below `Z` (`Z = 2ˢ`, `B = 2ᵗ`, `s ≤ t`). -/
theorem noCarry_mask_iff {s t : V} (hst : s ≤ t) (k : ℕ) (Y : V) :
    NoCarry Y (mask (Exp.exp t) (Exp.exp s) k) ↔
      ∀ j < k, Y / Exp.exp t ^ j % Exp.exp t < Exp.exp s := by
  have hB : 0 < Exp.exp t := exp_pos t
  have hdig : ∀ i < k, Exp.exp t - Exp.exp s < Exp.exp t :=
    fun _ _ => tsub_lt_self hB (exp_pos s)
  have hmlt : mask (Exp.exp t) (Exp.exp s) k < Exp.exp t ^ k :=
    dsum_lt (Exp.exp t) (fun _ => Exp.exp t - Exp.exp s) k hdig
  obtain ⟨K, hK⟩ := pow_exp_exists t k
  rw [hK] at hmlt
  have hEK : 0 < Exp.exp K := exp_pos K
  have hX : Y % Exp.exp K + (Y / Exp.exp K) * Exp.exp K = Y := by
    have hd := div_add_mod Y (Exp.exp K)
    calc Y % Exp.exp K + (Y / Exp.exp K) * Exp.exp K
        = Exp.exp K * (Y / Exp.exp K) + Y % Exp.exp K := by ring
      _ = Y := hd
  have h := noCarry_concat (k := K) (S₁ := Y % Exp.exp K) (S₂ := Y / Exp.exp K)
    (T₁ := mask (Exp.exp t) (Exp.exp s) k) (T₂ := 0) (mod_lt _ hEK) hmlt
  rw [hX, zero_mul, add_zero] at h
  rw [← h, and_iff_left (noCarry_zero_right _), ← hK, mod_pow_eq_dsum Y _ hB k, mask,
    noCarry_dsum_iff t (fun i => Y / Exp.exp t ^ i % Exp.exp t) (fun _ => Exp.exp t - Exp.exp s)
      k (fun i _ => mod_lt _ hB) hdig]
  constructor
  · intro h' j hj
    exact (lt_exp_iff_noCarry hst (mod_lt _ hB)).mpr ((noCarry_comm _ _).mp (h' j hj))
  · intro h' j hj
    exact (noCarry_comm _ _).mp ((lt_exp_iff_noCarry hst (mod_lt _ hB)).mp (h' j hj))

/-! ### Lemma 2.9 -/

/-- `Bⁱ ≡ Zⁱ (mod B − Z)`, additively. -/
theorem pow_eq_add_mul {Z B : V} (hZB : Z ≤ B) (i : ℕ) : ∃ c, B ^ i = Z ^ i + (B - Z) * c := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨Z ^ i + c * B, ?_⟩
    have hB : B = Z + (B - Z) := (add_tsub_cancel_of_le hZB).symm
    calc B ^ (i+1) = B ^ i * B := pow_succ B i
      _ = (Z ^ i + (B - Z) * c) * B := by rw [hc]
      _ = Z ^ i * B + (B - Z) * (c * B) := by ring
      _ = Z ^ i * (Z + (B - Z)) + (B - Z) * (c * B) := by rw [← hB]
      _ = Z ^ (i+1) + (B - Z) * (Z ^ i + c * B) := by ring

/-- `Σ fᵢ Bⁱ ≡ Σ fᵢ Zⁱ (mod B − Z)`, additively. -/
theorem dsum_eq_add_mul {Z B : V} (hZB : Z ≤ B) (f : ℕ → V) (n : ℕ) :
    ∃ C, dsum B f n = dsum Z f n + (B - Z) * C := by
  induction n with
  | zero => exact ⟨0, by rw [dsum_zero, dsum_zero, mul_zero, add_zero]⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨c, hc⟩ := pow_eq_add_mul hZB n
    refine ⟨C + f n * c, ?_⟩
    rw [dsum_succ, dsum_succ, hC, hc]
    ring

/-- **Lemma 2.9.** Let `Z = 2ˢ ≤ B = 2ᵗ`, `m ≤ k` (standard), `2 Z^(m+1) ≤ B`, and digits
`yᵢ < Z` (`i ≤ m`).  Then `Y = Σ_{i≤m} yᵢ Bⁱ` iff (i) `Y = Σ yᵢ Zⁱ + (B − Z) c` for some `c`,
(ii) `Y < Z Bᵐ`, (iii) `NoCarry Y (Σ_{i<k} (B − Z) Bⁱ)`. -/
theorem transfer_iff {s t : V} (hst : s ≤ t) {m k : ℕ} (hmk : m ≤ k)
    (hZB : 2 * Exp.exp s ^ (m + 1) ≤ Exp.exp t) (ys : ℕ → V)
    (hys : ∀ i < m + 1, ys i < Exp.exp s) (Y : V) :
    Y = dsum (Exp.exp t) ys (m + 1) ↔
      ((∃ c, Y = dsum (Exp.exp s) ys (m + 1) + (Exp.exp t - Exp.exp s) * c) ∧
        Y < Exp.exp s * Exp.exp t ^ m ∧ NoCarry Y (mask (Exp.exp t) (Exp.exp s) k)) := by
  have hZ : 0 < Exp.exp s := exp_pos s
  have hB : 0 < Exp.exp t := exp_pos t
  have hZleB : Exp.exp s ≤ Exp.exp t := exp_monotone_le.mpr hst
  have hZ1 : 1 ≤ Exp.exp s := one_le_exp s
  have hZpow : Exp.exp s ≤ Exp.exp s ^ (m + 1) := by
    calc Exp.exp s = Exp.exp s ^ 1 := (pow_one _).symm
      _ ≤ Exp.exp s ^ (m + 1) := pow_le_pow_right₀ hZ1 (by omega)
  have hM : Exp.exp s ^ (m + 1) ≤ Exp.exp t - Exp.exp s := by
    apply le_tsub_of_add_le_right
    calc Exp.exp s ^ (m + 1) + Exp.exp s ≤ Exp.exp s ^ (m + 1) + Exp.exp s ^ (m + 1) :=
          add_le_add (le_refl _) hZpow
      _ = 2 * Exp.exp s ^ (m + 1) := (two_mul _).symm
      _ ≤ Exp.exp t := hZB
  have hMpos : 0 < Exp.exp t - Exp.exp s := lt_of_lt_of_le (pow_pos hZ _) hM
  have hysB : ∀ i < m + 1, ys i < Exp.exp t := fun i hi => lt_of_lt_of_le (hys i hi) hZleB
  constructor
  · intro hY
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := dsum_eq_add_mul hZleB ys (m + 1)
      exact ⟨C, hY.trans hC⟩
    · rw [hY]
      exact dsum_lt_mul hZleB hys
    · rw [noCarry_mask_iff hst]
      intro j _
      by_cases hj : j < m + 1
      · rw [hY, dsum_digit _ hB ys (m + 1) hysB j hj]
        exact hys j hj
      · rw [hY, dsum_div_eq_zero _ hB ys (m + 1) hysB j (by omega), Arithmetic.zero_mod]
        exact hZ
  · rintro ⟨⟨c, hc⟩, hlt, hmask⟩
    obtain ⟨d, hd⟩ : ∃ d : ℕ → V, d = fun i => Y / Exp.exp t ^ i % Exp.exp t := ⟨_, rfl⟩
    have hYB : Y < Exp.exp t ^ (m + 1) := by
      calc Y < Exp.exp s * Exp.exp t ^ m := hlt
        _ ≤ Exp.exp t * Exp.exp t ^ m := mul_le_mul_of_nonneg_right hZleB (Arithmetic.zero_le _)
        _ = Exp.exp t ^ (m + 1) := by ring
    have hYd : Y = dsum (Exp.exp t) d (m + 1) := by
      rw [hd, ← mod_pow_eq_dsum Y _ hB (m + 1), mod_eq_self_of_lt hYB]
    -- every digit of `Y` is below `Z`
    have hmk' := (noCarry_mask_iff hst k Y).mp hmask
    have hdZ : ∀ i < m + 1, d i < Exp.exp s := by
      intro i hi
      by_cases hik : i < k
      · rw [hd]
        show Y / Exp.exp t ^ i % Exp.exp t < Exp.exp s
        exact hmk' i hik
      · have him : i = m := by omega
        have hm : d m < Exp.exp s := by
          rw [hd]
          show Y / Exp.exp t ^ m % Exp.exp t < Exp.exp s
          exact lt_of_le_of_lt (Arithmetic.mod_le _ _) (div_lt_of_lt_mul hlt)
        rw [him]
        exact hm
    -- the same digits read in base `Z` agree with `y`
    obtain ⟨C, hC⟩ := dsum_eq_add_mul hZleB d (m + 1)
    have hDd : dsum (Exp.exp s) d (m + 1) < Exp.exp t - Exp.exp s :=
      lt_of_lt_of_le (dsum_lt _ d _ hdZ) hM
    have hDy : dsum (Exp.exp s) ys (m + 1) < Exp.exp t - Exp.exp s :=
      lt_of_lt_of_le (dsum_lt _ ys _ hys) hM
    have heq : dsum (Exp.exp s) d (m + 1) = dsum (Exp.exp s) ys (m + 1) := by
      have h1 : dsum (Exp.exp s) d (m + 1) + (Exp.exp t - Exp.exp s) * C =
          dsum (Exp.exp s) ys (m + 1) + (Exp.exp t - Exp.exp s) * c :=
        hC.symm.trans (hYd.symm.trans hc)
      have h2 : (dsum (Exp.exp s) d (m + 1) + (Exp.exp t - Exp.exp s) * C) %
            (Exp.exp t - Exp.exp s) =
          (dsum (Exp.exp s) ys (m + 1) + (Exp.exp t - Exp.exp s) * c) %
            (Exp.exp t - Exp.exp s) := by rw [h1]
      rw [mod_add_mul' _ _ hMpos, mod_add_mul' _ _ hMpos, mod_eq_self_of_lt hDd,
        mod_eq_self_of_lt hDy] at h2
      exact h2
    have hdy : ∀ i < m + 1, d i = ys i := by
      intro i hi
      rw [← dsum_digit _ hZ d (m + 1) hdZ i hi, heq, dsum_digit _ hZ ys (m + 1) hys i hi]
    rw [hYd]
    exact dsum_congr _ (m + 1) hdy

/-! ### The code mask `M₁ = Bᴺ − 1 − (b − 1) l` of (4.8) -/

/-- Digits of the code mask: `B − b` at the code positions, `B − 1` elsewhere. -/
def codeMask (b B : V) (pos : ℕ → Prop) [DecidablePred pos] (j : ℕ) : V :=
  if pos j then B - b else B - 1

/-- Digits of `l`: one at the code positions, zero elsewhere. -/
def codeInd (pos : ℕ → Prop) [DecidablePred pos] (j : ℕ) : V := if pos j then 1 else 0

theorem codeMask_dsum {b B : V} (hb : 1 ≤ b) (hbB : b ≤ B) (pos : ℕ → Prop)
    [DecidablePred pos] (n : ℕ) :
    dsum B (codeMask b B pos) n + (b - 1) * dsum B (codeInd pos) n + 1 = B ^ n := by
  have hB1 : 1 ≤ B := le_trans hb hbB
  have hdig : ∀ j, codeMask b B pos j + (b - 1) * codeInd pos j = B - 1 := by
    intro j
    unfold codeMask codeInd
    split_ifs
    · rw [mul_one]
      apply eq_tsub_of_add_eq
      calc B - b + (b - 1) + 1 = B - b + (b - 1 + 1) := by ring
        _ = B := by rw [tsub_add_cancel_of_le hb, tsub_add_cancel_of_le hbB]
    · rw [mul_zero, add_zero]
  induction n with
  | zero => rw [dsum_zero, dsum_zero, mul_zero, add_zero, zero_add, pow_zero]
  | succ n ih =>
    rw [dsum_succ, dsum_succ, pow_succ]
    calc dsum B (codeMask b B pos) n + codeMask b B pos n * B ^ n +
          (b - 1) * (dsum B (codeInd pos) n + codeInd pos n * B ^ n) + 1
        = (dsum B (codeMask b B pos) n + (b - 1) * dsum B (codeInd pos) n + 1) +
            (codeMask b B pos n + (b - 1) * codeInd pos n) * B ^ n := by ring
      _ = B ^ n + (B - 1) * B ^ n := by rw [ih, hdig n]
      _ = ((B - 1) + 1) * B ^ n := by ring
      _ = B ^ n * B := by rw [tsub_add_cancel_of_le hB1, mul_comm]

/-- `Σ_{j<n} (codeMask)ⱼ Bʲ = Bⁿ − 1 − (b − 1) Σ_{j<n} (codeInd)ⱼ Bʲ`. -/
theorem codeMask_eq_sub {b B : V} (hb : 1 ≤ b) (hbB : b ≤ B) (pos : ℕ → Prop)
    [DecidablePred pos] (n : ℕ) :
    dsum B (codeMask b B pos) n = B ^ n - 1 - (b - 1) * dsum B (codeInd pos) n := by
  apply eq_tsub_of_add_eq
  apply eq_tsub_of_add_eq
  exact codeMask_dsum hb hbB pos n

/-- **(4.8), digitwise** (Lemmas 2.7, 2.11): for `b = 2ᵏ ≤ B = 2ᵗ` and `g < Bⁿ`, no carry
against the code mask iff the digits of `g` are `< b` at the code positions and vanish
elsewhere. -/
theorem noCarry_code_iff {k t : V} (hkt : k ≤ t) (n : ℕ) (pos : ℕ → Prop) [DecidablePred pos]
    (g : V) (hg : g < Exp.exp t ^ n) :
    NoCarry g (dsum (Exp.exp t) (codeMask (Exp.exp k) (Exp.exp t) pos) n) ↔
      ∀ j < n, (pos j → g / Exp.exp t ^ j % Exp.exp t < Exp.exp k) ∧
        (¬ pos j → g / Exp.exp t ^ j % Exp.exp t = 0) := by
  have hB : 0 < Exp.exp t := exp_pos t
  have hgd : g = dsum (Exp.exp t) (fun i => g / Exp.exp t ^ i % Exp.exp t) n := by
    rw [← mod_pow_eq_dsum g _ hB n, mod_eq_self_of_lt hg]
  have hm : ∀ j < n, codeMask (Exp.exp k) (Exp.exp t) pos j < Exp.exp t := by
    intro j _
    unfold codeMask
    split_ifs
    · exact tsub_lt_self hB (exp_pos k)
    · exact tsub_lt_self hB (by simp)
  have key : NoCarry g (dsum (Exp.exp t) (codeMask (Exp.exp k) (Exp.exp t) pos) n) ↔
      ∀ j < n, NoCarry (g / Exp.exp t ^ j % Exp.exp t) (codeMask (Exp.exp k) (Exp.exp t) pos j) := by
    have h := noCarry_dsum_iff t (fun i => g / Exp.exp t ^ i % Exp.exp t)
      (codeMask (Exp.exp k) (Exp.exp t) pos) n (fun i _ => mod_lt _ hB) hm
    rw [← hgd] at h
    exact h
  rw [key]
  constructor
  · intro h j hj
    have hj' := h j hj
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [codeMask, if_pos hp] at hj'
      exact (lt_exp_iff_noCarry hkt (mod_lt _ hB)).mpr ((noCarry_comm _ _).mp hj')
    · rw [codeMask, if_neg hp] at hj'
      exact (eq_zero_iff_noCarry_ones (mod_lt _ hB)).mpr ((noCarry_comm _ _).mp hj')
  · intro h j hj
    by_cases hp : pos j
    · rw [codeMask, if_pos hp]
      exact (noCarry_comm _ _).mp ((lt_exp_iff_noCarry hkt (mod_lt _ hB)).mp ((h j hj).1 hp))
    · rw [codeMask, if_neg hp]
      exact (noCarry_comm _ _).mp
        ((eq_zero_iff_noCarry_ones (mod_lt _ hB)).mp ((h j hj).2 hp))

/-- A digit sum supported on the positions `5^(i+1)` (`i < ν`, all below `N`). -/
theorem dsum_powers (B : V) (ν N : ℕ) (hN : 5 ^ ν < N) (f : ℕ → V)
    (hf : ∀ j, (¬ ∃ i < ν, 5 ^ (i + 1) = j) → f j = 0) :
    dsum B f N = ∑ i ∈ Finset.range ν, f (5 ^ (i + 1)) * B ^ (5 ^ (i + 1)) := by
  classical
  have hinj : Set.InjOn (fun i => 5 ^ (i + 1)) (↑(Finset.range ν) : Set ℕ) := by
    intro a _ c _ h
    have h' : a + 1 = c + 1 := Nat.pow_right_injective (show 2 ≤ 5 by omega) h
    omega
  have hsub : (Finset.range ν).image (fun i => 5 ^ (i + 1)) ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    have : 5 ^ (i + 1) ≤ 5 ^ ν := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h1 : ∑ j ∈ (Finset.range ν).image (fun i => 5 ^ (i + 1)), f j * B ^ j =
      ∑ j ∈ Finset.range N, f j * B ^ j := by
    apply Finset.sum_subset hsub
    intro j _ hj
    have hz : f j = 0 := hf j (fun ⟨i, hi, he⟩ =>
      hj (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, he⟩))
    rw [hz, zero_mul]
  unfold dsum
  rw [← h1, Finset.sum_image hinj]

/-- **(4.8) with the mask of (U9)**: `M₁ = Bᴺ − 1 − (b − 1) l`, `l = Σ_{i<ν} B^(5^(i+1))`. -/
theorem noCarry_M1_iff {k t : V} (hkt : k ≤ t) {ν N : ℕ} (hN : 5 ^ ν < N)
    (pos : ℕ → Prop) [DecidablePred pos] (hpos : ∀ j, pos j ↔ ∃ i < ν, 5 ^ (i + 1) = j)
    (g : V) (hg : g < Exp.exp t ^ N) :
    NoCarry g (Exp.exp t ^ N - 1 - (Exp.exp k - 1) *
        ∑ i ∈ Finset.range ν, Exp.exp t ^ (5 ^ (i + 1))) ↔
      ∀ j < N, (pos j → g / Exp.exp t ^ j % Exp.exp t < Exp.exp k) ∧
        (¬ pos j → g / Exp.exp t ^ j % Exp.exp t = 0) := by
  have hl : dsum (Exp.exp t) (codeInd pos) N =
      ∑ i ∈ Finset.range ν, Exp.exp t ^ (5 ^ (i + 1)) := by
    rw [dsum_powers (Exp.exp t) ν N hN (codeInd pos) (fun j hj => by
      unfold codeInd
      rw [if_neg (fun h => hj ((hpos j).mp h))])]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    unfold codeInd
    rw [if_pos ((hpos _).mpr ⟨i, Finset.mem_range.mp hi, rfl⟩), one_mul]
  rw [← hl, ← codeMask_eq_sub (one_le_exp k) (exp_monotone_le.mpr hkt) pos N]
  exact noCarry_code_iff hkt N pos g hg

/-- A number below `Bᴺ` whose digits vanish off the code positions is its code. -/
theorem eq_sum_of_code {t : V} {ν N : ℕ} (hN : 5 ^ ν < N) (pos : ℕ → Prop)
    (hpos : ∀ j, pos j ↔ ∃ i < ν, 5 ^ (i + 1) = j) (g : V) (hg : g < Exp.exp t ^ N)
    (h0 : ∀ j < N, ¬ pos j → g / Exp.exp t ^ j % Exp.exp t = 0) :
    g = ∑ i ∈ Finset.range ν,
      (g / Exp.exp t ^ (5 ^ (i + 1)) % Exp.exp t) * Exp.exp t ^ (5 ^ (i + 1)) := by
  have hB : 0 < Exp.exp t := exp_pos t
  have hgd : g = dsum (Exp.exp t) (fun j => g / Exp.exp t ^ j % Exp.exp t) N := by
    rw [← mod_pow_eq_dsum g _ hB N, mod_eq_self_of_lt hg]
  calc g = dsum (Exp.exp t) (fun j => g / Exp.exp t ^ j % Exp.exp t) N := hgd
    _ = ∑ i ∈ Finset.range ν,
          (g / Exp.exp t ^ (5 ^ (i + 1)) % Exp.exp t) * Exp.exp t ^ (5 ^ (i + 1)) :=
        dsum_powers (Exp.exp t) ν N hN (fun j => g / Exp.exp t ^ j % Exp.exp t) (fun j hj => by
          show g / Exp.exp t ^ j % Exp.exp t = 0
          by_cases hjN : j < N
          · exact h0 j hjN (fun hp => hj ((hpos j).mp hp))
          · rw [div_eq_zero_of_lt _ (lt_of_lt_of_le hg
              (pow_le_pow_right₀ (one_le_exp t) (by omega))), Arithmetic.zero_mod])

/-! ### The digit test (4.9)–(4.11) -/

/-- For digits `0 < dᵢ < B = 2^(κ+1)` (`i < n`) and `L < n`:
`NoCarry (2 Σ dᵢ Bⁱ) (2 (2^κ − 1) B^L) ↔ d_L = 2^κ`. -/
theorem noCarry_shifted_iff {κ : V} {n L : ℕ} (hL : L < n) (d : ℕ → V)
    (hd0 : ∀ i < n, 0 < d i) (hd : ∀ i < n, d i < Exp.exp (κ + 1)) :
    NoCarry (2 * dsum (Exp.exp (κ + 1)) d n) (2 * ((Exp.exp κ - 1) * Exp.exp (κ + 1) ^ L)) ↔
      d L = Exp.exp κ := by
  have hB : 0 < Exp.exp (κ + 1) := exp_pos _
  have hc : Exp.exp κ - 1 < Exp.exp (κ + 1) :=
    lt_of_le_of_lt tsub_le_self (exp_monotone.mpr (lt_add_one κ))
  rw [noCarry_two_mul, noCarry_block L _ _ hc, dsum_digit _ hB d n hd L hL]
  exact (eq_exp_iff_noCarry (hd0 L hL) (by rw [← exp_succ]; exact hd L hL)).symm

end DiophantineConsistency.ModelDigitTransfer
