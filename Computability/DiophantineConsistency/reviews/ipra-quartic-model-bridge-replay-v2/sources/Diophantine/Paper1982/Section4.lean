import Diophantine.Paper1982.Coding

/-!
# Jones 1982, §4: digit-level lemmas for the universal systems

The base is `B = b^(δ+1) = 2^t`; `λ = Σ_{i<4L} Bⁱ` is read off from (U4); the mask `θλ` of
(4.4) is `mask29 B (2z) (4L)`; (4.9)–(4.11): with `H = −c^δ D₀ = Σ_{i<8L} hᵢ Bⁱ` and
`|hᵢ| < B/2`, the number `S₃ = 2H(B) + Bλ(1 + q⁴) = 2 Σ_{i<8L} (hᵢ + B/2) Bⁱ` has the base-`B`
digits `hᵢ + B/2`, and `τ₂(S₃, (B−2)q) = 0` iff the digit at `L` is `B/2`, i.e. `h_L = 0`
(Lemmas 2.4, 2.8, 2.10).
-/

namespace Jones1982

open Polynomial Finset

/-! ### Geometric sums and masks -/

/-- (U4) determines `λ`: from `λ + Bⁿ = 1 + λB` (`B ≥ 2`), `λ = Σ_{i<n} Bⁱ`. -/
theorem geom_of_eq {B lam n : ℕ} (hB : 2 ≤ B) (h : lam + B ^ n = 1 + lam * B) :
    lam = ∑ i ∈ range n, B ^ i := by
  have hg := geom_sum_mul_add (B - 1) n
  rw [Nat.sub_add_cancel (by omega)] at hg
  have h1 : lam * (B - 1) + 1 = B ^ n := by
    rw [Nat.mul_sub, mul_one]
    have : lam ≤ lam * B := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h2 : lam * (B - 1) = (∑ i ∈ range n, B ^ i) * (B - 1) := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) h2

theorem mask29_add (B z k₁ k₂ : ℕ) :
    mask29 B z (k₁ + k₂) = mask29 B z k₁ + mask29 B z k₂ * B ^ k₁ := by
  unfold mask29
  rw [List.replicate_add, Nat.ofDigits_append, List.length_replicate, mul_comm]

/-- `ofDigits b (map f (range n)) = Σ_{j<n} f j b^j`. -/
theorem ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) :
    ∀ n : ℕ, Nat.ofDigits b ((List.range n).map f) = ∑ j ∈ range n, f j * b ^ j
  | 0 => by simp [Nat.ofDigits]
  | n + 1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_map_range b f n,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    ring

/-- The integer version, with nonnegative integer digits. -/
theorem ofDigits_map_range_int (b : ℕ) (f : ℕ → ℤ) (hf : ∀ i, 0 ≤ f i) :
    ∀ n : ℕ, ((Nat.ofDigits b ((List.range n).map fun i => (f i).toNat) : ℕ) : ℤ) =
      ∑ j ∈ range n, f j * (b : ℤ) ^ j
  | 0 => by simp [Nat.ofDigits]
  | n + 1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, Finset.sum_range_succ,
      ← ofDigits_map_range_int b f hf n]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    push_cast
    rw [Int.toNat_of_nonneg (hf n)]
    ring

theorem τ_zero_right (a : ℕ) : τ 2 a 0 = 0 := by
  rw [τ_two_eq_zero_iff, Nat.and_zero]

theorem τ_zero_left (a : ℕ) : τ 2 0 a = 0 := by
  rw [τ_comm]; exact τ_zero_right a

/-! ### Extracting one base-`B` digit (Lemma 2.10 twice) -/

/-- For `B = 2ᵗ` (`t ≥ 1`): `τ₂(E, (B/2 − 1) B^L) = 0` iff `τ₂(d, B/2 − 1) = 0` for the
`L`-th base-`B` digit `d` of `E`. -/
theorem tau_block {t : ℕ} (ht : 1 ≤ t) (L E : ℕ) :
    τ 2 E ((2 ^ (t - 1) - 1) * (2 ^ t) ^ L) = 0 ↔
      τ 2 (E / (2 ^ t) ^ L % 2 ^ t) (2 ^ (t - 1) - 1) = 0 := by
  have hBL : (2 ^ t) ^ L = 2 ^ (t * L) := by rw [← pow_mul]
  have hB : 0 < 2 ^ t := by positivity
  have hBLpos : 0 < (2 ^ t) ^ L := by positivity
  have hhalf : 2 ^ (t - 1) - 1 < 2 ^ t := by
    have : 2 ^ (t - 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 0 < 2 ^ (t - 1) := by positivity
    omega
  rw [hBL]
  have hBLpos' : 0 < 2 ^ (t * L) := by positivity
  -- first split at `B^L`
  have e1 : E = E % 2 ^ (t * L) + (E / 2 ^ (t * L)) * 2 ^ (t * L) := by
    have := Nat.div_add_mod E (2 ^ (t * L)); rw [mul_comm (2 ^ (t * L))] at this; omega
  have e2 : (2 ^ (t - 1) - 1) * 2 ^ (t * L) = 0 + (2 ^ (t - 1) - 1) * 2 ^ (t * L) := by ring
  rw [e2]
  conv_lhs => rw [e1]
  rw [← lemma_2_10 (Nat.mod_lt _ hBLpos') (by positivity)]
  rw [τ_zero_right]
  -- then split the quotient at `B`
  have e3 : E / 2 ^ (t * L) = E / 2 ^ (t * L) % 2 ^ t + (E / 2 ^ (t * L) / 2 ^ t) * 2 ^ t := by
    have := Nat.div_add_mod (E / 2 ^ (t * L)) (2 ^ t); rw [mul_comm (2 ^ t)] at this; omega
  have e4 : 2 ^ (t - 1) - 1 = (2 ^ (t - 1) - 1) + 0 * 2 ^ t := by ring
  constructor
  · rintro ⟨-, h⟩
    rw [e3, e4, ← lemma_2_10 (Nat.mod_lt _ hB) hhalf] at h
    exact h.1
  · intro h
    refine ⟨rfl, ?_⟩
    rw [e3, e4, ← lemma_2_10 (Nat.mod_lt _ hB) hhalf]
    exact ⟨h, τ_zero_right _⟩

/-- Lemma 2.8 in the form used: a digit `0 < d < B = 2ᵗ` satisfies `τ₂(d, B/2 − 1) = 0` iff
`d = B/2`. -/
theorem digit_iff {t d : ℕ} (ht : 1 ≤ t) (hd0 : 0 < d) (hd : d < 2 ^ t) :
    τ 2 d (2 ^ (t - 1) - 1) = 0 ↔ d = 2 ^ (t - 1) :=
  (lemma_2_8 ht hd0 hd).symm

/-! ### The number `Σ_{i<n} (hᵢ + B/2) Bⁱ` -/

/-- (4.9)–(4.11): for `B = 2ᵗ` and coefficients `|hᵢ| < B/2` (`i < n`), with `L < n`,
`τ₂(2 Σ_{i<n} (hᵢ + B/2) Bⁱ, 2 (B/2 − 1) B^L) = 0 ⟺ h_L = 0`. -/
theorem tau_shifted_iff {t n L : ℕ} (ht : 1 ≤ t) (hL : L < n) (h : ℕ → ℤ)
    (hb : ∀ i < n, |h i| < 2 ^ (t - 1)) :
    τ 2 (2 * ∑ i ∈ range n, (h i + 2 ^ (t - 1)) * (2 ^ t : ℤ) ^ i).toNat
        (2 * ((2 ^ (t - 1) - 1) * (2 ^ t) ^ L)) = 0 ↔ h L = 0 := by
  have hpos : ∀ i < n, 0 ≤ h i + 2 ^ (t - 1) := fun i hi => by
    have := (abs_lt.1 (hb i hi)).1; linarith
  have hlt : ∀ i < n, h i + 2 ^ (t - 1) < 2 ^ t := fun i hi => by
    have := (abs_lt.1 (hb i hi)).2
    have e : (2 : ℤ) ^ t = 2 * 2 ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    linarith
  -- the digits `dᵢ = hᵢ + B/2` as natural numbers
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℤ, d = fun i => if i < n then h i + 2 ^ (t - 1) else 0 := ⟨_, rfl⟩
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    rw [hd]; dsimp only; split_ifs with hi
    · exact hpos i hi
    · exact le_rfl
  have hdlt : ∀ i, (d i).toNat < 2 ^ t := fun i => by
    rw [hd]; dsimp only; split_ifs with hi
    · rw [Int.toNat_lt (hpos i hi)]; push_cast; exact hlt i hi
    · simp
  obtain ⟨E, hE⟩ : ∃ E : ℕ, E = Nat.ofDigits (2 ^ t) ((List.range n).map fun i => (d i).toNat) :=
    ⟨_, rfl⟩
  have hEZ : (E : ℤ) = ∑ i ∈ range n, (h i + 2 ^ (t - 1)) * (2 ^ t : ℤ) ^ i := by
    rw [hE, ofDigits_map_range_int _ _ hd0]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hd]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have hsum : (2 * ∑ i ∈ range n, (h i + 2 ^ (t - 1)) * (2 ^ t : ℤ) ^ i).toNat = 2 * E := by
    rw [← hEZ]
    have : (2 * (E : ℤ)) = ((2 * E : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  have h24 := lemma_2_4_τ 1 E ((2 ^ (t - 1) - 1) * (2 ^ t) ^ L)
  simp only [pow_one] at h24
  rw [hsum, h24]
  · rw [tau_block ht]
    have hdigit : E / (2 ^ t) ^ L % 2 ^ t = (h L + 2 ^ (t - 1)).toNat := by
      rw [hE, ofDigits_div_pow_mod (by positivity)
        (fun x hx => by
          rw [List.mem_map] at hx
          obtain ⟨i, -, rfl⟩ := hx
          exact hdlt i)]
      rw [List.getD_eq_getElem _ _ (by simpa using hL)]
      simp only [List.getElem_map, List.getElem_range]
      rw [hd]; dsimp only; rw [if_pos hL]
    rw [hdigit]
    have h0 : 0 < (h L + 2 ^ (t - 1)).toNat := by
      rw [Int.lt_toNat]; push_cast
      have := (abs_lt.1 (hb L hL)).1; linarith
    have h1 : (h L + 2 ^ (t - 1)).toNat < 2 ^ t := by
      rw [Int.toNat_lt (hpos L hL)]; push_cast; exact hlt L hL
    rw [digit_iff ht h0 h1]
    constructor
    · intro h2
      have := Int.toNat_of_nonneg (hpos L hL)
      rw [h2] at this
      push_cast at this
      linarith
    · intro h2
      rw [h2, zero_add]
      have : ((2 ^ (t - 1) : ℕ) : ℤ) = 2 ^ (t - 1) := by push_cast; rfl
      rw [← this, Int.toNat_natCast]

end Jones1982
