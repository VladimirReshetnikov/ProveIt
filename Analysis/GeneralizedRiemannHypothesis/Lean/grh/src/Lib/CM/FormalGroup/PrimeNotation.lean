import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# Notation at a prime, and elements of prime-power norm at split primes

For primes `p` and `d ≡ 7 mod 8`, the file defines the numbers and sets of exponents attached to `p`
and the imaginary quadratic field `K = ℚ(√-d)`, and computes them when `p` is split, inert or
ramified. For a prime `p` that splits in `K`, it then finds an element whose norm is a power of `p`
and whose conjugate is a unit at the `p`-adic place.

The statements use the following notions, for primes `p` and `d`; from `piPrime_mem_quadInt` on,
`d ≡ 7 mod 8` is assumed, and `quadInt d` is the ring of integers of `K` inside `ℂ`.

* `chiK d p`: the Legendre symbol `(p / d)`; for `d ≡ 7 mod 8` it is `1`, `-1`, `0` when `p` is
  split, inert, ramified in `K`.
* `primeNorm d p`, also written `q_p`: `p ^ 2` if `(p / d) = -1`, and `p` otherwise.
* `ιₚ : ℂ →+* ℂ_[p]`: the embedding given by an instance `PadicPlace p`; the valuation `v` of
  `ℂ_[p]` with `v(p) = 1` is expressed by `‖x‖ = p ^ (-v(x))`.

## Main definitions and results

* `New.piPrime`, `New.piPrimeValuation`: the number `π_p`, which is `√-d` for `p = d` and `p`
  otherwise, and its valuation `v(π_p)`, which is `1 / 2` for `p = d` and `1` otherwise.
* `New.varpiValuation`, `New.gammaPrime`: the numbers `ρ_p = v(π_p) / (q_p - 1)` and
  `γ_p = 1 / (p - 1) - ρ_p`.
* `New.partnerExponents`, `New.positivePartnerExponents`: the sets `I_p°` and `I_p`. The set `I_p°`
  consists of the odd numbers if `p` is inert, of all numbers if `p = d`, and is empty if `p`
  splits; `I_p` consists of its positive elements.
* `New.hasSum_gammaPrime`: `γ_p = v(π_p) ∑_{e ∈ I_p} p⁻ᵉ`.
* `New.piPrime_mul_conj`, `New.norm_piPrime`, `New.norm_piPrime_eq_rpow_pow`: the norm of `π_p` at a
  non-split prime, its valuation, and the relation `v(π_p) = (q_p - 1) ρ_p`.
* `New.exists_mul_conj_eq_pow`: for a prime `p` that splits in `K` there is an `α` in the ring of
  integers with `α ᾱ` a positive power of `p` and `ᾱ` a `p`-adic unit; the proof takes a generator
  of a power of the prime of `K` induced by the `p`-adic place.

## Relation to the literature

Known result: decomposition of primes in `ℚ(√-d)` and elements of prime-power norm at split primes.
The existence of `α` follows from the finiteness of the class group. The numbers `ρ_p`, `γ_p` and
the sets of exponents are notation, and the sum for `γ_p` is a geometric series.
-/

section PrimeNotation

open ComplexConjugate

namespace New
/-- The number `π_p`, as a complex number: `√-d = I * √d` if `p = d`, and `p` otherwise. -/
noncomputable def piPrime (d p : ℕ) : ℂ := if p = d then .I * √d else p

lemma exists_primeNorm_eq_pow (d p : ℕ) [Fact d.Prime] [Fact p.Prime] :
    ∃ e : ℕ, e ≠ 0 ∧ primeNorm d p = p ^ e := by
  by_cases h : chiK d p = -1
  · exact ⟨2, two_ne_zero, by simp [primeNorm, h]⟩
  · exact ⟨1, one_ne_zero, by simp [primeNorm, h]⟩

lemma one_lt_primeNorm (d p : ℕ) [Fact d.Prime] [Fact p.Prime] : 1 < primeNorm d p := by
  grind [exists_primeNorm_eq_pow d p, Nat.one_lt_pow, (Fact.out : p.Prime).one_lt]

/-- For primes `d` and `p`, the prime `p` is coprime to `q_p - 1`, where `q_p = primeNorm d p`. -/
lemma coprime_primeNorm_sub_one (d p : ℕ) [Fact d.Prime] [Fact p.Prime] :
    p.Coprime (primeNorm d p - 1) := by
  obtain ⟨e, he, h_eq⟩ := exists_primeNorm_eq_pow d p
  have h_dvd : p ∣ primeNorm d p := by simp [h_eq, dvd_pow_self p he]
  exact ((Nat.coprime_self_sub_right (one_lt_primeNorm d p).le).2 (by simp)).coprime_dvd_left h_dvd

instance (d p : ℕ) [Fact d.Prime] [Fact p.Prime] : NeZero (primeNorm d p - 1) :=
  ⟨Nat.sub_ne_zero_of_lt (one_lt_primeNorm d p)⟩

/-! ### The numbers `v(π_p)`, `ρ_p` and `γ_p` -/

/-- The valuation `v(π_p)` of the number `π_p = piPrime d p`, with `v(p) = 1`: it is `1 / 2` if
`p = d`, and `1` otherwise (see `New.norm_piPrime`). -/
noncomputable def piPrimeValuation (d p : ℕ) : ℝ := if p = d then 1 / 2 else 1

lemma piPrimeValuation_self (d : ℕ) : piPrimeValuation d d = 1 / 2 := ite_eq_left rfl

lemma piPrimeValuation_of_ne {d p : ℕ} (hd : p ≠ d) : piPrimeValuation d p = 1 := ite_eq_right hd

lemma piPrimeValuation_pos (d p : ℕ) : 0 < piPrimeValuation d p := by
  unfold piPrimeValuation
  positivity

lemma piPrimeValuation_le_one (d p : ℕ) : piPrimeValuation d p ≤ 1 := by
  unfold piPrimeValuation
  split_ifs <;> norm_num

lemma half_le_piPrimeValuation (d p : ℕ) : 1 / 2 ≤ piPrimeValuation d p := by
  grind [piPrimeValuation]

lemma chiK_self (d : ℕ) [Fact d.Prime] : chiK d d = 0 := by
  simpa using chiK_cases d d

lemma ne_of_chiK_ne_zero {d p : ℕ} [Fact d.Prime] (hp : chiK d p ≠ 0) : p ≠ d :=
  fun h ↦ hp (by rw [h, chiK_self])

/-- The number `ρ_p = v(π_p) / (q_p - 1)`, where `v(π_p) = piPrimeValuation d p` and
`q_p = primeNorm d p`. For primes `p` and `d ≡ 7 mod 8` it is `1 / (p - 1)`, `1 / (p² - 1)`,
`1 / (2 p - 2)` when `p` is split, inert, ramified in `ℚ(√-d)`. -/
noncomputable def varpiValuation (d p : ℕ) [Fact d.Prime] : ℝ :=
  piPrimeValuation d p / (primeNorm d p - 1)

lemma varpiValuation_of_split {d p : ℕ} [Fact d.Prime] (h_split : chiK d p = 1) :
    varpiValuation d p = 1 / (p - 1) := by
  have hd : p ≠ d := ne_of_chiK_ne_zero (by simp [h_split])
  simp [varpiValuation, primeNorm, h_split, piPrimeValuation_of_ne hd]

lemma varpiValuation_of_inert {d p : ℕ} [Fact d.Prime] (h_inert : chiK d p = -1) :
    varpiValuation d p = 1 / (p ^ 2 - 1) := by
  have hd : p ≠ d := ne_of_chiK_ne_zero (by simp [h_inert])
  simp [varpiValuation, primeNorm, h_inert, piPrimeValuation_of_ne hd]

lemma varpiValuation_self (d : ℕ) [Fact d.Prime] : varpiValuation d d = 1 / (2 * d - 2) := by
  grind [varpiValuation, piPrimeValuation_self d, chiK_self d]

lemma varpiValuation_nonneg (d p : ℕ) [Fact p.Prime] [Fact d.Prime] : 0 ≤ varpiValuation d p :=
  div_nonneg (piPrimeValuation_pos d p).le (sub_nonneg.2 (mod_cast (one_lt_primeNorm d p).le))

/-- For primes `d` and `p`, the number `ρ_p = varpiValuation d p` is at most `1 / (p - 1)`. -/
lemma varpiValuation_le_one_div_sub_one (d p : ℕ) [Fact d.Prime] [Fact p.Prime] :
    varpiValuation d p ≤ 1 / ((p : ℝ) - 1) := by
  have h_le : p ≤ primeNorm d p := by grind [Nat.le_self_pow]
  exact div_le_div₀ zero_le_one (piPrimeValuation_le_one d p)
    (sub_pos.2 (mod_cast (Fact.out : p.Prime).one_lt)) (sub_le_sub_right (mod_cast h_le) 1)

/-- The number `γ_p = 1 / (p - 1) - ρ_p`, where `ρ_p = varpiValuation d p`. For primes `p` and
`d ≡ 7 mod 8` it is `0`, `p / (p² - 1)`, `1 / (2 p - 2)` when `p` is split, inert, ramified in
`ℚ(√-d)`. -/
noncomputable def gammaPrime (d p : ℕ) [Fact d.Prime] : ℝ := 1 / (p - 1) - varpiValuation d p

lemma gammaPrime_of_split {d p : ℕ} [Fact d.Prime] (h_split : chiK d p = 1) :
    gammaPrime d p = 0 := by
  rw [gammaPrime, varpiValuation_of_split h_split, sub_self]

/-- If the prime `p` is inert, that is, `chiK d p = (p / d) = -1`, then `γ_p = p / (p² - 1)`. -/
lemma gammaPrime_of_inert {d p : ℕ} [Fact d.Prime] [Fact p.Prime] (h_inert : chiK d p = -1) :
    gammaPrime d p = p / (p ^ 2 - 1) := by
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have h_sq : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  grind [gammaPrime, varpiValuation_of_inert h_inert]

lemma gammaPrime_self (d : ℕ) [Fact d.Prime] : gammaPrime d d = 1 / (2 * d - 2) := by
  have hd : (1 : ℝ) < d := mod_cast (Fact.out : d.Prime).one_lt
  grind [gammaPrime, varpiValuation_self d]

lemma gammaPrime_nonneg (d p : ℕ) [Fact d.Prime] [Fact p.Prime] : 0 ≤ gammaPrime d p :=
  sub_nonneg.2 (varpiValuation_le_one_div_sub_one d p)

lemma gammaPrime_le_one_div (d p : ℕ) [Fact d.Prime] [Fact p.Prime] :
    gammaPrime d p ≤ 1 / ((p : ℝ) - 1) :=
  sub_le_self _ (varpiValuation_nonneg d p)

lemma gammaPrime_le_one (d p : ℕ) [Fact d.Prime] [Fact p.Prime] : gammaPrime d p ≤ 1 := by
  have hp : (2 : ℝ) ≤ p := mod_cast (Fact.out : p.Prime).two_le
  exact (gammaPrime_le_one_div d p).trans (div_le_one_of_le₀ (by linarith) (by linarith))

/-! ### The sets `I_p°` and `I_p` of exponents -/

/-- The set `I_p°` of exponents at a prime `p`: the odd numbers if the Legendre symbol `chiK d p` is
`-1`, all numbers if `p = d`, and none otherwise; for `d ≡ 7 mod 8` these cases are `p` inert,
ramified, split in `ℚ(√-d)`. The partners of an infinite place `τ` are the places `-p ^ e τ`
(`New.Parameters.partner`) with `e` in this set. -/
def partnerExponents (d p : ℕ) [Fact d.Prime] : Set ℕ := {e : ℕ | p = d ∨ chiK d p = -1 ∧ Odd e}

/-- The set `I_p` of the positive elements of `I_p° = partnerExponents d p`: the odd numbers if
`chiK d p = -1`, all positive numbers if `p = d`, and none otherwise. -/
def positivePartnerExponents (d p : ℕ) [Fact d.Prime] : Set ℕ :=
  {e : ℕ | 0 < e ∧ e ∈ partnerExponents d p}

lemma mem_partnerExponents {d p e : ℕ} [Fact d.Prime] :
    e ∈ partnerExponents d p ↔ p = d ∨ chiK d p = -1 ∧ Odd e := Iff.rfl

lemma mem_positivePartnerExponents {d p e : ℕ} [Fact d.Prime] :
    e ∈ positivePartnerExponents d p ↔ 0 < e ∧ e ∈ partnerExponents d p := Iff.rfl

noncomputable instance (d p : ℕ) [Fact d.Prime] : DecidablePred (· ∈ partnerExponents d p) :=
  fun _ ↦ decidable_of_iff _ mem_partnerExponents.symm

noncomputable instance (d p : ℕ) [Fact d.Prime] :
    DecidablePred (· ∈ positivePartnerExponents d p) :=
  fun _ ↦ decidable_of_iff _ mem_positivePartnerExponents.symm

lemma chiK_ne_one_of_mem_partnerExponents {d p e : ℕ} [Fact d.Prime]
    (he : e ∈ partnerExponents d p) : chiK d p ≠ 1 := by
  obtain rfl | ⟨h_inert, -⟩ := he <;> simp [↓chiK_self, *]

lemma one_mem_positivePartnerExponents {d p : ℕ} [Fact d.Prime] [Fact p.Prime]
    (hp : chiK d p ≠ 1) : 1 ∈ positivePartnerExponents d p := by
  obtain ⟨hd, -⟩ | ⟨-, h_split | h_inert⟩ := chiK_cases d p <;>
    simp_all [mem_positivePartnerExponents, mem_partnerExponents]

lemma partnerExponents_of_inert {d p : ℕ} [Fact d.Prime] (h_inert : chiK d p = -1) :
    partnerExponents d p = {e : ℕ | Odd e} := by
  simp [partnerExponents, h_inert, ne_of_chiK_ne_zero (d := d) (p := p) (by simp [h_inert])]

lemma positivePartnerExponents_of_split {d p : ℕ} [Fact d.Prime] (h_split : chiK d p = 1) :
    positivePartnerExponents d p = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, he⟩ ↦ chiK_ne_one_of_mem_partnerExponents he h_split

/-- For primes `d` and `p`, the number `(1 - χ_K(p) ^ e) / 2` is `v(π_p)` if `e ∈ I_p`, and `0`
otherwise. Here `χ_K(p) = chiK d p` is the Legendre symbol `(p / d)`,
`v(π_p) = piPrimeValuation d p` and `I_p = positivePartnerExponents d p`. -/
lemma one_sub_chiK_pow_div_two (d p e : ℕ) [Fact d.Prime] [Fact p.Prime] :
    ((1 - chiK d p ^ e) / 2 : ℝ) =
      if e ∈ positivePartnerExponents d p then piPrimeValuation d p else 0 := by
  simp only [mem_positivePartnerExponents, mem_partnerExponents, piPrimeValuation]
  obtain ⟨hd, h_zero⟩ | ⟨hd, h_split | h_inert⟩ := chiK_cases d p
  · rw [h_zero]
    cases e <;> simp [hd]
  · simp [hd, h_split]
  · obtain he | he := e.even_or_odd
    · simp [hd, h_inert, he.neg_one_pow, Nat.not_odd_iff_even.2 he]
    · simp [hd, h_inert, he.neg_one_pow, he, he.pos]

/-- For primes `d` and `p`, the number `γ_p = gammaPrime d p` (defined as
`1 / (p - 1) - varpiValuation d p`) equals the sum of `v(π_p) p⁻ᵉ` over
`e ∈ I_p = positivePartnerExponents d p`. Here `v(π_p) = piPrimeValuation d p` is `1/2` if `p = d`
and `1` otherwise. `I_p` consists of the positive odd numbers if `chiK d p = -1`, of all positive
numbers if `p = d`, and is empty otherwise (for `d ≡ 7 mod 8`: `p` inert, ramified, split in
`ℚ(√-d)`). -/
lemma hasSum_gammaPrime (d p : ℕ) [Fact d.Prime] [Fact p.Prime] :
    HasSum
      (fun e : ℕ ↦ if e ∈ positivePartnerExponents d p then piPrimeValuation d p / p ^ e else 0)
      (gammaPrime d p) := by
  -- With `χ = chiK d p`, the `e`-th term is `(p⁻¹ ^ e - (χ / p) ^ e) / 2`: half the difference
  -- of two geometric series.
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have h_inv : |(p : ℝ)⁻¹| < 1 := by simp [inv_lt_one_of_one_lt₀ hp]
  have h_quot : |(chiK d p / p : ℝ)| < 1 := by
    obtain ⟨-, hχ⟩ | ⟨-, hχ | hχ⟩ := chiK_cases d p <;>
      simp [hχ, neg_div, inv_lt_one_of_one_lt₀ hp]
  have h_term (e : ℕ) :
      (if e ∈ positivePartnerExponents d p then piPrimeValuation d p / p ^ e else 0) =
        ((p : ℝ)⁻¹ ^ e - (chiK d p / p) ^ e) / 2 := by
    rw [← zero_div ((p : ℝ) ^ e), ← ite_div, ← one_sub_chiK_pow_div_two, div_pow, inv_pow]
    ring
  have h_value : gammaPrime d p = ((1 - (p : ℝ)⁻¹)⁻¹ - (1 - chiK d p / p : ℝ)⁻¹) / 2 := by
    have h_sq : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    obtain ⟨rfl, h_zero⟩ | ⟨-, h_split | h_inert⟩ := chiK_cases d p
    · rw [gammaPrime_self, h_zero]
      grind
    · simp [gammaPrime_of_split h_split, h_split]
    · rw [gammaPrime_of_inert h_inert, h_inert]
      grind
  simp only [h_term, h_value]
  exact ((hasSum_geometric_of_abs_lt_one h_inv).sub
    (hasSum_geometric_of_abs_lt_one h_quot)).div_const 2

/-- For primes `d` and `p` and a real number `c`, the sum of `c p⁻ᵉ` over
`e ∈ I_p = positivePartnerExponents d p` is `c γ_p / v(π_p)`, where `γ_p = gammaPrime d p` and
`v(π_p) = piPrimeValuation d p`. -/
lemma hasSum_div_pow_positivePartnerExponents (d p : ℕ) [Fact d.Prime] [Fact p.Prime] (c : ℝ) :
    HasSum (fun e : ℕ ↦ if e ∈ positivePartnerExponents d p then (c / p ^ e : ℝ) else 0)
      (c * gammaPrime d p / piPrimeValuation d p) := by
  exact (((hasSum_gammaPrime d p).mul_left c).div_const (piPrimeValuation d p)).congr_fun
    (by grind [piPrimeValuation_pos d p])

/-! ### The norm and the valuation of `π_p` -/

lemma piPrime_mem_quadInt (d : ℕ) {p : ℕ} [PrimeSevenModEight d] : piPrime d p ∈ quadInt d := by
  unfold piPrime
  split_ifs
  exacts [I_mul_sqrt_mem_quadInt d, natCast_mem _ p]

lemma piPrime_ne_zero (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] :
    piPrime d p ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  unfold piPrime
  split_ifs <;> simp_all

/-- For primes `p` and `d ≡ 7 mod 8` such that `p` does not split in `K = ℚ(√-d)`, that is,
with Legendre symbol `chiK d p = (p / d) ≠ 1`, the number `π_p = piPrime d p` (which is `√-d` if
`p = d` and `p` otherwise) has the norm `q_p = primeNorm d p`, which is `p ^ 2` if `p` is inert
and `p` if it ramifies. -/
lemma piPrime_mul_conj (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]
    (hp : chiK d p ≠ 1) : piPrime d p * conj (piPrime d p) = primeNorm d p := by
  obtain ⟨rfl, h_zero⟩ | ⟨hd, h_one | h_neg_one⟩ := chiK_cases d p
  · simp [piPrime, primeNorm, ↓h_zero, Complex.ext_iff, Real.mul_self_sqrt p.cast_nonneg]
  · exact absurd h_one hp
  · simp [piPrime, primeNorm, hd, h_neg_one, sq]

/-- Under the embedding `ιₚ : ℂ →+* ℂ_[p]` given by a `PadicPlace p`, the number `π_p` (`√-d` if
`p = d`, else `p`) has valuation `piPrimeValuation d p`, which is `1 / 2` for `p = d` and `1`
otherwise. -/
lemma norm_piPrime (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p] :
    ‖ιₚ (piPrime d p)‖ = p ^ (-piPrimeValuation d p) := by
  obtain rfl | hd := eq_or_ne p d
  · have h_norm_sq : ‖ιₚ (piPrime p p)‖ ^ 2 = ((p : ℝ) ^ (-piPrimeValuation p p)) ^ 2 :=
      calc
        _ = ‖-(p : ℂ_[p])‖ := by rw [piPrime, ite_eq_left rfl, ← norm_pow, map_I_mul_sqrt_sq]
        _ = (p : ℝ) ^ (-1 : ℝ) := by rw [norm_neg, norm_p_eq_inv, Real.rpow_neg_one]
        _ = _ := by norm_num [← Real.rpow_mul_natCast p.cast_nonneg, piPrimeValuation_self]
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h_norm_sq
  · rw [piPrime, ite_eq_right hd, map_natCast, norm_p_eq_inv, piPrimeValuation_of_ne hd,
      Real.rpow_neg_one]

lemma norm_piPrime_lt_one (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p] :
    ‖ιₚ (piPrime d p)‖ < 1 := by
  rw [norm_piPrime]
  exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast (Fact.out : p.Prime).one_lt)
    (neg_lt_zero.2 (piPrimeValuation_pos d p))

/-- With `v` the valuation given by the `p`-adic embedding `ιₚ`, so that `‖ιₚ x‖ = p ^ (-v(x))`,
one has `v(π_p) = (q_p - 1) ρ_p`. Here `π_p = piPrime d p` is `√-d` if `p = d` and `p` otherwise,
`q_p = primeNorm d p` is `p ^ 2` if `p` is inert in `ℚ(√-d)` and `p` otherwise, and
`ρ_p = varpiValuation d p`, for a prime `d ≡ 7 mod 8`. -/
lemma norm_piPrime_eq_rpow_pow (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]
    [PadicPlace p] :
    ‖ιₚ (piPrime d p)‖ = ((p : ℝ) ^ (-varpiValuation d p)) ^ (primeNorm d p - 1) := by
  have hq : (1 : ℝ) < primeNorm d p := mod_cast one_lt_primeNorm d p
  have h_exponent :
      -varpiValuation d p * ((primeNorm d p - 1 : ℕ) : ℝ) = -piPrimeValuation d p := by
    rw [Nat.cast_pred (zero_lt_one.trans (one_lt_primeNorm d p)), varpiValuation, neg_mul,
      div_mul_cancel₀ _ (sub_pos.2 hq).ne']
  rw [norm_piPrime, ← Real.rpow_mul_natCast p.cast_nonneg, h_exponent]

/-- The image `ιₚ π_p` of the number `π_p` in the ring of integers of `ℂ_p`, for the `p`-adic
place that is given by the instance `PadicPlace p`. -/
noncomputable def piPrimeInt (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]
    [PadicPlace p] : valRingCp p := ⟨ιₚ (piPrime d p), (norm_piPrime_lt_one d).le⟩

lemma coe_piPrimeInt (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p] :
    (piPrimeInt d : ℂ_[p]) = ιₚ (piPrime d p) := rfl

lemma norm_piPrimeInt (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p] :
    ‖((piPrimeInt d : valRingCp p) : ℂ_[p])‖ = p ^ (-piPrimeValuation d p) :=
  norm_piPrime d

/-- In `valRingCp p`, the ring of integers of `ℂ_p`, the image `piPrimeInt d` of the number `π_p`
(`√-d` if `p = d`, and `p` otherwise; the prime `p` is implicit in the notation) divides `p`. -/
lemma piPrimeInt_dvd_natCast (d : ℕ) {p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]
    [PadicPlace p] : piPrimeInt d ∣ (p : valRingCp p) := by
  obtain rfl | hd := eq_or_ne p d
  · have h_sq : ιₚ (piPrime p p) ^ 2 = -p := by rw [piPrime, ite_eq_left rfl, map_I_mul_sqrt_sq]
    exact ⟨-piPrimeInt p, Subtype.ext (by simp [coe_piPrimeInt, ← sq, h_sq])⟩
  · exact ⟨1, Subtype.ext (by simp [coe_piPrimeInt, piPrime, hd])⟩

end New

end PrimeNotation

/-! ## An element of prime-power norm at a split prime -/

section SplitGenerator

open NumberField ComplexConjugate

namespace New
/-- Let `d ≡ 7 mod 8` and `p` be primes with Legendre symbol `chiK d p = (p / d) = 1`, and let `w`
be a prime of `K = QuadField d = ℚ(√-d)` that contains `p`. Then `w` differs from its complex
conjugate `star w`. Here `FinPlace` is the type of nonzero prime ideals of the ring of integers. -/
lemma QuadField.star_ne_of_chiK_eq_one {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]
    (hp : chiK d p = 1) (w : FinPlace (QuadField d))
    (hw : (p : 𝓞 (QuadField d)) ∈ w.asIdeal) : star w ≠ w := by
  intro h_star
  -- The residue field has `p` elements, so `betaK d = (1 + √-d) / 2` is congruent to an integer
  -- `n`. If `w` is its own conjugate, `star (betaK d)` is congruent to `n` too; their difference
  -- `sqrtNegDInt d = √-d` is then in `w`, so `p ∣ d`.
  have h_card : Nat.card (𝓞 (QuadField d) ⧸ w.asIdeal) = p :=
    (q_eq_iff_chiK_ne_neg_one w hw).2 (by simp [hp])
  have : Nontrivial (𝓞 (QuadField d) ⧸ w.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  obtain ⟨n, hn⟩ :
      ∃ n : ℤ, n • (1 : 𝓞 (QuadField d) ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (betaK d) :=
    mem_zmultiples_of_prime_card h_card one_ne_zero
  have h_mem : betaK d - n ∈ w.asIdeal := Ideal.Quotient.eq.1 (by rw [← hn, map_intCast, zsmul_one])
  have h_star_mem : star (betaK d - n) ∈ w.asIdeal := mem_star_place.1 (by rwa [h_star])
  have h_sqrt : sqrtNegDInt d ∈ w.asIdeal := by
    have h_sub : betaK d - n - star (betaK d - n) = sqrtNegDInt d := by simp [star_betaK]; ring
    simpa only [h_sub] using w.asIdeal.sub_mem h_mem h_star_mem
  have h_dvd : p ∣ d := (w.natCast_mem_iff_dvd hw).1
    (by simpa only [sqrtNegDInt_sq, neg_mem_iff] using w.asIdeal.pow_mem_of_mem h_sqrt 2 two_pos)
  exact ne_of_chiK_ne_zero (by simp [hp]) ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h_dvd)

/-- Let `d ≡ 7 mod 8` and `p` be primes with Legendre symbol `chiK d p = (p / d) = 1`, and let
`ιₚ : ℂ →+* ℂ_[p]` be the embedding given by a `p`-adic place. Then there are an exponent `h` and
a number `α` such that `h ≠ 0`, `α` lies in `quadInt d` (the ring of integers of `K = ℚ(√-d)`
inside `ℂ`), `α` has norm `p ^ h`, and `ιₚ (conj α)` is a unit: take a generator of the `h`-th
power of the prime of `K` that `ιₚ` induces. -/
lemma exists_mul_conj_eq_pow {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime] [PadicPlace p]
    (hp : chiK d p = 1) : ∃ (h : ℕ) (α : ℂ),
    h ≠ 0 ∧
    α ∈ quadInt d ∧
    α * conj α = p ^ h ∧
    ‖ιₚ (conj α)‖ = 1 := by
  let σ : QuadField d →+* ℂ_[p] := ιₚ.domRestrict (QuadField d)
  let w : FinPlace (QuadField d) := placeOfEmb σ
  have hw : (p : 𝓞 (QuadField d)) ∈ w.asIdeal := natCast_mem_placeOfEmb σ
  obtain ⟨h, h_ne, a, ha⟩ : ∃ h ≠ 0, ∃ a : 𝓞 (QuadField d), w.asIdeal ^ h = .span {a} :=
    exists_ideal_pow_eq_span_singleton w.asIdeal
  have hq : w.asIdeal.absNorm = p := (QuadField.q_eq_iff_chiK_ne_neg_one w hw).2 (by simp [hp])
  have h_norm : a * star a = p ^ h := by
    rw [← QuadField.absNorm_span_eq_mul_star, ← ha, map_pow, hq, Nat.cast_pow]
  -- If `ā` were in `w`, the conjugate prime would contain `w ^ h` and so be equal to `w`.
  have h_notMem : star a ∉ w.asIdeal := fun h_mem ↦ by
    have h_le : w.asIdeal ^ h ≤ (star w).asIdeal := by simpa [ha] using mem_star_place.2 h_mem
    exact QuadField.star_ne_of_chiK_eq_one hp w hw (IsDedekindDomain.HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le (star w).isPrime.ne_top ((star w).isPrime.le_of_pow_le h_le)).symm)
  have h_unit : ‖σ (star a : 𝓞 (QuadField d))‖ = 1 :=
    (norm_ringOfIntegers_le σ _).eq_of_not_lt (mt (mem_placeOfEmb σ _).2 h_notMem)
  refine ⟨h, (a : QuadField d), h_ne, ⟨a, rfl⟩, ?_, by simpa [σ] using h_unit⟩
  simpa using congr_arg (fun x : 𝓞 (QuadField d) ↦ ((x : QuadField d) : ℂ)) h_norm

end New

end SplitGenerator
