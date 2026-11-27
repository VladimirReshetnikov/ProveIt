import New.Derivatives.Vacuum.IntegralVacuum
import New.Reduction.Zeros.PrimeError

/-!
# Admissible data

Fix parameters `P : New.Parameters`. The data `D : New.Data P` are the objects that grow with the
length `x` of the prime sum: scales, ranks, the field `E`, the `a`-places and `b`-places, weights,
three primes, and numbers read off from them.

Letters used in comments, and the names in the code:

| letter | code |
|---|---|
| `p₀`, `p₁` | `D.levelPrime 0`, `D.levelPrime 1` |
| `π_M`, `π_N` | `star D.piMBar`, `D.piN` |
| `κ(τ)`, `κ_j(τ)` | `D.weight τ`, `D.liftWeight j τ` |
| `s`, `Δ` | `D.towerExp`, `D.gap` |
| `s_∞`, `s_fin` | `D.jetSize`, `D.primeSum` |

## Main definitions and results

* `New.Data`: the data; `New.Parameters.IsSparse` is the condition on the `b`-places. The scales and
  ranks are asked to lie in ranges only. The data with the exact values are
  `New.Parameters.IsAdmissibleData`; they are admissible for large `x`
  (`New.eventually_exists_data_of_isAdmissibleData`). Sizes are compared in the files `Magnitudes`
  and `Sizes` of this folder.
* `New.Parameters.logLevelMin_mem_Icc`: the lower end `N₋` of the range for the level has logarithm
  between `m log b` and `24 m log b`.

Notions from other files:
* `New.Parameters`: a multiple `q₀` of `18480 = 16 · 3 · 5 · 7 · 11` and a prime `d` with
  `d ≡ q₀/2 - 1 mod q₀`; they determine the field `P.K = ℚ(√-d)`.
* `New.towerDeg s`: the number `3 l₀ 2 ^ s`, where `l₀ = New.l₀ s` is, for `s ≥ 1`, the least power
  of `3` above `27 s`. The modulus `P.q₁ s` is `q₀ * towerDeg s`.
* `P.E s`, `P.Φ s`: the field `E = K(ζ)`, with `ζ` a primitive `q₁`-th root of unity, and its
  infinite places, which form a group isomorphic to `(ℤ/q₁)ˣ`.
* `P.q₂ s`: the number `(q₀ d) ^ (s + 6)`.
-/

noncomputable section

open NumberField Set
open Real (exp log)

/-- A bound for the constants that depend on `q₀` and `d` only. It is the sum of the constant
`P.vacuumBoundConst` in the bound for the conjugates of the integral vacuum, `2 d + 6`, `q₀`, the
absolute value of `chowlaSelbergConst d = γ - Re L'/L(1, χ_K)`, and `∑_w |log ‖Φ'(w)‖|`, where `w`
runs over the complex roots of the cyclotomic polynomial `Φ` of order `q₀`. -/
def New.Parameters.constantBound (P : Parameters) : ℝ :=
  P.vacuumBoundConst + (2 * P.d + 6) + (P.q₀ + |chowlaSelbergConst P.d| +
    ∑ w ∈ primitiveRoots P.q₀ ℂ, |log ‖(Polynomial.cyclotomic P.q₀ ℂ).derivative.eval w‖|)

/-- A set `T` of infinite places of `P.E s`, viewed in `(ℤ/q₁)ˣ` with `q₁ = P.q₁ s`, is sparse for
the primes up to `L` if for all primes `ℓ ≤ L` and integers `0 < i < j < l₀ s` there are no places
`σ, τ, ρ` in `T`, distinct or not, with `τ / σ ≡ ± ℓ ^ i` and `ρ / σ ≡ ± ℓ ^ j` modulo the part of
`q₁` prime to `ℓ`. The two signs are independent. -/
def New.Parameters.IsSparse (P : Parameters) (s L : ℕ) (T : Finset (P.Φ s)) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ L → ∀ i j : ℕ, 0 < i → i < j → j < l₀ s →
    let φ : P.Φ s →* (ZMod (ordCompl[ℓ] (P.q₁ s)))ˣ := P.placeClass (Nat.ordCompl_dvd (P.q₁ s) ℓ)
    ¬∃ σ ∈ T, ∃ τ ∈ T, ∃ ρ ∈ T, ∃ ε ε' : ℤˣ,
      (φ (τ / σ)).val = (ε : ℤ) * ℓ ^ i ∧ (φ (ρ / σ)).val = (ε' : ℤ) * ℓ ^ j

/-- The logarithm of `N₋ = κ̄ ^ m (M rd_E / 2π) ^ (m - 1) b ^ (-15 / 2)`, the lower end of the
range for the level. Here `κ̄` is the geometric mean of the weights `κ τ` over the infinite
places `τ` of `E = P.E s`, `rd_E` is the root discriminant of `E`, and `logB = log b`. -/
def New.Parameters.logLevelMin (P : Parameters) (s m : ℕ) (κ : P.Φ s → ℕ) (M : ℕ) (logB : ℝ) : ℝ :=
  m * ((∑ τ : P.Φ s, log (κ τ)) / Core.numInfPlaces (P.E s)) +
    (m - 1) * log (M * rootDiscr (P.E s) / (2 * Real.pi)) - 15 / 2 * logB

/-- The data for the parameters `P`: scales `x`, `x₁`, `b`, the number `m` of lifts, the rank `r`,
the exponent `s` of the field `E = P.E s`, a sparse set of `b`-places with the weights that it
determines, and primes `p₀`, `p₁`, `N` with integers of `K` and of `E` whose products with their
conjugates are `p₀ p₁` and `N`. The scales, `m` and `r` are not fixed: they lie in ranges, `m` and
`r` are powers of `2` and `3`, and `q₁ x₁` divides `b`. `New.eventually_exists_data` constructs data
with explicit `x₁`, `b`, `m`, `r` for every large integer `x`. -/
structure New.Data (P : Parameters) where
  /-- The length `x` of the prime sum, an integer. -/
  natX : ℕ
  /-- The second cut-off `x₁`, an integer. -/
  natX₁ : ℕ
  /-- The weight `b` at the `b`-places, an integer. -/
  natB : ℕ
  /-- The logarithm of `x`. -/
  logX : ℝ
  /-- The logarithm of `x₁`. -/
  logX₁ : ℝ
  /-- The logarithm of `b`. -/
  logB : ℝ
  /-- `logX = log x`. -/
  exp_logX : exp logX = natX
  /-- `logX₁ = log x₁`. -/
  exp_logX₁ : exp logX₁ = natX₁
  /-- `logB = log b`. -/
  exp_logB : exp logB = natB
  /-- `log log b ≥ 10¹² c`, where `c = P.constantBound` bounds the constants that depend on `P`
  only. -/
  constantBound_le : 1e12 * P.constantBound ≤ log logB
  /-- `(log b) ^ 100 ≤ x`. -/
  mul_log_logB_le_logX : 100 * log logB ≤ logX
  /-- `x ^ 10⁶ ≤ x₁`. -/
  logX_le_logX₁ : 1e6 * logX ≤ logX₁
  /-- `x₁ ^ 10⁶ ≤ b`. -/
  logX₁_le_logB : 1e6 * logX₁ ≤ logB
  /-- `(log x₁) ^ 6 ≤ log b`. -/
  log_logX₁_le_log_logB : 6 * log logX₁ ≤ log logB
  /-- The number `m` of lifts in the chain. -/
  m : ℕ
  /-- The rank `r` of the target, that is, of the hermitian spaces `New.Data.spaceW` over `E`. -/
  r : ℕ
  /-- The exponent `s` with `2 ^ s = m ^ 22`; the field is `P.E s`. -/
  towerExp : ℕ
  /-- `m` lies in `[√x, 2 √x]`. -/
  m_mem : (m : ℝ) ∈ Icc (exp (logX / 2)) (2 * exp (logX / 2))
  /-- `r` lies in `[x⁵, 3 x⁵]`. -/
  r_mem : (r : ℝ) ∈ Icc (exp (5 * logX)) (3 * exp (5 * logX))
  /-- `m` is a power of `2` with positive exponent, and `2 ^ s = m ^ 22`. -/
  exists_m_eq_two_pow : ∃ e : ℕ, m = 2 ^ (e + 1) ∧ towerExp = (e + 1) * 22
  /-- `r` is a power of `3` with positive exponent. -/
  exists_r_eq_three_pow : ∃ e : ℕ, r = 3 ^ (e + 1)
  /-- `s ≤ 32 log x`. -/
  towerExp_le : towerExp ≤ 32 * logX
  /-- `b` is a multiple of `q₁ x₁`. -/
  dvd_natB : P.q₁ towerExp * natX₁ ∣ natB
  /-- The set `Φ_b` of `b`-places. -/
  bPlaces : Finset (P.Φ towerExp)
  /-- The `b`-places are `≡ -1` modulo `q₀`. -/
  placeClass_of_mem_bPlaces : ∀ σ ∈ bPlaces,
    P.placeClass (P.q₀.dvd_mul_right (towerDeg towerExp)) σ = -1
  /-- There are at least `towerDeg s / log b` of them; `towerDeg s` is the number of places `≡ 1`
  modulo `q₀`. -/
  towerDeg_le_card_bPlaces_mul : towerDeg towerExp ≤ bPlaces.card * logB
  /-- The `b`-places are sparse for the primes up to `k t`, where `k = r + 1 - m` and `t = 5 r`. -/
  sparse : P.IsSparse towerExp ((r + 1 - m) * (5 * r)) bPlaces
  /-- The weight `κ(τ)` of a place. -/
  weight : P.Φ towerExp → ℕ
  /-- The weight is `b = a / x` at the `b`-places and `a / x₁` elsewhere, where `a = x b`. -/
  weight_eq (τ : P.Φ towerExp) : weight τ = if τ ∈ bPlaces then natB else natX * natB / natX₁
  /-- The two primes `p₀`, `p₁` of the principal level. -/
  levelPrime : Fin 2 → ℕ
  /-- `p₀` and `p₁` are prime. -/
  levelPrime_prime (i : Fin 2) : (levelPrime i).Prime
  /-- `p₀, p₁ ≡ 1` modulo `q₂²`, with `q₂ = P.q₂ s`. -/
  levelPrime_modEq_one_q₂_sq (i : Fin 2) : levelPrime i ≡ 1 [MOD P.q₂ towerExp ^ 2]
  /-- `p₀ ≠ p₁`. -/
  levelPrime_injective : levelPrime.Injective
  /-- `p₀` and `p₁` lie in `[b¹⁰, b¹¹]`. -/
  levelPrime_mem (i : Fin 2) : (levelPrime i : ℝ) ∈ Icc (exp logB ^ 10) (exp logB ^ 11)
  /-- An integer of `K` of norm `M = p₀ p₁`; its conjugate is written `π_M`. -/
  piMBar : 𝓞 P.K
  /-- `piMBar` times its conjugate is `p₀ p₁`. -/
  piMBar_mul_star : piMBar * star piMBar = levelPrime 0 * levelPrime 1
  /-- The level `N`. -/
  N : ℕ
  /-- `N` is prime. -/
  N_prime : N.Prime
  /-- `N ≡ 1` modulo `q₂²`. -/
  N_modEq_one_q₂_sq : N ≡ 1 [MOD P.q₂ towerExp ^ 2]
  /-- `log N₋ ≤ log N ≤ log N₋ + √(log b)`, with `N₋` as in `New.Parameters.logLevelMin`. -/
  log_N_mem : log N ∈ Icc (P.logLevelMin towerExp m weight (levelPrime 0 * levelPrime 1) logB)
    (P.logLevelMin towerExp m weight (levelPrime 0 * levelPrime 1) logB + √logB)
  /-- An integer `π_N` of `E` whose product with its complex conjugate is `N`. -/
  piN : 𝓞 (P.E towerExp)
  /-- `π_N` times its conjugate is `N`. -/
  piN_mul_star : piN * star piN = N

namespace New.Data

variable {P : Parameters} (D : Data P)

/-- The length `x` of the prime sum, as a real number. -/
abbrev x : ℝ := exp D.logX

/-- The second cut-off `x₁`, as a real number. -/
abbrev x₁ : ℝ := exp D.logX₁

/-- The weight `b` at the `b`-places, as a real number. -/
abbrev b : ℝ := exp D.logB

/-- The field `E = K(ζ)`, with `ζ` a primitive root of unity of order `q₁`. -/
@[reducible] def E : Type := P.E D.towerExp deriving NumberField, CharZero, IsCMField

/-- The infinite places of `E`; they form the group `Gal(E/K) = (ℤ/q₁)ˣ`. -/
protected abbrev Φ : Type := InfinitePlace D.E

/-- The order `q₁ = 3 l₀ m ^ 22 q₀` of the root of unity that generates `E` over `K`; here
`l₀ = New.l₀ D.towerExp` and `m ^ 22 = 2 ^ D.towerExp`. -/
abbrev q₁ : ℕ := P.q₁ D.towerExp

/-- The number `f` of infinite places of `E`. -/
abbrev f : ℕ := Core.numInfPlaces D.E

/-- The number `q₁ d`; the field `E` lies in the cyclotomic field of this order. -/
protected abbrev cyclotomicConductor : ℕ := D.q₁ * P.d

/-- The root discriminant `rd_E` of `E`. -/
abbrev rootDisc : ℝ := rootDiscr D.E

/-- The rank `k = r + 1 - m` of the source; the subtraction is exact by `New.Data.r_add_one`. -/
def k : ℕ := D.r + 1 - D.m

/-- The number `t = 5 r`; consecutive ranks `n j` differ by `t + 1`. -/
def t : ℕ := 5 * D.r

/-- Half the gap, `Δ / 2 = r ^ 8`. -/
def halfGap : ℕ := D.r ^ 8

/-- The gap `Δ = 2 r ^ 8` between the weights `D.liftWeight j σ` of consecutive lifts. -/
def gap : ℕ := 2 * D.halfGap

/-- The number `Δ / 2 - (t + 1) / 2`, where `Δ / 2 = D.halfGap`; note that `t` is odd. -/
def reducedHalfGap : ℕ := D.halfGap - (D.t + 1) / 2

/-- The number `a = x b`, called the long order; the sum `D.primeSum` runs over `1 ≤ ν ≤ a`. -/
def a : ℕ := D.natX * D.natB

/-- The weight `a / x₁` at the places outside the set `D.bPlaces` of `b`-places. -/
def offWeight : ℕ := D.a / D.natX₁

/-- The place that corresponds to the class of `j` in `(ℤ/q₁)ˣ` if `j` is prime to `q₁`, and the
identity place otherwise. -/
abbrev placeOfInt (j : ℤ) : D.Φ := P.placeOfInt D.towerExp j

/-- The ranks `n_j = k + j (t + 1)`. -/
def n (j : ℕ) : ℕ := D.k + j * (D.t + 1)

/-- The number `k + j - 1`. In the `j`-th step, `1 ≤ j ≤ m`, of the chain of theta lifts it is the
number of plus signs of the diagonal hermitian space `W_j = New.Data.spaceW` of rank `r` over `E`,
whose signs are `New.Data.signsW`. -/
abbrev posRank (j : ℕ) : ℕ := D.k + j - 1

instance (j : Fin 2) : Fact (D.levelPrime j).Prime := ⟨D.levelPrime_prime j⟩

/-- The principal level `M = p₀ p₁`. -/
def M : ℕ := D.levelPrime 0 * D.levelPrime 1 deriving NeZero

/-- The set `Φ_a` of `a`-places: the places `≡ 1` modulo `q₀`. -/
def aPlaces : Finset D.Φ := {τ : D.Φ | P.placeClass (P.q₀.dvd_mul_right
  (towerDeg D.towerExp)) τ = 1}

/-- The number `κ(σ) + (i + 1) Δ / 2`, where `κ = D.weight` and `Δ / 2 = D.halfGap` is half the
gap. -/
def shiftedWeight (i : ℕ) (σ : D.Φ) : ℕ := D.weight σ + (i + 1) * D.halfGap

/-- The weight `κ_j(σ) = κ(σ) + (j + 1/2) Δ` of the character of the `j`-th lift. -/
def liftWeight (j : ℕ) (σ : D.Φ) : ℕ := D.shiftedWeight (2 * j) σ

/-- The prime sum `s_fin(y, σ) = ∑ Λ_K(ν) (y / ν - κ(-ν σ))₊` over `1 ≤ ν ≤ a`. Here
`Λ_K(ν) = Λ(ν) (1 - χ_K(ν))` is `lambdaKResidueClass P.d 1 ν`, and `-ν σ` is the product of `σ` with
`D.placeOfInt (-ν)`, which is the identity place if `ν` is not prime to `q₁`. -/
def primeSum (y : ℝ) (σ : D.Φ) : ℝ :=
  ∑ ν ∈ Finset.Icc 1 D.a, lambdaKResidueClass P.d 1 ν * (y / ν - D.weight (D.placeOfInt (-ν) * σ))⁺

/-- The unit of loss `f a log³ b`, with `f` the number of infinite places and `a = x b`. -/
abbrev errorUnit : ℝ := D.f * D.a * D.logB ^ 3

/-- The size `s_∞(j) = log j! + j log (M / Ω)` of a derivative of order `j`. Here `M = D.M` and
`Ω = P.bigOmega D.towerExp = exp (γ - Re L'/L(1, χ_K)) 2π / rd_E`. -/
def jetSize (j : ℕ) : ℝ := log j.factorial + j * log (D.M / P.bigOmega D.towerExp)

/-- The direction amount `∑_σ (s_∞(κ(σ)) - s_fin(κ(σ), σ))`, summed over all infinite places `σ`:
the size `s_∞ = D.jetSize` of a derivative of order `κ(σ)`, less the prime sum `s_fin = D.primeSum`
that measures its guaranteed divisibility. -/
def directionAmount : ℝ := ∑ σ : D.Φ, (D.jetSize (D.weight σ) - D.primeSum (D.weight σ) σ)

end New.Data

/-! ## The size of `N₋`

The bounds for `N₋` do not involve the level `N`, so they can be used to construct it. -/

namespace New

open Real Module

/-- The root discriminant of a number field is at least `1`. -/
lemma one_le_rootDiscr (K : Type*) [Field K] [NumberField K] : 1 ≤ rootDiscr K := by
  have h_one : (1 : ℝ) ≤ |(discr K : ℝ)| := mod_cast Int.one_le_abs (discr_ne_zero K)
  rw [rootDiscr_def, Int.cast_abs]
  exact one_le_rpow h_one (by positivity)

/-- If a positive integer `c` lies in the different of the number field `K`, then the root
discriminant of `K` lies between `1` and `c`. -/
lemma rootDiscr_mem_Icc {K : Type*} [Field K] [NumberField K] {c : ℕ} (hc : c ≠ 0)
    (h_mem : (c : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K)) : rootDiscr K ∈ Icc (1 : ℝ) c := by
  refine ⟨one_le_rootDiscr K, ?_⟩
  -- the norm of the different is `|discr K|`, and it divides the norm `c ^ [K : ℚ]` of `c`
  have h_dvd : (discr K).natAbs ∣ c ^ finrank ℚ K := by
    rw [← absNorm_differentIdeal K (𝓞 K), ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h_mem)
  have h_le : |(discr K : ℝ)| ≤ (c : ℝ) ^ (finrank ℚ K : ℝ) := by
    rw [rpow_natCast, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Nat.le_of_dvd (by positivity) h_dvd
  rw [rootDiscr_def, Int.cast_abs, rpow_inv_le_iff_of_pos (by positivity) c.cast_nonneg
    (mod_cast finrank_pos)]
  exact h_le

/-- If real numbers `κ i`, indexed by a nonempty finite type, lie in `[1, exp L]`, then the mean of
their logarithms lies in `[0, L]`. -/
lemma sum_log_div_card_mem_Icc {ι : Type*} [Fintype ι] [Nonempty ι] {κ : ι → ℝ} {L : ℝ}
    (hκ : ∀ i : ι, κ i ∈ Icc 1 (exp L)) :
    (∑ i : ι, log (κ i)) / Fintype.card ι ∈ Icc 0 L := by
  have h_card : (0 : ℝ) < Fintype.card ι := mod_cast Fintype.card_pos
  have h_log (i : ι) : log (κ i) ∈ Icc 0 L := by
    obtain ⟨h_lower, h_upper⟩ := hκ i
    exact ⟨log_nonneg h_lower, (log_le_iff_le_exp (by positivity)).2 h_upper⟩
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ ↦ (h_log i).1) h_card.le, ?_⟩
  rw [div_le_iff₀' h_card, ← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul Finset.univ _ L fun i _ ↦ (h_log i).2

/-- If `b = exp L` with `L ≥ 7`, `M` lies in `[b ^ 20, b ^ 22]` and `R` lies in `[1, b]`, then
`M R / 2π` lies in `[b ^ 19, b ^ 23]`; the bounds are stated for the logarithm. -/
lemma log_mul_div_two_pi_mem_Icc {M R L : ℝ} (hL : 7 ≤ L) (hM : M ∈ Icc (exp L ^ 20) (exp L ^ 22))
    (hR : R ∈ Icc 1 (exp L)) : log (M * R / (2 * π)) ∈ Icc (19 * L) (23 * L) := by
  obtain ⟨hM_lower, hM_upper⟩ := hM
  obtain ⟨hR_lower, hR_upper⟩ := hR
  have hM_pos : 0 < M := hM_lower.trans_lt' (by positivity)
  have h_pi_upper : 2 * π ≤ exp L := by linarith [pi_le_four, add_one_le_exp L]
  constructor
  · rw [le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    calc exp (19 * L) * (2 * π) ≤ exp (19 * L) * exp L := by gcongr
      _ = exp L ^ 20 * 1 := by
        rw [← exp_add, ← exp_nat_mul]
        ring_nf
      _ ≤ M * R := by gcongr
  · rw [log_le_iff_le_exp (by positivity)]
    calc M * R / (2 * π) ≤ M * R := div_le_self (by positivity) (by linarith [two_le_pi])
      _ ≤ exp L ^ 22 * exp L := by gcongr
      _ = exp (23 * L) := mod_cast (exp_nat_mul L 23).symm

/-- The bounds `m log b ≤ log N₋ ≤ 24 m log b` for `log N₋ = P.logLevelMin s m κ M L`, the logarithm
of `N₋ = κ̄ ^ m (M rd_E / 2π) ^ (m - 1) b ^ (-15 / 2)`, where `b = exp L`. The parameters `P`
consist of a modulus `q₀` and a prime `d = P.d`. The index `s` selects the multiple `q₁ = P.q₁ s` of
`q₀` and the field `E = K(ζ_{q₁})` over `K = ℚ(√-d)`, whose infinite places form the type `P.Φ s`.
Further `κ̄` is the geometric mean of the weights `κ` over these places, and `rd_E` is the root
discriminant of `E`, which is at most `q₁ d`. The hypotheses are `L ≥ 7`, `m ≥ 2`, weights in
`[1, b]`, `M` in `[b ^ 20, b ^ 22]` and `q₁ d ≤ b`. -/
lemma Parameters.logLevelMin_mem_Icc (P : Parameters) {s m M : ℕ} {κ : P.Φ s → ℕ} {L : ℝ}
    (hm : 2 ≤ m) (hL : 7 ≤ L) (hκ : ∀ τ : P.Φ s, (κ τ : ℝ) ∈ Icc 1 (exp L))
    (hM : (M : ℝ) ∈ Icc (exp L ^ 20) (exp L ^ 22))
    (h_conductor_le : (P.q₁ s * P.d : ℕ) ≤ exp L) :
    P.logLevelMin s m κ M L ∈ Icc (m * L) (24 * m * L) := by
  have hm_real : (2 : ℝ) ≤ m := mod_cast hm
  have hm_sub : (0 : ℝ) ≤ m - 1 := by linarith
  have h_rootDiscr : rootDiscr (P.E s) ∈ Icc (1 : ℝ) (P.q₁ s * P.d : ℕ) :=
    rootDiscr_mem_Icc (mul_ne_zero (NeZero.ne _) P.d_prime.ne_zero) P.conductor_mem_differentIdeal
  set logMean : ℝ := (∑ τ : P.Φ s, log (κ τ)) / Fintype.card (P.Φ s)
  set logScaled : ℝ := log (M * rootDiscr (P.E s) / (2 * π))
  obtain ⟨h_mean_lower, h_mean_upper⟩ : logMean ∈ Icc 0 L := sum_log_div_card_mem_Icc hκ
  obtain ⟨h_scaled_lower, h_scaled_upper⟩ : logScaled ∈ Icc (19 * L) (23 * L) :=
    log_mul_div_two_pi_mem_Icc hL hM (Icc_subset_Icc_right h_conductor_le h_rootDiscr)
  change m * logMean + (m - 1) * logScaled - 15 / 2 * L ∈ Icc (m * L) (24 * m * L)
  constructor
  · calc m * L ≤ m * 0 + (m - 1) * (19 * L) - 15 / 2 * L := by nlinarith
      _ ≤ m * logMean + (m - 1) * logScaled - 15 / 2 * L := by gcongr
  · calc m * logMean + (m - 1) * logScaled - 15 / 2 * L
      _ ≤ m * L + (m - 1) * (23 * L) - 15 / 2 * L := by gcongr
      _ ≤ 24 * m * L := by linarith

end New

end
