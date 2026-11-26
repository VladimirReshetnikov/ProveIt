import New.Reduction.Data.Sizes

/-!
# Prime sums: main amount, expected value and total remainder

For admissible data `D` this file defines the main amount (`D.mainAmount`), the expected value
`s_main` (`D.mainPrimeSum`) and the total remainder `rem` (`D.totalRemainder`). It expresses the
total remainder through the remainders `R_q` of prime sums (`totalRemainder_eq`) and bounds `s_fin`,
`s_∞`, the direction amount and the main amount (`primeSum_le`, `jetSize_mem_Icc`,
`directionAmount_mem_Icc`, `le_mainAmount`). The modulus `q₀` is `P.q₀`.

Notions from other files:
* `lambdaKResidueClass d q n` is `Λ_K(n) = Λ(n) (1 - chiK d n)` if `n ≡ 1` modulo `q`, and `0`
  otherwise; `Λ` is the von Mangoldt function and `chiK d` is the Legendre symbol `(·/d)`.
* `primeRemainder d q z` is `R_q(z) = ∑_{n ≤ z} λ(n) (1 / n - 1 / z) - log z / φ(q) - c_q` with
  `λ = lambdaKResidueClass d q` and `c_q = (logDerivMean d q 1).re`. The function `logDerivMean d q`
  is `(∑_ψ (L'/L(quadTwist ψ d) - L'/L(ψ)) - 1) / φ(q)`, summed over the Dirichlet characters `ψ`
  modulo `q`, where `L = entireL` is the `L`-function made entire.
* `D.Φ` is the group of the `D.f` infinite places; `D.aPlaces` (`Φ_a`, the `a`-places) are those
  `≡ 1` modulo `q₀`, and `D.bPlaces` (`Φ_b`, the `b`-places) is a set of places `≡ -1` modulo `q₀`.
  The class of a place modulo `q₀` is its image under `P.placeClass`, and `-n τ` stands for
  `D.placeOfInt (-n) * τ`. The weight `κ = D.weight` is `b = a / x` on `Φ_b` and `a / x₁` elsewhere.
* `D.primeSum y τ` is `s_fin(y, τ) = ∑_{n ≤ a} Λ_K(n) (y / n - κ(-n τ))₊`.
* `D.jetSize j` is `s_∞(j) = log j! + j log (M / Ω)` with `M = D.M` and `Ω = P.bigOmega D.towerExp`,
  and the direction amount `D.directionAmount` is `∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))`.
-/

noncomputable section

open Real Finset

namespace New

variable {d : ℕ} [Fact d.Prime] {q : ℕ}

/-- The function `lambdaKResidueClass d q` is the restriction of `Λ_K = lambdaKResidueClass d 1` to
the integers `n ≡ 1` modulo `q`. -/
lemma lambdaKResidueClass_eq_ite (n : ℕ) :
    lambdaKResidueClass d q n = if (n : ZMod q) = 1 then lambdaKResidueClass d 1 n else 0 := by
  simp [lambdaKResidueClass, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator,
    Subsingleton.elim (n : ZMod 1) 1]

/-- For `0 < z ≤ A` with `A` an integer, the sum of `Λ_K(n) (A / n - A / z)₊` over the `n ≤ A` with
`n ≡ 1` modulo `q` equals `A (R_q(z) + log z / φ(q) + c_q)`. -/
lemma sum_lambdaKResidueClass_mul_posPart [NeZero q] (A : ℕ) {z : ℝ} (hz : 0 < z) (hzA : z ≤ A) :
    ∑ n ∈ Icc 1 A, lambdaKResidueClass d q n * (A / n - A / z : ℝ)⁺ =
      A * (primeRemainder d q z + log z / q.totient + (logDerivMean d q 1).re) := by
  have hA : (A : ℝ) ≠ 0 := (hz.trans_le hzA).ne'
  rw [primeRemainder_eq_sum A hz hzA, ← sum_div]
  field_simp
  ring

namespace Data

open Parameters

variable {P : Parameters} (D : Data P)

/-- The main amount `m k ∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))`, that is, `m k` times the direction
amount. Here `m = D.m` is the number of theta lifts in each chain; the source has rank
`k = D.k = r + 1 - m` and the target has rank `r = D.r`. -/
def mainAmount : ℝ := D.m * D.k * D.directionAmount

/-- The expected value `s_main = a (log (a / κ̄) + c₁)` of the mean of the prime sums `s_fin(a, τ)`
over the `a`-places `τ`, that is, the main term of this mean (see `sum_aPlaces_primeSum` and
`card_aPlaces_mul_mainPrimeSum`). Here `log κ̄` is the mean of `log κ(τ)` over all `f` places, `κ`
is the weight, and `c₁ = (logDerivMean P.d 1 1).re`. -/
def mainPrimeSum : ℝ :=
  D.a * (log D.a - (∑ τ : D.Φ, log (D.weight τ)) / D.f + (logDerivMean P.d 1 1).re)

/-- The total remainder `rem = ∑ (s_fin(a, τ) - s_main)`, summed over the `a`-places `τ`; `s_fin` is
`D.primeSum` and `s_main` is `D.mainPrimeSum`. -/
def totalRemainder : ℝ := ∑ τ ∈ D.aPlaces, (D.primeSum D.a τ - D.mainPrimeSum)

/-- The set `D.aPlaces` of places `≡ 1` modulo `q₀` has `towerDeg towerExp = q₁ / q₀` elements. Here
`towerExp = D.towerExp` is the exponent with `2 ^ towerExp = m ^ 22` that selects the field
`E = P.E towerExp`, and `q₁ = P.q₁ towerExp` is the order of the root of unity that generates `E`
over `K`. -/
lemma card_aPlaces : #D.aPlaces = towerDeg D.towerExp :=
  card_placeClass_eq_one_eq_towerDeg (P.q₀.dvd_mul_right (towerDeg D.towerExp))

/-- The number `f` of all places is the number of `a`-places times `φ(q₀)`. -/
lemma f_eq_card_aPlaces_mul : D.f = #D.aPlaces * P.q₀.totient := by
  rw [card_aPlaces]
  exact numInfPlaces_E D.towerExp

/-- If `-n τ` is a `b`-place, hence `≡ -1` modulo `q₀`, then `τ` is an `a`-place (`τ ≡ 1`) if and
only if `n ≡ 1` modulo `q₀`. -/
lemma mem_aPlaces_iff_of_mul_mem_bPlaces {n : ℕ} {τ : D.Φ}
    (hτ : D.placeOfInt (-n) * τ ∈ D.bPlaces) :
    τ ∈ D.aPlaces ↔ (n : ZMod P.q₀) = 1 := by
  have h_dvd : P.q₀ ∣ P.q₁ D.towerExp := P.q₀.dvd_mul_right (towerDeg D.towerExp)
  have h_class : P.placeClass h_dvd (D.placeOfInt (-n)) * P.placeClass h_dvd τ = -1 :=
    (map_mul _ _ _).symm.trans (D.placeClass_of_mem_bPlaces _ hτ)
  calc τ ∈ D.aPlaces ↔ P.placeClass h_dvd τ = 1 := by rw [aPlaces, mem_filter_univ]
    _ ↔ P.placeClass h_dvd (D.placeOfInt (-n)) = -1 := by rw [← h_class, left_eq_mul]
    _ ↔ (n : ZMod P.q₀) = 1 := by simp [placeClass_placeOfInt_eq_neg_one_iff]

/-- As `τ` runs over the `a`-places `D.aPlaces`, the place `-n τ = D.placeOfInt (-n) * τ` lies in
`D.bPlaces` for `#D.bPlaces` values of `τ` if `n ≡ 1` modulo `q₀`, and for none otherwise. -/
lemma card_filter_mem_bPlaces (n : ℕ) :
    #{τ ∈ D.aPlaces | D.placeOfInt (-n) * τ ∈ D.bPlaces} =
      if (n : ZMod P.q₀) = 1 then #D.bPlaces else 0 := by
  split_ifs with hn
  · refine card_equiv (Equiv.mulLeft (D.placeOfInt (-n))) fun τ ↦ ?_
    simpa using fun hτ ↦ (D.mem_aPlaces_iff_of_mul_mem_bPlaces hτ).2 hn
  · simpa [filter_eq_empty_iff] using
      fun τ hτa hτb ↦ hn ((D.mem_aPlaces_iff_of_mul_mem_bPlaces (τ := τ) hτb).1 hτa)

/-- The contribution of one integer `n` to the sum of the prime sums `D.primeSum D.a τ` over the
places `τ ≡ 1` modulo `q₀` (the set `D.aPlaces`). So every `τ` gives the term of weight `a / x₁`,
and if `n ≡ 1` modulo `q₀` there is one correction to the weight `a / x` for each place of
`D.bPlaces`. -/
lemma sum_aPlaces_lambdaKResidueClass_mul_posPart (n : ℕ) :
    ∑ τ ∈ D.aPlaces, lambdaKResidueClass P.d 1 n * (D.a / n - D.weight (D.placeOfInt (-n) * τ) : ℝ)⁺
      =
      #D.aPlaces * (lambdaKResidueClass P.d 1 n * (D.a / n - D.a / D.x₁ : ℝ)⁺) +
        #D.bPlaces * (lambdaKResidueClass P.d P.q₀ n * (D.a / n - D.a / D.x : ℝ)⁺ -
          lambdaKResidueClass P.d P.q₀ n * (D.a / n - D.a / D.x₁ : ℝ)⁺) := by
  have h_term (σ : D.Φ) : (D.a / n - D.weight σ : ℝ)⁺ = (D.a / n - D.a / D.x₁ : ℝ)⁺ +
      if σ ∈ D.bPlaces then (D.a / n - D.a / D.x : ℝ)⁺ - (D.a / n - D.a / D.x₁ : ℝ)⁺ else 0 := by
    rw [cast_weight]
    split_ifs <;> ring
  have h_sum : ∑ τ ∈ D.aPlaces, (D.a / n - D.weight (D.placeOfInt (-n) * τ) : ℝ)⁺ =
      #D.aPlaces * (D.a / n - D.a / D.x₁ : ℝ)⁺ +
        #{τ ∈ D.aPlaces | D.placeOfInt (-n) * τ ∈ D.bPlaces} *
        ((D.a / n - D.a / D.x : ℝ)⁺ - (D.a / n - D.a / D.x₁ : ℝ)⁺) := by
    simp only [h_term, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul]
  rw [← mul_sum, h_sum, card_filter_mem_bPlaces, lambdaKResidueClass_eq_ite (q := P.q₀)]
  split_ifs <;> simp [mul_add, mul_sub, mul_left_comm]

/-- The sum over the `a`-places `τ` of the prime sums `D.primeSum a τ = s_fin(a, τ) = ∑_{1 ≤ n ≤ a}
Λ_K(n) (a / n - κ(-n τ))₊` is `a` times the remainders `#Φ_b (R_{q₀}(x) - R_{q₀}(x₁)) + #Φ_a R₁(x₁)`
plus `a` times the main terms `#Φ_a (log x₁ + c₁) + #Φ_b log (x / x₁) / φ(q₀)`. -/
lemma sum_aPlaces_primeSum :
    ∑ τ ∈ D.aPlaces, D.primeSum D.a τ =
      D.a * (#D.bPlaces * (primeRemainder P.d P.q₀ D.x - primeRemainder P.d P.q₀ D.x₁) +
          #D.aPlaces * primeRemainder P.d 1 D.x₁) +
        D.a * (#D.aPlaces * (D.logX₁ + (logDerivMean P.d 1 1).re) +
          #D.bPlaces * ((D.logX - D.logX₁) / P.q₀.totient)) := by
  simp only [primeSum]
  rw [sum_comm, sum_congr rfl fun n _ ↦ D.sum_aPlaces_lambdaKResidueClass_mul_posPart n]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [sum_lambdaKResidueClass_mul_posPart (q := 1) D.a (exp_pos D.logX₁) D.le_of_hasLogBound,
    sum_lambdaKResidueClass_mul_posPart (q := P.q₀) D.a (exp_pos D.logX) D.le_of_hasLogBound,
    sum_lambdaKResidueClass_mul_posPart (q := P.q₀) D.a (exp_pos D.logX₁) D.le_of_hasLogBound,
    log_exp D.logX, log_exp D.logX₁, Nat.totient_one, Nat.cast_one]
  ring

/-- The sum of `log κ(τ)` over all `D.f` places `τ` is `f log (a / x₁) - #Φ_b log (x / x₁)`. This
holds since the weight `κ = D.weight` is `a / x` on the set `Φ_b = D.bPlaces` of `b`-places and
`a / x₁` elsewhere. -/
lemma sum_log_weight :
    ∑ τ : D.Φ, log (D.weight τ) = D.f * (log D.a - D.logX₁) - #D.bPlaces * (D.logX - D.logX₁) := by
  have h_log (τ : D.Φ) :
      log (D.weight τ) = log D.a - D.logX₁ - if τ ∈ D.bPlaces then D.logX - D.logX₁ else 0 := by
    rw [cast_weight]
    split_ifs <;> simp [log_div, (HasLogBound.pos D).ne']
  simp [h_log, sum_sub_distrib, mul_sub]

/-- Let `s_main = D.mainPrimeSum = a (log a - f⁻¹ ∑_τ log κ(τ) + c₁)`, the sum running over all `f`
places with weights `κ = D.weight`. Then `#Φ_a s_main` equals
`a (#Φ_a (log x₁ + c₁) + #Φ_b log (x / x₁) / φ(q₀))`, the main term of the sum of `D.primeSum a τ`
over `τ ∈ Φ_a` in `sum_aPlaces_primeSum`. -/
lemma card_aPlaces_mul_mainPrimeSum :
    #D.aPlaces * D.mainPrimeSum =
      D.a * (#D.aPlaces * (D.logX₁ + (logDerivMean P.d 1 1).re) +
        #D.bPlaces * ((D.logX - D.logX₁) / P.q₀.totient)) := by
  have hf : (#D.aPlaces * P.q₀.totient : ℝ) ≠ 0 := by
    rw [← Nat.cast_mul, ← f_eq_card_aPlaces_mul]
    exact (HasLogBound.pos D).ne'
  rw [mainPrimeSum, sum_log_weight, f_eq_card_aPlaces_mul, Nat.cast_mul]
  field [left_ne_zero_of_mul hf, right_ne_zero_of_mul hf]

/-- The total remainder `∑_{τ ∈ Φ_a} (D.primeSum a τ - D.mainPrimeSum)` is
`a (#Φ_b (R_{q₀}(x) - R_{q₀}(x₁)) + #Φ_a R₁(x₁))`. -/
lemma totalRemainder_eq :
    D.totalRemainder =
      D.a * (#D.bPlaces * (primeRemainder P.d P.q₀ D.x - primeRemainder P.d P.q₀ D.x₁) +
        #D.aPlaces * primeRemainder P.d 1 D.x₁) := by
  rw [totalRemainder, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_aPlaces_primeSum,
    card_aPlaces_mul_mainPrimeSum, add_sub_cancel_right]

/-- For `0 ≤ y ≤ a = D.a`, `n ≥ 1` and a place `σ` (an element of `D.Φ`) of weight
`κ(σ) = D.weight σ`, the term `Λ_K(n) (y / n - κ(σ))₊` is at most `2 y Λ(n) / n` for `n` up to the
cut-off `x₁ = D.x₁`, and at most `0` for `n > x₁` because `κ(σ) ≥ a / x₁`. -/
lemma lambdaKResidueClass_mul_posPart_le_ite {y : ℝ} (hy : 0 ≤ y) (hya : y ≤ D.a) (σ : D.Φ) {n : ℕ}
    (hn : 0 < n) :
    lambdaKResidueClass P.d 1 n * (y / n - D.weight σ : ℝ)⁺ ≤
      if n ∈ Ioc 0 ⌊D.x₁⌋₊ then 2 * y * (ArithmeticFunction.vonMangoldt n / n) else 0 := by
  split_ifs with h_mem
  · have h_part : (y / n - D.weight σ : ℝ)⁺ ≤ y / n :=
      sup_le (sub_le_self _ (Nat.cast_nonneg _)) (by positivity)
    calc _ ≤ 2 * ArithmeticFunction.vonMangoldt n * (y / n) :=
          mul_le_mul (lambdaKResidueClass_le_two_mul_vonMangoldt n) h_part (posPart_nonneg _)
            (by positivity)
      _ = 2 * y * (ArithmeticFunction.vonMangoldt n / n) := by ring
  · have hxn : D.x₁ ≤ n := (Nat.lt_of_floor_lt (by simpa [hn] using h_mem)).le
    have h_le : y / n ≤ D.weight σ :=
      calc y / n ≤ D.a / D.x₁ := by gcongr
        _ ≤ D.weight σ := (D.weight_mem_Icc σ).1
    rw [posPart_eq_zero.2 (sub_nonpos.2 h_le), mul_zero]

/-- For `0 ≤ y ≤ a = D.a` and every place `τ` (an element of `D.Φ`) the prime sum `s_fin(y,
τ) = ∑_{1 ≤ n ≤ a} Λ_K(n) (y / n - κ(-n τ))₊` is at most `4 y log x₁`, as only `n ≤ x₁` count. -/
lemma primeSum_le {y : ℝ} (hy : 0 ≤ y) (hya : y ≤ D.a) (τ : D.Φ) :
    D.primeSum y τ ≤ 4 * y * D.logX₁ := by
  have h_log : log ⌊D.x₁⌋₊ ≤ D.logX₁ :=
    (log_le_iff_le_exp (mod_cast Nat.floor_pos.2 (D.le_of_hasLogBound : 1 ≤ D.x₁))).2
      (Nat.floor_le (exp_nonneg _))
  calc D.primeSum y τ
      ≤ ∑ n ∈ Icc 1 D.a,
          if n ∈ Ioc 0 ⌊D.x₁⌋₊ then 2 * y * (ArithmeticFunction.vonMangoldt n / n) else 0 :=
        sum_le_sum fun n hn ↦ D.lambdaKResidueClass_mul_posPart_le_ite hy hya _ (mem_Icc.1 hn).1
    _ ≤ ∑ n ∈ Ioc 0 ⌊D.x₁⌋₊, 2 * y * (ArithmeticFunction.vonMangoldt n / n) := by
        rw [sum_ite_mem]
        exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ ↦ by positivity
    _ ≤ 2 * y * (2 * D.logX₁) := by grw [← mul_sum, sum_vonMangoldt_div_le, h_log]
    _ = 4 * y * D.logX₁ := by ring

/-- For `0 ≤ y ≤ a` and every place `τ` the prime sum `D.primeSum y τ = ∑_{1 ≤ n ≤ a} Λ_K(n)
(y / n - κ(-n τ))₊` lies between `0` and `y log b`. -/
lemma primeSum_mem_Icc {y : ℝ} (hy : 0 ≤ y) (hya : y ≤ D.a) (τ : D.Φ) :
    D.primeSum y τ ∈ Set.Icc 0 (y * D.logB) := by
  have h_scale : 4 * D.logX₁ ≤ D.logB := D.le_of_hasLogBound
  refine ⟨sum_nonneg fun n _ ↦ mul_nonneg (lambdaKResidueClass_nonneg P.d 1 n) (posPart_nonneg _),
    ?_⟩
  grw [D.primeSum_le hy hya, ← h_scale]
  linarith

/-- For an integer `y ≤ a` the quantity `s_∞(y) = D.jetSize y = log y! + y log (M / Ω)` satisfies
`20 y log b ≤ s_∞(y) ≤ 25 y log b`. Here `M = D.M = p₀ p₁` is the principal level, a product of two
primes in `[b¹⁰, b¹¹]`, `Ω = P.bigOmega D.towerExp = exp (γ - Re L'/L(1, χ_K)) 2π / rd_E` with `γ`
Euler's constant and `rd_E` the root discriminant of `E`, and `log b = D.logB`. -/
lemma jetSize_mem_Icc {y : ℕ} (hya : y ≤ D.a) :
    D.jetSize y ∈ Set.Icc (20 * y * D.logB) (25 * y * D.logB) := by
  have h_fact : log y.factorial ≤ y * (2 * D.logB) := by
    have ha : (D.a : ℝ) ≤ D.b ^ 2 := D.le_of_hasLogBound
    calc log y.factorial ≤ log ((D.b ^ 2) ^ y) := by
          gcongr
          grw [Nat.factorial_le_pow, Nat.cast_pow, hya, ha]
      _ = y * (2 * D.logB) := by simp
  obtain ⟨h_log_lower, h_log_upper⟩ :
      log (D.M / P.bigOmega D.towerExp) ∈ Set.Icc (20 * D.logB) (23 * D.logB) :=
    D.log_M_div_bigOmega_mem_Icc
  have h_lower : y * (20 * D.logB) ≤ y * log (D.M / P.bigOmega D.towerExp) := by gcongr
  have h_upper : y * log (D.M / P.bigOmega D.towerExp) ≤ y * (23 * D.logB) := by gcongr
  rw [jetSize]
  constructor <;> linarith [log_natCast_nonneg y.factorial]

/-- For a place `τ` of weight `y = D.weight τ`, the difference `s_∞(y) - s_fin(y, τ)` lies between
`y log b` and `25 y log b`. -/
lemma jetSize_sub_primeSum_mem_Icc (τ : D.Φ) :
    D.jetSize (D.weight τ) - D.primeSum (D.weight τ) τ ∈
      Set.Icc (D.weight τ * D.logB) (25 * D.weight τ * D.logB) := by
  have hκa : (D.weight τ : ℝ) ≤ D.a := D.le_of_hasLogBound
  obtain ⟨h_jet_lower, h_jet_upper⟩ : D.jetSize (D.weight τ) ∈
      Set.Icc (20 * D.weight τ * D.logB) (25 * D.weight τ * D.logB) :=
    D.jetSize_mem_Icc (mod_cast hκa)
  obtain ⟨h_prime_lower, h_prime_upper⟩ :
      D.primeSum (D.weight τ) τ ∈ Set.Icc 0 (D.weight τ * D.logB) :=
    D.primeSum_mem_Icc (Nat.cast_nonneg _) hκa τ
  constructor <;> linarith

/-- The direction amount `D.directionAmount = ∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))`, summed over all `f`
places with weights `κ`, lies between `b #Φ_a` and `25 f b log b`. -/
lemma directionAmount_mem_Icc :
    D.directionAmount ∈ Set.Icc (D.b * #D.aPlaces) (25 * D.f * D.b * D.logB) := by
  have h_log : 0 ≤ D.logB := (HasLogBound.pos D).le
  constructor
  · -- On the `b`-places `κ = b`, and there are at least `#Φ_a / log b` of them.
    calc D.b * #D.aPlaces ≤ D.b * (#D.bPlaces * D.logB) := by
          grw [card_aPlaces, D.towerDeg_le_card_bPlaces_mul]
      _ = ∑ τ ∈ D.bPlaces, D.weight τ * D.logB := by
        simp +contextual [D.weight_eq, ← D.exp_logB, mul_left_comm]
      _ ≤ ∑ τ : D.Φ, D.weight τ * D.logB := sum_le_univ_sum_of_nonneg fun τ ↦ by positivity
      _ ≤ D.directionAmount := sum_le_sum fun τ _ ↦ (D.jetSize_sub_primeSum_mem_Icc τ).1
  · calc D.directionAmount ≤ ∑ τ : D.Φ, 25 * D.weight τ * D.logB :=
          sum_le_sum fun τ _ ↦ (D.jetSize_sub_primeSum_mem_Icc τ).2
      _ ≤ ∑ _τ : D.Φ, 25 * D.b * D.logB := by
          gcongr with τ
          exact D.weight_le_b τ
      _ = 25 * D.f * D.b * D.logB := by simp [mul_assoc, mul_left_comm]

/-- The main amount `m k ∑_τ (s_∞(κ(τ)) - s_fin(κ(τ), τ))` is at least `x⁴ f a`. Here
`m ∈ [√x, 2 √x]` is the number of theta lifts, `k = r + 1 - m` is the rank of the source
(`r ∈ [x⁵, 3 x⁵]` that of the target), `x` is the first cut-off, `b` is the weight on `D.bPlaces`
and `a = x b`. -/
lemma le_mainAmount : D.x ^ 4 * D.f * D.a ≤ D.mainAmount := by
  -- The first step is an inequality between products of the parameters, compared by logarithms.
  calc D.x ^ 4 * D.f * D.a ≤ D.m * D.k * (D.b * towerDeg D.towerExp) := D.le_of_hasLogBound
    _ ≤ D.mainAmount := by grw [mainAmount, ← D.card_aPlaces, D.directionAmount_mem_Icc.1]

/-- The main amount `D.mainAmount` is nonnegative. -/
lemma mainAmount_nonneg : 0 ≤ D.mainAmount := le_trans (by positivity) D.le_mainAmount

end Data

end New

end
