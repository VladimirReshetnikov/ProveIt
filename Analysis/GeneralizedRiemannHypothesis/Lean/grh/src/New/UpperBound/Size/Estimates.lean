import New.UpperBound.Size.ClassCount

/-!
# Numerical inequalities between the parameters of the data

This file proves explicit identities and inequalities between the parameters of the data `D`,
which are used to bound heights and indices. It groups the von Mangoldt sum prime by prime,
bounds the rows of the diagrams and the size of jets, computes the norm of `D.piMBar`, bounds the
number of classes at levels that contain a principal level, and bounds the sum of the allowed
losses. Here `s_p(y, σ)` is `New.Data.localPrimeSum p y σ`, and `κ(τ)` is the weight `D.weight τ`
of an infinite place `τ` (not the column count `D.columnCount τ h`).

## Main definitions and results

* `New.Data.localPrimeSum_eq_tsum`, `New.Data.primeSum_eq_sum_localPrimeSum`: the local sum at `p`
  as a sum over the powers of `p`, and the von Mangoldt sum `New.Data.primeSum` grouped prime by
  prime.
* `New.Data.card_stdClasses_le_exp_mul_log`, `New.Data.card_stdClasses_le_exp`: bounds for the
  number of classes of the definite unitary group at a level `K` that contains a given principal
  level.
* `New.Data.sum_allowedLoss_mul_log_le`: the losses `New.Data.allowedLoss p`, weighted by `log p`,
  add up to at most `New.Data.errorUnit`.

Notions from other files:
* `New.StdClasses K`: the double cosets `Γ \ G_f / K` of the finite adelic unitary group `G_f` of
  the form `∑ x_i \bar x_i` by its rational points `Γ` and a subgroup `K`.
* `New.Data`: the parameters `x`, `x₁`, `a`, `b`, `m`, `N`, … of the construction; `D.E` is its CM
  field, which contains `P.K = ℚ(√-d)` and has `D.f` infinite places.
* `New.Data.loss`: `f a (log b)² / p`, times `m` if `p ≡ ±1` mod `m`.

## Relation to the literature

See `Lib.Adelic.Reduction.FiniteVolume` for sources. See
`New.UpperBound.Divisibility.LocalDivisibility` for related work.
-/

noncomputable section

section SizeEstimates

namespace New.Data

open Nat ArithmeticFunction Finset Real NumberField Space NeZero Subgroup

variable {P : Parameters} (D : Data P)

/-! ### The von Mangoldt sum, prime by prime -/

/-- The set of primes `p < x₁` with Legendre symbol `(p / d) ≠ 1`, that is the primes below `x₁`
that do not split in `K = ℚ(√-d)`. -/
abbrev smallNonsplitPrimes : Finset ℕ := {p ∈ range ⌈D.x₁⌉₊ | Nat.Prime p ∧ chiK P.d p ≠ 1}

/-- The admissible data `D : Data P` give a CM field `E = D.E`, a modulus `q₁`, the group `D.Φ` of
infinite places of `E`, identified with `(ℤ/q₁)ˣ`, and a weight `κ = D.weight` on `D.Φ`. For an
integer `ν`, `D.placeOfInt ν` is the place of the class of `ν` if `ν` is prime to `q₁`, and the
identity place otherwise; `ν σ` stands for the product `D.placeOfInt ν * σ` of places. Let `χ_K` be
the Legendre symbol modulo the prime `d = P.d`, attached to `K = ℚ(√-d)`. For a prime `p`, a real
`y` and a place `σ`, the local term `s_p(y, σ) = D.localPrimeSum p y σ` equals `∑_{e ≥ 1} (1 - χ_K(p
^ e)) / 2 · (y / p ^ e - κ(-p ^ e σ))₊`. -/
lemma localPrimeSum_eq_tsum {p : ℕ} (hp : p.Prime) (y : ℝ) (σ : D.Φ) :
    D.localPrimeSum p y σ = ∑' e : ℕ, (1 - chiK P.d (p ^ (e + 1))) / 2 *
      (y / p ^ (e + 1) - D.weight (D.placeOfInt (-p ^ (e + 1)) * σ))⁺ := by
  have : Fact p.Prime := ⟨hp⟩
  -- The term `e = 0` vanishes, so the sum can be shifted by one.
  have h_shift (g : ℕ → ℝ) (hg : g 0 = 0) : ∑' e, g e = ∑' e, g (e + 1) :=
    (succ_injective.tsum_eq fun e he ↦ by cases e <;> simp_all).symm
  rw [localPrimeSum, ← tsum_mul_left, h_shift _ (by simp [mem_positivePartnerExponents])]
  refine tsum_congr fun e ↦ ?_
  rw [map_pow, Int.cast_pow, one_sub_chiK_pow_div_two]
  split_ifs <;> simp

/-- For `y ≤ a` and `x₁ ≤ t` we have `(y / t - κ(τ))₊ = 0`, since the weight `κ(τ)` of every
infinite place `τ` is at least `a / x₁`. -/
lemma posPart_div_sub_weight_eq_zero {y t : ℝ} (hy : y ≤ D.a) (ht : D.x₁ ≤ t) (τ : D.Φ) :
    (y / t - D.weight τ)⁺ = 0 := by
  have ht_pos : 0 < t := (exp_pos _).trans_le ht
  refine posPart_eq_zero.2 (sub_nonpos.2 ?_)
  calc y / t ≤ D.a / t := by gcongr
    _ ≤ D.a / D.x₁ := by gcongr
    _ ≤ D.weight τ := (D.weight_mem_Icc τ).1

/-- For a natural number `p ≥ x₁` and `y ≤ a` the local term `D.localPrimeSum p y σ` vanishes,
since every weight is at least `a / x₁`. -/
lemma localPrimeSum_eq_zero {p : ℕ} (hp : D.x₁ ≤ p) {y : ℝ} (hy : y ≤ D.a) (σ : D.Φ) :
    D.localPrimeSum p y σ = 0 := by
  simp +contextual [localPrimeSum, mem_positivePartnerExponents, fun (e : ℕ) (he : 0 < e) ↦
    D.posPart_div_sub_weight_eq_zero hy
      (hp.trans (le_self_pow₀ (le_trans D.le_of_hasLogBound hp) he.ne'))]

/-- The gain `D.gain p`, which is `m` times a sum of local terms `s_p`, is zero if `p` splits in
`K`, that is `χ_K(p) = 1`, or if `p ≥ x₁`. -/
lemma gain_eq_zero {p : ℕ} (hp : chiK P.d p = 1 ∨ D.x₁ ≤ p) : D.gain p = 0 := by
  have h_local_zero {y : ℝ} (hy : y ≤ D.a) (σ : D.Φ) : D.localPrimeSum p y σ = 0 := by
    rcases hp with h_split | h_large
    · simp [localPrimeSum, positivePartnerExponents_of_split h_split]
    · exact D.localPrimeSum_eq_zero h_large hy σ
  simp [gain, localPrimeSumTotal, h_local_zero le_rfl,
    fun σ : D.Φ ↦ h_local_zero (y := D.weight σ) D.le_of_hasLogBound σ]

/-- The prime sum `D.primeSum y σ = ∑_{1 ≤ ν ≤ a} Λ(ν) (1 - χ_K(ν)) (y / ν - κ(-ν σ))₊`, grouped by
primes. The admissible data `D` give an integer `a`, a real number `x₁` and a weight `κ ≥ a / x₁` on
the group `D.Φ` of infinite places of the field `D.E`, identified with `(ℤ/q₁)ˣ`. Here `-ν σ` is
`D.placeOfInt (-ν) * σ`, where `D.placeOfInt (-ν)` is the place of the class of `-ν` if `ν` is prime
to `q₁` and the identity place otherwise, and `χ_K` is the Legendre symbol modulo the prime
`d = P.d`. For `y ≤ a` the terms with `ν ≥ x₁` vanish, and for `U ≥ x₁` the sum is that of
`2 s_p(y, σ) log p` over the primes `p < U`. -/
lemma primeSum_eq_sum_localPrimeSum {U : ℕ} (hU : ⌈D.x₁⌉₊ ≤ U) {y : ℝ} (σ : D.Φ) (hy : y ≤ D.a) :
    D.primeSum y σ = ∑ p ∈ range U with p.Prime, 2 * D.localPrimeSum p y σ * Real.log p := by
  -- The summand `G` is supported on prime powers below `x₁`; group it by the prime.
  let G (ν : ℕ) : ℝ := Λ ν * (1 - chiK P.d ν) * (y / ν - D.weight (D.placeOfInt (-ν) * σ))⁺
  have h_large (ν : ℕ) (hν : ⌈D.x₁⌉₊ ≤ ν) : G ν = 0 := by
    simp only [G, D.posPart_div_sub_weight_eq_zero hy (ceil_le.1 hν), mul_zero]
  have h_summable : Summable G :=
    summable_of_ne_finset_zero (s := range ⌈D.x₁⌉₊) fun ν hν ↦ h_large ν (by simpa using hν)
  -- `G` vanishes outside `Icc 1 a`, as `Λ 0 = 0` and `⌈x₁⌉₊ ≤ a`.
  have h_outside (ν : ℕ) (hν : ν ∉ Finset.Icc 1 D.a) : G ν = 0 := by
    obtain rfl | h_pos := ν.eq_zero_or_pos
    exacts [by simp [G], h_large ν (by grind [(D.nat_le_of_hasLogBound : ⌈D.x₁⌉₊ ≤ D.a)])]
  have h_support : Function.support G ⊆ {ν | IsPrimePow ν} := by simp +contextual [G, vonMangoldt]
  -- The powers of `p` contribute `2 s_p(y, σ) log p`, as `Λ (p ^ e) = log p`.
  have h_prime (p : ℕ) (hp : p.Prime) :
      2 * D.localPrimeSum p y σ * Real.log p = ∑' e : ℕ, G (p ^ (e + 1)) := by
    rw [D.localPrimeSum_eq_tsum hp, ← tsum_mul_left, ← tsum_mul_right]
    refine tsum_congr fun e ↦ ?_
    simp only [G, vonMangoldt_apply_pow e.succ_ne_zero, vonMangoldt_apply_prime hp, cast_pow]
    ring
  calc
    D.primeSum y σ = ∑ ν ∈ .Icc 1 D.a, G ν := by
      simp [primeSum, lambdaKResidueClass, G, Unique.eq_default]
    _ = ∑' ν, G ν := (tsum_eq_sum h_outside).symm
    _ = ∑' (p : Primes) (e : ℕ), G (p ^ (e + 1)) :=
      tsum_eq_tsum_primes_of_support_subset_prime_powers h_summable h_support
    _ = ∑ p ∈ range U with p.Prime, ∑' e, G (p ^ (e + 1)) := by
      rw [← sum_subtype_eq_sum_filter]
      refine tsum_eq_sum fun p hp ↦ (tsum_congr fun e ↦ h_large _ ?_).trans tsum_zero
      exact (hU.trans (not_lt.1 fun h ↦ hp (mem_subtype.2 (mem_range.2 h)))).trans
        (Nat.le_self_pow e.succ_ne_zero _)
    _ = ∑ p ∈ range U with p.Prime, 2 * D.localPrimeSum p y σ * Real.log p :=
      sum_congr rfl fun p hp ↦ (h_prime p (mem_filter.1 hp).2).symm

/-- The number `D.localPrimeSumTotal p`, the sum over the infinite places `τ` of the local terms
`D.localPrimeSum p (D.weight τ) τ`, is nonnegative. -/
lemma localPrimeSumTotal_nonneg (p : ℕ) : 0 ≤ D.localPrimeSumTotal p := by
  refine sum_nonneg fun σ _ ↦ mul_nonneg (piPrimeValuation_pos P.d p).le (tsum_nonneg fun e ↦ ?_)
  positivity

/-- The admissible data `D` give an integer `a` and a weight `κ = D.weight` on the group `D.Φ` of
infinite places of the field `D.E`, identified with `(ℤ/q₁)ˣ`. Let `χ_K` be the Legendre symbol
modulo the prime `d = P.d`, and for a place `τ` put `g_τ(ν) = (1 - χ_K(ν)) (κ(τ) / ν - κ(-ν τ))₊`.
For a prime `p` the number `F(p) = D.localPrimeSumTotal p` is `∑_τ ∑_{e ≥ 1} g_τ(p ^ e) / 2`, and
`D.primeSum κ(τ) τ` is `∑_{1 ≤ ν ≤ a} Λ(ν) g_τ(ν)`. For every finite set `T` of primes,
`∑_{p ∈ T} 2 F(p) log p ≤ ∑_τ D.primeSum κ(τ) τ`. -/
lemma sum_localPrimeSumTotal_mul_log_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∑ p ∈ T, 2 • (D.localPrimeSumTotal p * Real.log p) ≤ ∑ τ : D.Φ, D.primeSum (D.weight τ) τ := by
  -- Enlarge `T` to all primes below a bound `U ≥ x₁`, where equality holds.
  obtain ⟨U, hU⟩ : ∃ U : ℕ, T.sup id ⊔ ⌈D.x₁⌉₊ < U := exists_gt _
  have h_subset : T ⊆ {p ∈ range U | p.Prime} := fun p hp ↦ by
    simpa [hT p hp] using (le_sup (f := id) hp).trans_lt (le_sup_left.trans_lt hU)
  have h_prime_sum (τ : D.Φ) : D.primeSum (D.weight τ) τ =
      ∑ p ∈ range U with p.Prime, 2 * D.localPrimeSum p (D.weight τ) τ * Real.log p :=
    D.primeSum_eq_sum_localPrimeSum (le_sup_right.trans hU.le) τ D.le_of_hasLogBound
  calc ∑ p ∈ T, 2 • (D.localPrimeSumTotal p * Real.log p)
      ≤ ∑ p ∈ range U with p.Prime, 2 • (D.localPrimeSumTotal p * Real.log p) :=
        sum_le_sum_of_subset_of_nonneg h_subset fun p _ _ ↦
          nsmul_nonneg (mul_nonneg (D.localPrimeSumTotal_nonneg p) (Real.log_natCast_nonneg p)) 2
    _ = ∑ τ : D.Φ, D.primeSum (D.weight τ) τ := by
        simp only [h_prime_sum, localPrimeSumTotal, sum_mul, smul_sum, nsmul_eq_mul, Nat.cast_ofNat,
          mul_assoc]
        exact sum_comm

/-! ### Rows of the diagrams, the norm of `piMBar` and the size of jets -/

/-- The main length of row `i` of a lift diagram at the place `τ`: the number `D.columnCount τ 1` of
columns of height `1` for the first row (`i = 0`), the weight `κ(τ) = D.weight τ` for the next
`k - 1` rows, and `0` for the others. -/
def rowMainLength (τ : D.Φ) (i : ℕ) : ℕ :=
  if i = 0 then D.columnCount τ 1 else if i < D.k then D.weight τ else 0

/-- The number of boxes by which row `i` of a lift diagram may exceed its main length:
`b + offWeight + halfGap ^ 2` for the first row (`i = 0`) and `halfGap ^ 2` for the others. Here
`b = D.natB`, `offWeight = ⌊a / ⌊x₁⌋⌋` and `halfGap = D.r ^ 8` is half the gap `D.gap`. -/
def rowSlack (i : ℕ) : ℕ :=
  (if i = 0 then D.natB + D.offWeight else 0) + D.halfGap ^ 2

/-- The admissible data `D` give the number `m` of lifts, the rank `k` of the first space, index
sets `D.X j` of sizes `n_j = k + j (t + 1)`, and a weight `κ = D.weight` on the set `D.Φ` of
infinite places of the field `D.E`, with values at least `a / x₁`. For a place `τ` the number
`D.columnCount τ h` is the number of columns of height `h` in the highest weight at `τ` of the forms
on the definite space of rank `n_j`. Let `j < m`, and take the Young diagram at `τ` with these
columns for all `h < n_{j+1}`. Then row `i`, counted from `0`, has length at most
`D.rowMainLength τ i + D.rowSlack i`. -/
lemma diagramWeight_le_rowMainLength_add_rowSlack {j : ℕ} (hj : j < D.m) (τ : D.Φ) (i : ℕ) :
    diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i) ≤
      D.rowMainLength τ i + D.rowSlack i := by
  have h_rows : (diagramWeight (rankAt fun _ : D.Φ ↦ D.X (j + 1)) D.columnCount (τ, i) : ℤ) ≤
      if i = 0 then (D.columnCount τ 1 + D.liftWeight (j + 1) τ : ℤ)
      else if i < D.k then (D.liftWeight (j + 1) τ : ℤ) else (D.m * D.gap : ℕ) := by
    rw [cast_diagramWeight_columnCount, columnCount_one, Nat.cast_mul]
    exact D.liftDiagram_le τ hj i
  have h_weight : D.liftWeight (j + 1) τ ≤ D.weight τ + D.m * D.gap + D.halfGap := by
    grw [liftWeight_eq, show j + 1 ≤ D.m from hj]
  have h_weight_le_natB : D.weight τ ≤ D.natB + D.offWeight := D.weight_le_natB_add_offWeight τ
  have h_gap_le : D.m * D.gap + D.halfGap ≤ D.halfGap ^ 2 := D.nat_le_of_hasLogBound
  rw [rowMainLength, rowSlack]
  -- In each of the three ranges of `i` the bound is linear in the four facts above.
  split_ifs at h_rows ⊢ <;> omega

/-- The integer `D.piMBar` of `K ⊆ ℂ` has norm `M = D.M`, so the image of its conjugate under any
automorphism `σ` of `ℂ` has squared absolute value `M`. -/
lemma norm_map_star_piMBar_sq (σ : ℂ ≃+* ℂ) : ‖σ (star (D.piMBar : P.K).val)‖ ^ 2 = D.M := by
  let ι : P.K →+* ℂ := σ.toRingHom.comp (ComplexEmbedding.conjugate P.K.val.toRingHom)
  have hι (z : P.K) : ι z = σ (star z.val) := rfl
  have h_norm : (D.piMBar : P.K) * star (D.piMBar : P.K) = D.M := by
    simpa [M] using congrArg (algebraMap (𝓞 P.K) P.K) D.piMBar_mul_star
  have h_conj : ‖ι (star (D.piMBar : P.K))‖ = ‖ι D.piMBar‖ := by simp
  calc ‖σ (star (D.piMBar : P.K).val)‖ ^ 2
    _ = ‖ι D.piMBar‖ * ‖ι (star (D.piMBar : P.K))‖ := by rw [h_conj, hι, sq]
    _ = D.M := by rw [← norm_mul, ← map_mul, h_norm, map_natCast, Complex.norm_natCast]

/-- Let `M = D.M = p₀ p₁` be the product of the two level primes of the data, let `E = D.E` and let
`Ω = P.bigOmega D.towerExp = exp (γ - Re L'/L(1, χ_K)) · 2π / rd_E`, with `γ` Euler's constant and
`rd_E` the root discriminant of `E`. For `l ≤ r + e` the jet size
`D.jetSize l = log l! + l log (M / Ω)`, which measures a derivative of order `l`, is at most
`D.jetSize r + e (log (r + e + 1) + log (M / Ω))`. -/
lemma jetSize_le_add {l r e : ℕ} (hl : l ≤ r + e) :
    D.jetSize l ≤
      D.jetSize r + (Real.log (↑(r + e) + 1) + Real.log (D.M / P.bigOmega D.towerExp)) * e := by
  -- `(r + e)!` is `r!` times `e` factors, each at most `r + e + 1`.
  have h_fact : l ! ≤ r ! * (r + e + 1) ^ e := calc
    l ! ≤ (r + e)! := factorial_le hl
    _ = r ! * (r + 1).ascFactorial e := (factorial_mul_ascFactorial r e).symm
    _ ≤ _ := by grw [ascFactorial_le_pow_add, (r + e).le_succ]
  have h_log_fact : Real.log l ! ≤ Real.log r ! + e * Real.log (↑(r + e) + 1) := by
    simpa (disch := positivity) [log_mul] using log_le_log (by positivity) (cast_le.2 h_fact)
  have h_linear : l * Real.log (D.M / P.bigOmega D.towerExp) ≤
      (r + e) * Real.log (D.M / P.bigOmega D.towerExp) :=
    mul_le_mul_of_nonneg_right (mod_cast hl) (log_nonneg D.le_of_hasLogBound)
  rw [jetSize, jetSize]
  linarith

/-! ### Class counts -/

/-- The admissible data `D` give a CM field `E = D.E`, the length `x = D.x` of the prime sum, the
number `m = D.m` of lifts and the rank `n_m = D.n D.m` of the last lift. Let `G ≥ 1` be an integer,
`n` an index set of size at most `2 n_m`, and `G_f` the finite adelic unitary group over `E` of the
form `∑_{i ∈ n} z_i \bar z_i`. If a subgroup `K` of `G_f` contains the principal congruence subgroup
of level `G`, then there are at most `exp (x ^ 29 (1 + log G))` double cosets `Γ \ G_f / K`. -/
lemma card_stdClasses_le_exp_mul_log {n : Type} [Fintype n] [DecidableEq n]
    {K : Subgroup (Gf D.E n)} (G : ℕ) [NeZero G] (hn : Fintype.card n ≤ 2 * D.n D.m)
    (hK : principalLevel n (G : 𝓞 D.E) ≤ K) :
    Nat.card (StdClasses K) ≤ exp (D.x ^ 29 * (1 + Real.log G)) := by
  -- The number of classes is at most the class number of the maximal level `K₀ = stdLevel` times
  -- the index of `K ∩ K₀` in `K₀`; both are bounded explicitly.
  have : Fact ((G : 𝓞 D.E) ≠ 0) := ⟨NeZero.out⟩
  have h_index_ne : (principalLevel n (G : 𝓞 D.E)).relIndex (stdLevel D.E n) ≠ 0 :=
    relIndex_ne_zero_of_isLevel _
  have : (K.subgroupOf (stdLevel D.E n)).FiniteIndex :=
    ⟨fun h_zero ↦ h_index_ne (relIndex_eq_zero_of_le_left hK h_zero)⟩
  let f : ℕ := Core.numInfPlaces D.E
  let r : ℕ := 2 * D.n D.m
  have h_index : K.relIndex (stdLevel D.E n) ≤ G ^ (2 * f * r ^ 2) := calc
    _ ≤ (principalLevel n (G : 𝓞 D.E)).relIndex (stdLevel D.E n) :=
      relIndex_le_of_le_left hK h_index_ne
    _ ≤ Ideal.absNorm (Ideal.span {(G : 𝓞 D.E)}) ^ Fintype.card n ^ 2 :=
      relIndex_principalLevel_le NeZero.out
    _ = G ^ (2 * f * Fintype.card n ^ 2) := by
      rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, finrank_eq_two_mul_card_infinitePlace,
        ← pow_mul]
    _ ≤ G ^ (2 * f * r ^ 2) := by
      gcongr
      exact NeZero.one_le
  -- Apply `Space.card_stdClasses_le` to the number `q₁ * d`, which lies in the different of `E`.
  let c : ℕ := 1 + 2 * (6 * (P.q₁ D.towerExp * P.d) * (f * r) ^ 2) ^ 3
  have h_class : Nat.card (StdClasses (stdLevel D.E n)) ≤ c ^ (4 * f * r ^ 2) := by
    refine (card_stdClasses_le P.conductor_mem_differentIdeal).trans ?_
    simp only [shortBasisConst, c, f, r]
    gcongr
    simp
  have h_log_c : 4 * f * (r : ℝ) ^ 2 * Real.log c ≤ D.x ^ 29 := by
    simpa only [r, c, f, cast_mul, cast_ofNat] using D.le_of_hasLogBound
  have h_exponent : 2 * f * (r : ℝ) ^ 2 ≤ D.x ^ 29 := by
    simpa only [r, f, cast_mul, cast_ofNat] using D.le_of_hasLogBound
  calc (Nat.card (StdClasses K) : ℝ)
    _ ≤ ↑(Nat.card (StdClasses (stdLevel D.E n)) * K.relIndex (stdLevel D.E n)) := by
      -- Every class for `K` is a class for the maximal level times a coset of `K ∩ K₀` in `K₀`.
      grw [card_le_card_of_surjective _ (surjective_doubleCoset_mk_mul _ (stdLevel D.E n) K),
        card_prod, ← index, ← relIndex]
    _ ≤ c ^ (4 * f * r ^ 2) * G ^ (2 * f * r ^ 2) := mod_cast mul_le_mul' h_class h_index
    _ = exp ((4 * f * r ^ 2 : ℕ) * Real.log c + (2 * f * r ^ 2 : ℕ) * Real.log G) := by
      rw [exp_add, exp_nat_mul, exp_nat_mul, exp_log (by positivity),
        exp_log (cast_pos.2 (NeZero.pos G))]
    _ ≤ exp (D.x ^ 29 * (1 + .log G)) := by
      push_cast
      grw [h_log_c, h_exponent, mul_add, mul_one]

/-- The admissible data `D` give a CM field `E = D.E`, the length `x = D.x` of the prime sum, the
level primes with product `M = D.M`, a further prime level `N = D.N`, and integers `D.piM`, `D.piN`
of `E` whose products with their conjugates are `M` and `N`. Let `n` be an index set with at most
`n_m = D.n D.m` elements and `G_f` the finite adelic unitary group over `E` of the form
`∑_{i ∈ n} z_i \bar z_i`, with group `Γ` of rational points. If a subgroup `K` of `G_f` contains the
principal congruence subgroup of level `D.piM * D.piN`, then there are at most `exp (x ^ 30)` double
cosets `Γ \ G_f / K`. -/
lemma card_stdClasses_le_exp {n : Type} [Fintype n] [DecidableEq n] {K : Subgroup (Gf D.E n)}
    (hK : principalLevel n (D.piM * D.piN) ≤ K) (hn : Fintype.card n ≤ D.n D.m) :
    Nat.card (StdClasses K) ≤ exp (D.x ^ 30) := by
  -- `K` contains the principal level of `M * N`, which is `piM * piN` times its conjugate.
  have h_dvd : D.piM * D.piN ∣ ↑(D.M * D.N) := by
    simp [← piM_mul_star, ← piN_mul_star, mul_dvd_mul]
  calc (Nat.card (StdClasses K) : ℝ)
    _ ≤ exp (D.x ^ 29 * (1 + .log ↑(D.M * D.N))) := D.card_stdClasses_le_exp_mul_log _
      (by lia) ((principalLevel_le_of_dvd h_dvd).trans hK)
    _ ≤ exp (D.x ^ 30) := by simpa using D.le_of_hasLogBound

/-! ### The sum of the allowed losses -/

/-- The allowed loss at `p`: it is `2 · D.loss p` for a non-split prime `p < x₁`, else `2 m f b` if
`p` is the level `N`, and `0` otherwise. -/
def allowedLoss (p : ℕ) : ℝ :=
  if p ∈ D.smallNonsplitPrimes then 2 * D.loss p else if p = D.N then (2 * D.m * D.f * D.b : ℝ) else
    0

lemma allowedLoss_nonneg (p : ℕ) : 0 ≤ D.allowedLoss p := by
  unfold allowedLoss loss
  positivity

/-- If `p ≥ 2` satisfies `D.IsPlusMinusOneModLifts p`, that is `p ≡ ±1` modulo the number `m = D.m`
of lifts, then `p = m c ± 1` for some `c` with `1 ≤ c ≤ p` and `m ≤ 2 p / c`. -/
lemma exists_mul_sub_one_eq_or_mul_add_one_eq {p : ℕ} (hp : 2 ≤ p)
    (hp_mod : D.IsPlusMinusOneModLifts p) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ p ∧ D.m ≤ 2 * p / c ∧ (D.m * c - 1 = p ∨ D.m * c + 1 = p) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, D.m * c = p + 1 ∨ D.m * c + 1 = p := by
    obtain ⟨c, hc⟩ | ⟨c, hc⟩ := hp_mod <;> exact ⟨c, by omega⟩
  have hc_pos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have h_two : 2 * c ≤ D.m * c := Nat.mul_le_mul_right c
    (le_trans (by norm_num) D.ten_thousand_le_m)
  exact ⟨c, hc_pos, by omega, (Nat.le_div_iff_mul_le hc_pos).2 (by omega), by omega⟩

/-- The admissible data `D` give a real number `x₁`, integers `x`, `b`, `a = x b`, `m`, a prime `N`
and a field `D.E` with `f` infinite places that contains `K = ℚ(√-d)`, for the prime `d = P.d`. For
every finite set `U` of natural numbers, the sum over `p ∈ U` of the allowed loss at `p` times
`log p` is at most `D.errorUnit = f a (log b)³`. -/
lemma sum_allowedLoss_mul_log_le (U : Finset ℕ) :
    ∑ p ∈ U, D.allowedLoss p * Real.log p ≤ D.errorUnit := by
  classical
  -- Each term is at most `T / c` for some `1 ≤ c ≤ x₁`, and each `c` serves at most the four
  -- numbers `N`, `m c - 1`, `c`, `m c + 1`. So the sum is at most `4 T` times a harmonic sum.
  -- The last factor `2` of `T` comes from `m ≤ 2 p / c` for `p = m c ± 1`.
  let T : ℝ := 2 * D.f * D.a * D.logB ^ 2 * D.logX₁ * 2
  let J : Finset (ℕ × ℕ) := Icc 1 ⌊D.x₁⌋₊ ×ˢ range 4
  -- `served (c, r)` is the `r`-th of the four numbers served by `c`.
  let served : ℕ × ℕ → ℕ := fun (c, r) ↦ [D.N, D.m * c - 1, c, D.m * c + 1][r]!
  have h_logX₁_nonneg : 0 ≤ D.logX₁ := (HasLogBound.pos D).le
  have h_single {p c r : ℕ} (hc_pos : 1 ≤ c) (hc_le : c ≤ ⌊D.x₁⌋₊) (hr : r < 4)
      (h_served : served (c, r) = p) : T / c ≤ ∑ u ∈ J with served u = p, T / u.1 :=
    single_le_sum (f := fun u : ℕ × ℕ ↦ T / u.1) (a := (c, r)) (fun u _ ↦ by positivity)
      (by simp [J, hc_pos, hc_le, hr, h_served])
  have h_term (p : ℕ) : D.allowedLoss p * .log p ≤ ∑ u ∈ J with served u = p, T / u.1 := by
    rw [allowedLoss]
    split_ifs with hp hN
    · -- A non-split prime `p < x₁`: take `c = p`, or `c` with `p = m c ± 1` if `p ≡ ±1` mod `m`.
      obtain ⟨hp_lt, hp_prime, -⟩ : p < D.x₁ ∧ p.Prime ∧ chiK P.d p ≠ 1 := by
        simpa [lt_ceil] using hp
      obtain ⟨c, r, hc_pos, hc_le, hr, h_served, h_factor⟩ : ∃ c r : ℕ, 1 ≤ c ∧ c ≤ p ∧ r < 4 ∧
          served (c, r) = p ∧ (if D.IsPlusMinusOneModLifts p then D.m else 1) ≤ 2 * p / c := by
        split_ifs with hp_mod
        · obtain ⟨c, hc_pos, hc_le, h_factor, h_eq | h_eq⟩ :=
            D.exists_mul_sub_one_eq_or_mul_add_one_eq hp_prime.two_le hp_mod
          exacts [⟨c, 1, hc_pos, hc_le, by norm_num, h_eq, h_factor⟩,
            ⟨c, 3, hc_pos, hc_le, by norm_num, h_eq, h_factor⟩]
        · exact ⟨p, 2, hp_prime.pos, le_rfl, by norm_num, rfl, by simp [hp_prime.pos]⟩
      have hp_pos : (0 : ℝ) < p := cast_pos.2 hp_prime.pos
      have h_log_p : Real.log p ≤ D.logX₁ := by grw [hp_lt, log_exp]
      calc 2 * D.loss p * Real.log p
        _ ≤ 2 * (D.f * D.logB ^ 2 * (D.a / p * (↑(2 * p) / c))) * D.logX₁ := by
          grw [loss, h_factor, h_log_p, cast_div_le]
        _ = T / c := by simp [T, field]
        _ ≤ _ := h_single hc_pos (hc_le.trans (le_floor hp_lt.le)) hr h_served
    · -- The level `N` takes `c = 1`.
      calc 2 * D.m * D.f * D.b * Real.log p
        _ ≤ T / (1 : ℕ) := by
          rw [hN]
          exact D.le_of_hasLogBound (by grind [log_nonneg, scale_inequalities])
        _ ≤ _ := h_single (r := 0) le_rfl (le_floor (by simpa)) (by norm_num) hN.symm
    · exact (zero_mul _).trans_le (by positivity)
  have h_harmonic : ∑ c ∈ Icc 1 ⌊D.x₁⌋₊, (c : ℝ)⁻¹ ≤ 1 + D.logX₁ := by
    simpa [harmonic_eq_sum_Icc] using harmonic_floor_le_one_add_log D.x₁ D.le_of_hasLogBound
  calc ∑ p ∈ U, D.allowedLoss p * .log p
    _ ≤ ∑ u ∈ J, T / u.1 := by grw [sum_le_sum fun p _ ↦ h_term p,
      sum_fiberwise_eq_sum_filter, filter_subset]
    _ = T * (4 * ∑ c ∈ Icc 1 ⌊D.x₁⌋₊, (c : ℝ)⁻¹) := by
      simp [J, sum_product, division_def, ← mul_sum]
    _ ≤ T * (4 * (1 + D.logX₁)) := by gcongr
    _ ≤ D.errorUnit := D.le_of_hasLogBound

end New.Data

end SizeEstimates

end
