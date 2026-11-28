import Lib.CM.FormalGroup.FormalParameter

/-!
# Frobenius congruence for `θ` and the coefficient of `z ^ (p - 1)` in `x`

Let `d ≡ 7` modulo `8` be a prime, `C` a lattice with complex multiplication by the integers of
`K = ℚ(√-d)`, and `p` a prime that does not split in `K`. This file proves that
`θ(π_p z) / θ(z) ^ q_p` is `1` modulo `π_p` in `𝒪[[y]]`. For `g = -log θ` it follows that
`q_p g(z) - g(π_p z)` lies in `π_p 𝒪[[y]]`. Independently of this congruence, it shows by a
recursion that at an inert prime the coefficient of `z ^ (p - 1)` in `x` is a unit; this is used in
the last step for the exponent on one curve (`New.CMLattice.norm_coeff_exponentSeries_eq_one`).

Notions from other files:
* `chiK d p` is the Legendre symbol `(p / d)`: it is `1`, `-1`, `0` when `p` is split, inert,
  ramified in `K`.
* `π_p = piPrime d p` is `√-d` for `p = d` and `p` otherwise; `q_p = primeNorm d p` is `p ^ 2` for
  inert `p` and `p` otherwise.
* `PadicPlace p` is the choice of a ring homomorphism `ιₚ : ℂ →+* ℂ_[p]`, and `taylorVia ιₚ f` is
  the Taylor series of `f` at `0`, with coefficients sent to `ℂ_[p]` by `ιₚ`.
* `θ`, `x`, `y` are the series of the theta function `C.θ`, of `C.translatedX z = ℘(z + t) - ℘(t)`
  and of `C.translatedY z = (℘'(z + t) - a₁ x(z)) / 2`. Here `t = C.t` is the chosen point of order
  two, the lattice is scaled so that `℘''(t) = 2`, and `a₁ = C.a₁` satisfies `a₁ ^ 2 = 12 ℘(t)`;
  moreover `g = C.negLogTheta = -log θ`.
* `C.integralSeriesRing = 𝒪[[y]]` is the ring of power series in `y` with coefficients in the
  valuation ring `𝒪` of `ℂ_[p]`.

## Main definitions and results

* `New.CMLattice.exists_rescale_theta_eq_pow_mul_one_add_smul`: at a non-split prime `p` the
  quotient `θ(π_p z) / θ(z) ^ q_p` is `1` modulo `π_p` in `𝒪[[y]]`.
* `New.CMLattice.exists_negLogTheta_frobenius_congruence`: `q_p g(z) - g(π_p z) ∈ π_p 𝒪[[y]]` for
  `g = -log θ`.
* `New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one`: at an inert prime `p` the coefficient
  of `z ^ (p - 1)` in the series `x` is a unit.
-/

/-!
## The Frobenius congruence for `θ`

The quotient `θ(π_p z) / θ(z) ^ q_p` is a polynomial in `x` of degree less than `q_p / 2`, so the
congruence can be checked below the degree `q_p`, where `π_p g` is integral.
-/

section FrobeniusCongruence

open PowerSeries IsUltrametricDist

namespace New
variable {d p : ℕ} [PrimeSevenModEight d] [Fact p.Prime]

/-- A prime `p` with `chiK d p ≠ 1`, that is, with Legendre symbol `(p / d) ≠ 1`, so that `p` does
not split in `ℚ(√-d)`, is odd (`p ≠ 2`), as `2` splits. -/
lemma ne_two_of_chiK_ne_one (hp : chiK d p ≠ 1) : p ≠ 2 := by
  rintro rfl
  exact hp QuadField.chiK_two

/-- Let `d ≡ 7` modulo `8` be a prime. If the prime `p` does not split in `ℚ(√-d)`, that is
`chiK d p ≠ 1`, then `primeNorm d p`, which is `p ^ 2` or `p`, is odd, since the prime `2`
splits. -/
lemma odd_primeNorm (hp : chiK d p ≠ 1) : Odd (primeNorm d p) := by
  obtain ⟨e, -, h_eq⟩ : ∃ e : ℕ, e ≠ 0 ∧ primeNorm d p = p ^ e := exists_primeNorm_eq_pow d p
  rw [h_eq]
  exact ((Fact.out : p.Prime).odd_of_ne_two (ne_two_of_chiK_ne_one hp)).pow

/-- If `p` is inert in `ℚ(√-d)`, then `p < q_p = primeNorm d p = p ^ 2`. -/
lemma lt_primeNorm_of_chiK_eq_neg_one (hp : chiK d p = -1) : p < primeNorm d p := by
  rw [primeNorm, ite_eq_left hp]
  exact lt_self_pow₀ (Fact.out : p.Prime).one_lt one_lt_two

variable [PadicPlace p]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`|q_p| = |π_p| ^ 2` in `ℂ_[p]`, as `q_p = ± π_p ^ 2`. -/
lemma norm_primeNorm (hp : chiK d p ≠ 1) : ‖(primeNorm d p : ℂ_[p])‖ = ‖ιₚ (piPrime d p)‖ ^ 2 := by
  obtain ⟨rfl, h_ram⟩ | ⟨hd, h_split | h_inert⟩ := chiK_cases d p
  · rw [piPrime, ite_eq_left rfl, ← norm_pow, map_I_mul_sqrt_sq, norm_neg, primeNorm, h_ram,
      ite_eq_right (by norm_num)]
  · exact absurd h_split hp
  · rw [piPrime, ite_eq_right hd, map_natCast, primeNorm, ite_eq_left h_inert, Nat.cast_pow,
      norm_pow]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`|π_p| ≤ p ^ (-1 / (p - 1))` in `ℂ_[p]`, as `p ≥ 3` (the prime `2` splits) and the valuation of
`π_p` is at least `1 / 2`. -/
lemma norm_piPrime_le_rpow (hp : chiK d p ≠ 1) :
    ‖ιₚ (piPrime d p)‖ ≤ p ^ (-(1 / (p - 1)) : ℝ) := by
  have h_three : (3 : ℝ) ≤ p :=
    mod_cast (Fact.out : p.Prime).two_le.lt_of_ne' (ne_two_of_chiK_ne_one hp)
  have h_exponent : 1 / (p - 1 : ℝ) ≤ piPrimeValuation d p :=
    (one_div_le_one_div_of_le two_pos (by linarith)).trans (half_le_piPrimeValuation d p)
  rw [norm_piPrime]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg h_exponent)

/-- Let `d ≡ 7` modulo `8` and `p` be primes. Then `|π_p| ≤ |√-d|` in `ℂ_[p]`, via the homomorphism
`ιₚ : ℂ →+* ℂ_[p]` that `PadicPlace p` chooses. -/
lemma norm_piPrime_le_norm_sqrt_neg : ‖ιₚ (piPrime d p)‖ ≤ ‖ιₚ (.I * √d)‖ := by
  obtain rfl | hd := eq_or_ne p d
  · rw [piPrime, ite_eq_left rfl]
  · have h_sq : ‖ιₚ (.I * √d)‖ ^ 2 = 1 := by
      rw [← norm_pow, map_I_mul_sqrt_sq, norm_neg,
        ((Nat.coprime_primes Fact.out Fact.out).2 hd).norm_natCast_eq_one]
    rw [(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h_sq]
    exact (norm_piPrime_lt_one d).le

/-- Let `d ≡ 7` modulo `8` and `p` be primes. Then `|π_p| ≤ |n|` in `ℂ_[p]` for `0 < n < q_p`. -/
lemma norm_piPrime_le_norm_natCast {n : ℕ} (hn_ne : n ≠ 0) (hn : n < primeNorm d p) :
    ‖ιₚ (piPrime d p)‖ ≤ ‖(n : ℂ_[p])‖ := by
  have hp : p.Prime := Fact.out
  by_cases h_inert : chiK d p = -1
  · have hd : p ≠ d := by
      rintro rfl
      simp [chiK, ZMod.natCast_self] at h_inert
    have hn_lt : n < p ^ 2 := by rwa [primeNorm, ite_eq_left h_inert] at hn
    have h_pow_le : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn_ne.bot_lt pow_padicValNat_dvd
    have h_val : padicValNat p n ≤ 1 :=
      Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right hp.one_lt).1 (h_pow_le.trans_lt hn_lt))
    rw [piPrime, ite_eq_right hd, map_natCast, norm_p_eq_inv,
      norm_natCast_eq_inv_pow_padicValNat hn_ne]
    calc (p : ℝ)⁻¹ = (p : ℝ)⁻¹ ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ)⁻¹ ^ padicValNat p n :=
        pow_le_pow_of_le_one (by positivity) p.cast_inv_le_one h_val
  · have hn_lt : n < p := by rwa [primeNorm, ite_eq_right h_inert] at hn
    rw [(Nat.coprime_of_lt_prime hn_ne hn_lt hp).norm_natCast_eq_one]
    exact (norm_piPrime_lt_one d).le

/-- Let `d ≡ 7` modulo `8` and `p` be primes. Then `|π_p| ≤ |(k + 2) (k + 1)|` in `ℂ_[p]` for
`k + 2 < q_p`, as one of the two factors is prime to `p`. -/
lemma norm_piPrime_le_norm_mul_succ {k : ℕ} (hk : k + 2 < primeNorm d p) :
    ‖ιₚ (piPrime d p)‖ ≤ ‖((k + 2 : ℕ) : ℂ_[p]) * (k + 1 : ℕ)‖ := by
  have hp : p.Prime := Fact.out
  rw [norm_mul]
  by_cases h_dvd : p ∣ k + 1
  · have h_coprime : p.Coprime (k + 2) := hp.coprime_iff_not_dvd.2
      fun h_dvd_succ ↦ hp.not_dvd_one ((Nat.dvd_add_right h_dvd).1 h_dvd_succ)
    rw [h_coprime.norm_natCast_eq_one, one_mul]
    exact norm_piPrime_le_norm_natCast k.succ_ne_zero (by omega)
  · rw [(hp.coprime_iff_not_dvd.2 h_dvd).norm_natCast_eq_one, mul_one]
    exact norm_piPrime_le_norm_natCast (k + 1).succ_ne_zero hk

namespace CMLattice
variable (C : CMLattice d)

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`θ(π_p z) = θ(z) ^ q_p * R(x(z))` as power series over `ℂ_[p]`, for a polynomial `R` of degree less
than `q_p / 2`. -/
lemma exists_rescale_theta_eq_pow_mul_aeval (hp : chiK d p ≠ 1) :
    ∃ R : Polynomial ℂ_[p],
      2 * R.natDegree < primeNorm d p ∧
      rescale (ιₚ (piPrime d p)) (taylorVia ιₚ C.θ) =
        taylorVia ιₚ C.θ ^ primeNorm d p * R.aeval (taylorVia ιₚ C.translatedX) := by
  -- `θ(π z)` is an even section of degree `q` with integral torsion values.
  have h_isog : C.IsIsogeny C.periodPair (piPrime d p) (primeNorm d p) :=
    ⟨C.mul_mem_of_quadInt (piPrime_mem_quadInt d), by rw [piPrime_mul_conj d hp]⟩
  let f : ℂ → ℂ := fun z ↦ C.θ (piPrime d p * z)
  have h_mem : f ∈ C.sections (primeNorm d p) := by
    simpa only [one_mul] using C.comp_mul_mem_sections h_isog C.theta_mem
  have h_int : C.HasIntegralValues (primeNorm d p) f := by
    simpa only [one_mul] using C.hasIntegralValues_theta.comp_isogeny h_isog
  have h_even : f.Even := fun z ↦ by simp only [f, mul_neg, theta_neg]
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℂ, C.IsIntegralEvenExpansion (primeNorm d p) f R :=
    C.exists_polynomial_of_even h_mem h_int h_even
  refine ⟨R.map ιₚ, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : Odd (primeNorm d p) := odd_primeNorm hp
    have h_deg : 2 * R.natDegree ≤ primeNorm d p := hR.two_mul_natDegree_le
    grind [Polynomial.natDegree_map]
  · rw [← hR.taylorVia_eq, taylorVia, taylorVia, taylorAtZero_comp_mul, rescale_map]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. Then
`|π_p| |g_n| ≤ 1` for the `n`-th coefficient `g_n` of `g` and `n < q_p`. -/
lemma norm_piPrime_mul_coeff_negLogTheta_le_one (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < primeNorm d p) : ‖ιₚ (piPrime d p)‖ * ‖coeff n C.negLogTheta‖ ≤ 1 := by
  match n with
  | 0 => simp [constantCoeff_negLogTheta]
  | 1 => simp [coeff_one_negLogTheta]
  | 2 =>
    have h_two : ‖(2 : ℂ_[p])‖ = 1 := mod_cast Nat.Coprime.norm_natCast_eq_one
      ((Nat.coprime_primes Fact.out Nat.prime_two).2 (ne_two_of_chiK_ne_one hp)) ℂ_[p]
    have h_sqrt : ‖ιₚ (.I * √d)‖ * ‖coeff 2 C.negLogTheta‖ ≤ 1 := by
      simpa only [norm_mul, h_two, one_mul] using C.norm_sqrt_mul_coeff_two_negLogTheta_le_one
    exact (mul_le_mul_of_nonneg_right norm_piPrime_le_norm_sqrt_neg (norm_nonneg _)).trans h_sqrt
  | k + 3 =>
    -- Compare the coefficients of `z ^ (k + 1)` in `g'' = g''(0) + x`.
    have h_coeff : ((k + 1 + 2 : ℕ) : ℂ_[p]) * (k + 1 + 1 : ℕ) * coeff (k + 3) C.negLogTheta =
        coeff (k + 1) (taylorVia ιₚ C.translatedX) := by
      have h_coeff_eq : coeff (k + 1) (d⁄dX (d⁄dX C.negLogTheta)) =
          coeff (k + 1) (taylorVia ιₚ C.translatedX) := by
        rw [C.derivative_derivative_negLogTheta, map_add, coeff_succ_C, zero_add]
      rw [← h_coeff_eq, coeff_derivative, coeff_derivative]
      push_cast
      ring
    calc ‖ιₚ (piPrime d p)‖ * ‖coeff (k + 3) C.negLogTheta‖
        ≤ ‖((k + 1 + 2 : ℕ) : ℂ_[p]) * (k + 1 + 1 : ℕ)‖ * ‖coeff (k + 3) C.negLogTheta‖ :=
          mul_le_mul_of_nonneg_right (norm_piPrime_le_norm_mul_succ hn) (norm_nonneg _)
      _ = ‖coeff (k + 1) (taylorVia ιₚ C.translatedX)‖ := by rw [← norm_mul, h_coeff]
      _ ≤ 1 := C.norm_coeff_le_one_of_lt C.taylorVia_translatedX_mem_integralSeriesRing (by omega)

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split in `ℚ(√-d)`. For `n < q_p`
the `n`-th coefficient `(q_p - π_p ^ n) g_n` of `q_p g(z) - g(π_p z)` has norm at most `|π_p|`. -/
lemma norm_coeff_smul_negLogTheta_sub_rescale_le (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < primeNorm d p) :
    ‖coeff n ((primeNorm d p : ℂ_[p]) • C.negLogTheta -
      rescale (ιₚ (piPrime d p)) C.negLogTheta)‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  rw [map_sub, coeff_smul, coeff_rescale, smul_eq_mul, ← sub_mul, norm_mul]
  match n with
  | 0 => simp [constantCoeff_negLogTheta]
  | 1 => simp [coeff_one_negLogTheta]
  | k + 2 =>
    have h_bound : ‖ιₚ (piPrime d p)‖ * ‖coeff (k + 2) C.negLogTheta‖ ≤ 1 :=
      C.norm_piPrime_mul_coeff_negLogTheta_le_one hp hn
    set π : ℂ_[p] := ιₚ (piPrime d p)
    have h_factor : ‖(primeNorm d p : ℂ_[p]) - π ^ (k + 2)‖ ≤ ‖π‖ ^ 2 := by
      rw [sub_eq_add_neg]
      refine (norm_add_le_max _ _).trans (max_le (norm_primeNorm hp).le ?_)
      rw [norm_neg, norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg π) (norm_piPrime_lt_one d).le (Nat.le_add_left 2 k)
    calc ‖(primeNorm d p : ℂ_[p]) - π ^ (k + 2)‖ * ‖coeff (k + 2) C.negLogTheta‖
        ≤ ‖π‖ ^ 2 * ‖coeff (k + 2) C.negLogTheta‖ := by gcongr
      _ = ‖π‖ * (‖π‖ * ‖coeff (k + 2) C.negLogTheta‖) := by ring
      _ ≤ ‖π‖ := mul_le_of_le_one_right (norm_nonneg π) h_bound

/-- The Frobenius congruence. Let `d ≡ 7` modulo `8` be a prime and `p` a prime that does not split
in `ℚ(√-d)`. The Taylor series of `θ` at `0`, mapped by the chosen `ιₚ : ℂ →+* ℂ_[p]`, satisfies
`θ(π_p z) = θ(z) ^ q_p * (1 + π_p H)` for some `H ∈ 𝒪[[y]]`. -/
lemma exists_rescale_theta_eq_pow_mul_one_add_smul (hp : chiK d p ≠ 1) :
    ∃ H : ℂ_[p]⟦X⟧, H ∈ C.integralSeriesRing ∧
      rescale (ιₚ (piPrime d p)) (taylorVia ιₚ C.θ) =
        taylorVia ιₚ C.θ ^ primeNorm d p * (1 + ιₚ (piPrime d p) • H) := by
  set π : ℂ_[p] := ιₚ (piPrime d p)
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX
  obtain ⟨R, h_deg, hR⟩ : ∃ R : Polynomial ℂ_[p], 2 * R.natDegree < primeNorm d p ∧
      rescale π (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ primeNorm d p * R.aeval x :=
    C.exists_rescale_theta_eq_pow_mul_aeval hp
  have hx : x ∈ C.integralSeriesRing := C.taylorVia_translatedX_mem_integralSeriesRing
  -- `R(x) = exp (q g(z) - g(π z))` is `1` modulo `π` below the degree `q`.
  have h_low (n : ℕ) (hn : n < primeNorm d p) : ‖coeff n ((R - 1).aeval x)‖ ≤ ‖π‖ := by
    rw [map_sub, map_one, ← C.expSubst_smul_negLogTheta_sub_rescale_eq hR]
    exact norm_coeff_expSubst_sub_one_le (norm_piPrime_le_rpow hp)
      (constantCoeff_smul_sub_rescale C.constantCoeff_negLogTheta _ _)
      (fun k hk ↦ C.norm_coeff_smul_negLogTheta_sub_rescale_le hp hk) hn
  -- Hence `π` divides the coefficients of `R - 1`, as `x = z ^ 2 + ⋯` is integral in these degrees.
  have h_dvd (i : ℕ) (hi : 2 * i < primeNorm d p) : ‖(R - 1).coeff i‖ ≤ ‖π‖ :=
    norm_coeff_le_of_aeval C.X_sq_dvd_taylorVia_translatedX C.coeff_two_taylorVia_translatedX
      (fun k hk ↦ C.norm_coeff_le_one_of_lt hx hk) h_low hi
  have h_deg_le : (R - 1).natDegree ≤ R.natDegree := by simpa using R.natDegree_sub_le 1
  refine ⟨π⁻¹ • (R - 1).aeval x, ?_, ?_⟩
  · rw [Polynomial.aeval_eq_sum_range, Finset.smul_sum]
    refine sum_mem fun i hi ↦ ?_
    rw [smul_smul]
    refine C.isSeriesGenerator_translatedY.smul_mem ?_ (pow_mem hx i)
    rw [norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (h_dvd i (by grind)) (norm_nonneg π)
  · rw [smul_inv_smul₀ ((map_ne_zero ιₚ).2 (piPrime_ne_zero d)), map_sub, map_one, add_sub_cancel,
      hR]

/-- The logarithm of the Frobenius congruence. Let `d ≡ 7` modulo `8` be a prime and `p` a prime
that does not split in `ℚ(√-d)`. Then `q_p g(z) - g(π_p z) = π_p H` for some `H ∈ 𝒪[[y]]`. -/
lemma exists_negLogTheta_frobenius_congruence (hp : chiK d p ≠ 1) :
    ∃ H : ℂ_[p]⟦X⟧, H ∈ C.integralSeriesRing ∧
      (primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale (ιₚ (piPrime d p)) C.negLogTheta =
        ιₚ (piPrime d p) • H := by
  set π : ℂ_[p] := ιₚ (piPrime d p)
  obtain ⟨H, hH, h_eq⟩ : ∃ H : ℂ_[p]⟦X⟧, H ∈ C.integralSeriesRing ∧
      rescale π (taylorVia ιₚ C.θ) = taylorVia ιₚ C.θ ^ primeNorm d p * (1 + π • H) :=
    C.exists_rescale_theta_eq_pow_mul_one_add_smul hp
  have hπ : π ≠ 0 := (map_ne_zero ιₚ).2 (piPrime_ne_zero d)
  let G : ℂ_[p]⟦X⟧ := π⁻¹ • ((primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale π C.negLogTheta)
  have hG : π • G = (primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale π C.negLogTheta :=
    smul_inv_smul₀ hπ _
  have hG_zero : constantCoeff G = 0 := by
    rw [constantCoeff_smul, constantCoeff_smul_sub_rescale C.constantCoeff_negLogTheta, smul_zero]
  have h_exp : expSubst (π • G) = 1 + π • H := by
    rw [hG, C.expSubst_smul_negLogTheta_sub_rescale_eq h_eq]
  exact ⟨G, C.isSeriesGenerator_translatedY.mem_of_expSubst_smul_eq hπ (norm_piPrime_le_rpow hp)
    hG_zero hH h_exp, hG.symm⟩

end CMLattice

end New

end FrobeniusCongruence

/-!
## The coefficient of `z ^ (p - 1)` in `x` at an inert prime

The numbers `h_n = [z ^ (p - 1)] x ^ n` satisfy a three-term recursion modulo `p` that leads from
`h_0 = 0` and `h_1` to `h_((p - 1) / 2) = 1`.
-/

section SupersingularCoeff

open PowerSeries IsUltrametricDist

namespace New.CMLattice

section Derivatives
variable {d : ℕ} (C : CMLattice d)
variable {K : Type*} [Field K] [CharZero K] (ι : ℂ →+* K)

/-- `x'² = 4 x³ + a₁² x² + 4 x` for the Taylor series `x` of `℘(z + t) - ℘(t)`, with coefficients
mapped to `K` by `ι`. -/
lemma derivative_taylorVia_translatedX_sq :
    d⁄dX (taylorVia ι C.translatedX) ^ 2 = 4 * taylorVia ι C.translatedX ^ 3 +
      .C (ι C.a₁) ^ 2 * taylorVia ι C.translatedX ^ 2 + 4 * taylorVia ι C.translatedX := by
  rw [derivative_taylorVia_translatedX]
  linear_combination 4 * C.taylorVia_curve_eq ι

/-- `x'' = 6 x² + a₁² x + 2` for the Taylor series `x` of `℘(z + t) - ℘(t)`, with coefficients
mapped to `K` by `ι`. -/
lemma derivative_derivative_taylorVia_translatedX :
    d⁄dX (d⁄dX (taylorVia ι C.translatedX)) = 6 * taylorVia ι C.translatedX ^ 2 +
      .C (ι C.a₁) ^ 2 * taylorVia ι C.translatedX + 2 := by
  have h_deriv : d⁄dX (d⁄dX (taylorVia ι C.translatedX)) =
      2 * d⁄dX (taylorVia ι C.translatedY) +
        .C (ι C.a₁) * d⁄dX (taylorVia ι C.translatedX) := by
    conv_lhs => rw [derivative_taylorVia_translatedX]
    simp [two_mul, Derivation.leibniz]
  rw [h_deriv, derivative_taylorVia_translatedY, derivative_taylorVia_translatedX]
  ring

/-- `(xⁿ x')' = (4 n + 6) xⁿ⁺² + (n + 1) a₁² xⁿ⁺¹ + (4 n + 2) xⁿ` for the Taylor series `x` of
`℘(z + t) - ℘(t)`, with coefficients mapped to `K` by `ι`. -/
lemma derivative_pow_mul_derivative_taylorVia_translatedX (n : ℕ) :
    d⁄dX (taylorVia ι C.translatedX ^ n * d⁄dX (taylorVia ι C.translatedX)) =
      (4 * n + 6 : K) • taylorVia ι C.translatedX ^ (n + 2) +
      ((n + 1) * ι C.a₁ ^ 2 : K) • taylorVia ι C.translatedX ^ (n + 1) +
      (4 * n + 2 : K) • taylorVia ι C.translatedX ^ n := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_derivative_taylorVia_translatedX]
  simp only [smul_eq_C_mul, smul_eq_mul, nsmul_eq_mul, map_add, map_mul, map_pow, map_ofNat,
    map_natCast, map_one]
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel]
    push_cast
    linear_combination
      (n + 1) * taylorVia ι C.translatedX ^ n * C.derivative_taylorVia_translatedX_sq ι

end Derivatives

variable {d : ℕ} (C : CMLattice d) [PrimeSevenModEight d]
variable {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that is inert in `ℚ(√-d)`. The numbers
`h_n = [z ^ (p - 1)] x ^ n` satisfy a recursion modulo the maximal ideal: `(4 n + 6)
h_(n + 2) + (n + 1) a₁² h_(n + 1) + (4 n + 2) h_n` has norm less than `1`. -/
lemma norm_coeff_pow_taylorVia_translatedX_recursion_lt_one (hp : chiK d p = -1) (n : ℕ) :
    ‖(4 * n + 6) * coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 2)) +
      (n + 1) * ιₚ C.a₁ ^ 2 * coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 1)) +
      (4 * n + 2) * coeff (p - 1) (taylorVia ιₚ C.translatedX ^ n)‖ < 1 := by
  -- This is the coefficient of `z ^ (p - 1)` in `(xⁿ x')'`, so `p` times an integral number.
  set x : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedX with hx
  have hx_mem : x ∈ C.integralSeriesRing := C.taylorVia_translatedX_mem_integralSeriesRing
  have h_int : ‖coeff p (x ^ n * d⁄dX x)‖ ≤ 1 := C.norm_coeff_le_one_of_lt
    (mul_mem (pow_mem hx_mem n) (C.derivative_mem_integralSeriesRing hx_mem))
    (lt_primeNorm_of_chiK_eq_neg_one hp)
  have h_deriv : coeff (p - 1) (d⁄dX (x ^ n * d⁄dX x)) =
      coeff p (x ^ n * d⁄dX x) * (p : ℂ_[p]) := by
    rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  calc _ = ‖coeff (p - 1) (d⁄dX (x ^ n * d⁄dX x))‖ := by
        simp only [hx, C.derivative_pow_mul_derivative_taylorVia_translatedX ιₚ n, map_add,
          coeff_smul, smul_eq_mul]
    _ = ‖coeff p (x ^ n * d⁄dX x)‖ * ‖(p : ℂ_[p])‖ := by rw [h_deriv, norm_mul]
    _ < 1 := (mul_le_of_le_one_left (norm_nonneg _) h_int).trans_lt norm_p_lt_one

omit [PrimeSevenModEight d] in
/-- The coefficient of `z ^ (2 m)` in `x ^ m` is `1`, as the Taylor series `x` of
`℘(z + t) - ℘(t)`, mapped by `ιₚ : ℂ →+* ℂ_[p]`, is `z² + ⋯`. Here `t = C.t` is the chosen point of
order two, with `℘''(t) = 2`. -/
lemma coeff_two_mul_taylorVia_translatedX_pow (m : ℕ) :
    coeff (2 * m) (taylorVia ιₚ C.translatedX ^ m) = (1 : ℂ_[p]) := by
  obtain ⟨u, hu⟩ : X ^ 2 ∣ taylorVia ιₚ C.translatedX := C.X_sq_dvd_taylorVia_translatedX
  have hu_one : constantCoeff u = 1 := by
    simpa [hu, coeff_X_pow_mul'] using C.coeff_two_taylorVia_translatedX (p := p)
  simp [hu, mul_pow, ← pow_mul, coeff_X_pow_mul', hu_one]

/-- Let `d ≡ 7` modulo `8` be a prime and `p = 2 m + 1` a prime that is inert in `ℚ(√-d)`. If the
coefficient of `z ^ (p - 1)` in `x` has norm less than `1`, then so does that in `x ^ n` for every
`n ≤ m`, by the recursion for these coefficients. -/
lemma norm_coeff_pow_taylorVia_translatedX_lt_one (hp : chiK d p = -1) {m : ℕ}
    (hp_eq : p = 2 * m + 1) (h_lt : ‖coeff (p - 1) (taylorVia ιₚ C.translatedX)‖ < 1)
    {n : ℕ} (hn : n ≤ m) :
    ‖coeff (p - 1) (taylorVia ιₚ C.translatedX ^ n)‖ < 1 := by
  have hp_prime : p.Prime := Fact.out
  induction n using Nat.twoStepInduction with
  | zero => simp [coeff_one, Nat.sub_ne_zero_of_lt hp_prime.one_lt]
  | one => simpa only [pow_one] using h_lt
  | more n ih₀ ih₁ =>
    set c₀ : ℂ_[p] := coeff (p - 1) (taylorVia ιₚ C.translatedX ^ n)
    set c₁ : ℂ_[p] := coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 1))
    set c₂ : ℂ_[p] := coeff (p - 1) (taylorVia ιₚ C.translatedX ^ (n + 2))
    have h_rec : ‖(4 * n + 6) * c₂ + (n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀‖ < 1 :=
      C.norm_coeff_pow_taylorVia_translatedX_recursion_lt_one hp n
    -- `4 n + 6 = 2 (2 n + 3)` with `p` odd and `2 n + 3 < p`.
    have h_coprime : p.Coprime (2 * (2 * n + 3)) :=
      .mul_right (Nat.coprime_two_right.2 ⟨m, hp_eq⟩)
        (Nat.coprime_of_lt_prime (Nat.succ_ne_zero _) (by omega) hp_prime)
    have h_unit : ‖(4 * n + 6 : ℂ_[p])‖ = 1 := by
      rw [← h_coprime.norm_natCast_eq_one ℂ_[p]]
      norm_num [mul_add, ← mul_assoc]
    have h_factor₁ : ‖(n + 1) * ιₚ C.a₁ ^ 2‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      refine (mul_le_of_le_one_left (by positivity) ?_).trans
        (pow_le_one₀ (norm_nonneg _) C.norm_a₁_le_one)
      exact_mod_cast norm_natCast_le_one ℂ_[p] (n + 1)
    have h_lower : ‖(n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀‖ < 1 :=
      norm_lt_one_of_eq_mul_add_mul h_factor₁ (mod_cast norm_natCast_le_one ℂ_[p] (4 * n + 2))
        rfl (ih₁ (by omega)) (ih₀ (by omega))
    calc ‖c₂‖ = ‖(4 * n + 6) * c₂‖ := by rw [norm_mul, h_unit, one_mul]
      _ = ‖((4 * n + 6) * c₂ + (n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀) +
            -((n + 1) * ιₚ C.a₁ ^ 2 * c₁ + (4 * n + 2) * c₀)‖ := by ring_nf
      _ < 1 := (norm_add_le_max _ _).trans_lt (max_lt h_rec (by rwa [norm_neg]))

/-- Let `d ≡ 7` modulo `8` be a prime and `p` a prime that is inert in `ℚ(√-d)`. The coefficient of
`z ^ (p - 1)` in the Taylor series `x` of `℘(z + t) - ℘(t)`, mapped by `ιₚ : ℂ →+* ℂ_[p]`, has norm
`1`. -/
lemma norm_coeff_taylorVia_translatedX_eq_one (hp : chiK d p = -1) :
    ‖coeff (p - 1) (taylorVia ιₚ C.translatedX)‖ = 1 := by
  -- If this coefficient is not a unit, neither is that in `x ^ m` for `p = 2 m + 1`, which is `1`.
  obtain ⟨m, hp_eq⟩ : Odd p :=
    (Fact.out : p.Prime).odd_of_ne_two (ne_two_of_chiK_ne_one (by simp [hp] : chiK d p ≠ 1))
  have h_le : ‖coeff (p - 1) (taylorVia ιₚ C.translatedX)‖ ≤ 1 :=
    C.norm_coeff_le_one_of_lt C.taylorVia_translatedX_mem_integralSeriesRing
      ((Nat.sub_le p 1).trans_lt (lt_primeNorm_of_chiK_eq_neg_one hp))
  refine h_le.eq_of_not_lt fun h_lt ↦ ?_
  have h_last : ‖coeff (p - 1) (taylorVia ιₚ C.translatedX ^ m)‖ < 1 :=
    C.norm_coeff_pow_taylorVia_translatedX_lt_one hp hp_eq h_lt le_rfl
  simp [show p - 1 = 2 * m by omega, C.coeff_two_mul_taylorVia_translatedX_pow m] at h_last

end New.CMLattice

end SupersingularCoeff
