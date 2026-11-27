import Lib.General.Algebra.SeriesCongruences
import New.Derivatives.FormalGroup.FrobeniusCongruence

/-!
# The exponent on one curve

Let `d ≡ 7` mod `8` be a prime (`PrimeSevenModEight d`), let `p` be a prime that does not split in
`ℚ(√-d)`, and let `𝒪` (`valRingCp p`) be the ring of integers of `ℂ_p`; a series is integral if its
coefficients lie in `𝒪`.

* `New.CMLattice.exists_exponent_tsum`: for some `ϖ` of valuation `ρ_p` the series `θ(ϖ z)` is
  integral up to one exponential `exp (c_ϖ Ξ₁)`, where `c_ϖ = ϖ ^ (p + 1) / p`, the series `Ξ₁` is
  integral, and modulo `π_p` it has only terms `(z ^ p ^ e * z) ^ p ^ j` with `e ∈ I_p°`
  (`partnerExponents d p`: the odd numbers, and all numbers if `p = d`).

The proof has four steps.

1. Averaging `ζ ^ (-p - 1) g(ζ z)` over the `(q_p - 1)`-th roots of unity `ζ` replaces `g = -log θ`
   by its part `g^♭` in the degrees `≡ p + 1` mod `q_p - 1`.
2. The Frobenius congruence gives a functional equation for `Ξ₁ = -g^♭(ϖ z) / c_ϖ`.
3. The equation is solved degree by degree. With `Y = T(ϖ z) / ϖ ≡ ∑_j z ^ q_p ^ j` and a number
   `λ ∈ 𝒪` one has `Ξ₁ ≡ λ Y ^ (p + 1)` for inert `p` and `Ξ₁ ≡ λ (Y ^ 2 - z ^ 2 / 2)` for `p = d`.
   The coefficients of the terms are `λ` in the first case, and `λ / 2`, `λ` or `2 λ` in the second.
4. For inert `p` the coefficient of `z ^ (p + 1)` in `Ξ₁` is a unit, and so is `λ`.

Notions from other files:
* `chiK d p` is the Legendre symbol `(p / d)`; the prime `p` is non-split if `chiK d p ≠ 1`.
* `q_p = primeNorm d p` is the norm of a prime above `p`, `π_p = piPrime d p` is `√-d` if `p = d`
  and `p` otherwise, and `ρ_p = varpiValuation d p` is `v(π_p) / (q_p - 1)` with `v(p) = 1`.
* `C : CMLattice d` is a lattice in `ℂ` that is stable under the ring of integers of `ℚ(√-d)`, with
  a chosen point `t` of order two.
* `taylorVia ιₚ C.θ` is the Taylor series over `ℂ_p` of the theta function `θ` of `C`, along the
  embedding `ιₚ : ℂ →+* ℂ_[p]` fixed by `PadicPlace p`, and `C.negLogTheta` is `g = -log θ`.
* `C.integralSeriesRing` is the ring `𝒪[[y]] = 𝒪[[T]]`, where `y` is the Taylor series of
  `C.translatedY` and `T = C.formalParam` is the formal parameter.

## Relation to the literature

Earlier bounds for one curve at inert primes, which are not used: Bannai–Kobayashi, Algebraic theta
functions and the p-adic interpolation of Eisenstein–Kronecker numbers (first arXiv version, Theorem
4.1); Bannai–Kobayashi, Integral structures on p-adic Fourier theory; Bannai–Kobayashi–Yasuda, The
radius of convergence of the p-adic sigma function; Fujiwara, On divisibilities of special values of
real analytic Eisenstein series.
-/

open PowerSeries Finset

namespace New

/-- The least positive degree `i₀ ≡ p + 1` mod `q_p - 1` at a non-split prime: `2` if `p = d`, and
`p + 1` if `p` is inert. -/
def leastFlatDegree (d p : ℕ) : ℕ := if p = d then 2 else p + 1

lemma leastFlatDegree_pos (d p : ℕ) : 0 < leastFlatDegree d p := by
  grind [leastFlatDegree]

/-- Let `G` be a series over the ring of integers `𝒪 = valRingCp p` of `ℂ_p`, read over `ℂ_p` by
`seriesToCp`, and let `i < m`. The part `congruencePart m i` of `G` in the degrees `≡ i` mod `m` is
`l X ^ i + X ^ (i + m) H` with `l ∈ 𝒪` and `H ∈ 𝒪[[X]]`. -/
lemma exists_congruencePart_eq_smul_X_pow_add {p : ℕ} [Fact p.Prime] {m i : ℕ} (hi : i < m)
    (G : (valRingCp p)⟦X⟧) :
    ∃ (l : valRingCp p) (H : (valRingCp p)⟦X⟧),
      congruencePart m i (seriesToCp G) = (l : ℂ_[p]) • X ^ i + X ^ (i + m) * seriesToCp H := by
  refine ⟨coeff i G, mk fun k ↦ if i + m + k ≡ i [MOD m] then coeff (i + m + k) G else 0, ?_⟩
  ext n
  simp only [congruencePart, coeff_mk, map_add, coeff_smul, coeff_X_pow, coeff_X_pow_mul',
    coeff_seriesToCp, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h_large : i + m ≤ n
  · -- From the degree `i + m` on the part agrees with the shifted series.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_large
    rw [ite_eq_right (by omega : i + m + k ≠ i), ite_eq_left h_large, Nat.add_sub_cancel_left,
      zero_add]
    split_ifs <;> rfl
  · -- Below the degree `i + m` only the degree `i` is congruent to `i`.
    have h_iff : n ≡ i [MOD m] ↔ n = i :=
      ⟨fun h ↦ h.eq_of_abs_lt (abs_lt.2 (by omega)), fun h ↦ by rw [h]⟩
    simp only [h_iff, ite_eq_right h_large, add_zero]
    split_ifs with h_eq <;> simp [h_eq]

/-- A number of norm `p ^ r` is not zero. -/
lemma ne_zero_of_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} {r : ℝ}
    (hx : ‖x‖ = (p : ℝ) ^ r) : x ≠ 0 := by
  rw [← norm_pos_iff, hx]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _

/-- Let `𝒪 = valRingCp p` be the ring of integers of `ℂ_p`. A series `F` over `ℂ_p` whose
coefficients are congruent modulo `π ∈ 𝒪` to those of an integral series `G` comes from an integral
series `Ξ` by `seriesToCp`, and `Ξ ≡ G` modulo `π`. -/
lemma exists_seriesToCp_eq_and_C_dvd_sub {p : ℕ} [Fact p.Prime] {π : valRingCp p} {F : ℂ_[p]⟦X⟧}
    {G : (valRingCp p)⟦X⟧} (h : ∀ n : ℕ, ‖coeff n F - (coeff n G).val‖ ≤ ‖π.val‖) :
    ∃ Ξ : (valRingCp p)⟦X⟧, seriesToCp Ξ = F ∧ C π ∣ Ξ - G := by
  obtain ⟨D, hD⟩ : ∃ D : (valRingCp p)⟦X⟧, seriesToCp D = F - seriesToCp G :=
    mem_range_seriesToCp.2 fun n ↦ (h n).trans π.property
  refine ⟨D + G, by rw [map_add, hD, sub_add_cancel], ?_⟩
  rw [add_sub_cancel_right]
  refine C_dvd_iff_dvd_coeff.2 fun n ↦ dvd_iff_norm_le.2 ?_
  rw [← coeff_seriesToCp, hD]
  exact h n

section Numbers
variable {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d]

/-- For a prime `d ≡ 7` mod `8` the Legendre symbol `chiK d p = (p / d)` vanishes at `p = d`. -/
lemma chiK_eq_zero_of_ramified (hd : p = d) : chiK d p = 0 :=
  (chiK_cases d p).elim (·.2) fun h ↦ absurd hd h.1

/-- Let `d ≡ 7` mod `8` be a prime. A prime `p` with Legendre symbol `chiK d p = (p / d) ≠ 1` is
ramified in `ℚ(√-d)`, with norm `q_p = primeNorm d p = p`, or inert, with `(p / d) = -1` and
`q_p = p²`. -/
lemma ramified_or_inert (hp : chiK d p ≠ 1) :
    p = d ∧ primeNorm d p = p ∨ p ≠ d ∧ chiK d p = -1 ∧ primeNorm d p = p ^ 2 := by
  rcases chiK_cases d p with ⟨hd, h_zero⟩ | ⟨hd, h_split | h_inert⟩
  · exact .inl ⟨hd, by simp [primeNorm, h_zero]⟩
  · exact absurd h_split hp
  · exact .inr ⟨hd, h_inert, by rw [primeNorm, ite_eq_left h_inert]⟩

/-- At a non-split prime `p` (one with `chiK d p ≠ 1`), the degree `i₀ = leastFlatDegree d p` is
less than `q_p - 1`, where `q_p = primeNorm d p`. -/
lemma leastFlatDegree_lt (hp : chiK d p ≠ 1) : leastFlatDegree d p < primeNorm d p - 1 := by
  rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hd, -, hq⟩
  · grind [leastFlatDegree, (PrimeSevenModEight.mod_eight : d % 8 = 7)]
  · have h3 : 3 ≤ p := (Fact.out : p.Prime).two_le.lt_of_ne' (ne_two_of_chiK_ne_one hp)
    rw [leastFlatDegree, ite_eq_right hd, hq, Nat.lt_sub_iff_add_lt]
    nlinarith

/-- At a non-split prime `p` (one with `chiK d p ≠ 1`), one has `p + 1 ≡ i₀ = leastFlatDegree d p`
mod `q_p - 1`, where `q_p = primeNorm d p`. -/
lemma add_one_modEq_leastFlatDegree (hp : chiK d p ≠ 1) :
    p + 1 ≡ leastFlatDegree d p [MOD primeNorm d p - 1] := by
  rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hd, -, -⟩
  · have h_eq : p + 1 = p - 1 + 2 := by grind [(Fact.out : p.Prime).pos]
    rw [leastFlatDegree, ite_eq_left hd, hq, h_eq]
    exact Nat.add_modEq_left
  · rw [leastFlatDegree, ite_eq_right hd]

variable [PadicPlace p]

/-- Let `d ≡ 7` mod `8` be a prime and `p` a prime with Legendre symbol `chiK d p = (p / d) ≠ 1`.
The numbers `π_p = piPrime d p`, `q_p = primeNorm d p`, `i₀ = leastFlatDegree d p` are `√-d`, `p`,
`2` if `p = d`, and `p`, `p²`, `p + 1` if `p` is inert; `π_p` is read in `ℂ_p` by the embedding `ιₚ`
that `PadicPlace p` fixes. If `ϖ ≠ 0` and `‖ϖ‖ ^ (q_p - 1) = ‖π_p‖`, then `π_p ϖ ^ i₀ / (q_p c_ϖ)`
has norm one. -/
lemma norm_piPrime_mul_pow_leastFlatDegree_div (hp : chiK d p ≠ 1) {ϖ : ℂ_[p]} (hϖ0 : ϖ ≠ 0)
    (hϖ : ‖ϖ‖ ^ (primeNorm d p - 1) = ‖ιₚ (piPrime d p)‖) :
    ‖ιₚ (piPrime d p) * ϖ ^ leastFlatDegree d p / (primeNorm d p * (ϖ ^ (p + 1) / p))‖ = 1 := by
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hpd_ne, -, hq⟩
  · have h_norm : ‖ιₚ (piPrime d p)‖ = ‖ϖ ^ (p - 1)‖ := by rw [norm_pow, ← hϖ, hq]
    have h_eq : ιₚ (piPrime d p) * ϖ ^ 2 / (p * (ϖ ^ (p + 1) / p)) =
        ιₚ (piPrime d p) / ϖ ^ (p - 1) := by
      rw [pow_succ ϖ p, ← pow_sub_one_mul (Fact.out : p.Prime).ne_zero ϖ]
      field
    rw [leastFlatDegree, ite_eq_left hd, hq, h_eq, norm_div, h_norm,
      div_self (norm_ne_zero_iff.2 (pow_ne_zero _ hϖ0))]
  · have h_eq : (p : ℂ_[p]) * ϖ ^ (p + 1) / (p ^ 2 * (ϖ ^ (p + 1) / p)) = 1 := by field
    rw [leastFlatDegree, piPrime, ite_eq_right hpd_ne, ite_eq_right hpd_ne, hq, map_natCast,
      Nat.cast_pow, h_eq, norm_one]

omit [PrimeSevenModEight d] in
lemma piPrime_sq_of_ramified (hd : p = d) : ιₚ (piPrime d p) ^ 2 = -(p : ℂ_[p]) := by
  rw [piPrime, ite_eq_left hd, map_I_mul_sqrt_sq, ← hd]

/-- Let `d ≡ 7` mod `8` be a prime and `p` a prime that is non-split in `ℚ(√-d)`. Let
`π_p = piPrime d p` be `√-d` if `p = d` and `p` otherwise, mapped to `ℂ_p` by the place `ιₚ`, and
let `q_p = primeNorm d p` be the norm of a prime above `p`. For `n > 2` we have
`‖π_p ^ n / q_p‖ ≤ ‖π_p‖`: the number `π_p ^ n / q_p` is `p ^ (n - 2)` if `p` is inert, and
`-π_p ^ (n - 2)` if `p = d`. -/
lemma norm_piPrime_pow_div_le (hp : chiK d p ≠ 1) {n : ℕ} (hn : 2 < n) :
    ‖ιₚ (piPrime d p) ^ n / primeNorm d p‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = 2 + (k + 1) := ⟨n - 3, by omega⟩
  have h_eq : ‖ιₚ (piPrime d p) ^ (2 + (k + 1)) / primeNorm d p‖ =
      ‖ιₚ (piPrime d p)‖ ^ (k + 1) := by
    rcases ramified_or_inert hp with ⟨hd, hq⟩ | ⟨hpd_ne, -, hq⟩
    · -- Here `π_p ^ 2 = -p`.
      simp [hq, pow_add, piPrime_sq_of_ramified hd, hp0]
    · simp [hq, piPrime, hpd_ne, pow_add, hp0]
  rw [h_eq]
  exact pow_le_of_le_one (norm_nonneg _) (norm_piPrime_lt_one d).le k.succ_ne_zero

end Numbers

namespace CMLattice
variable {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p]

/-! ## Step 1: averaging -/

/-- The series `g^♭`: the part of `g = -log θ` (`C.negLogTheta`) in the degrees `≡ p + 1` mod
`q_p - 1`, where `q_p = primeNorm d p` and `θ` is the theta function of `C`, a lattice with complex
multiplication by the ring of integers of `ℚ(√-d)`. -/
noncomputable def negLogThetaPart : ℂ_[p]⟦X⟧ :=
  congruencePart (primeNorm d p - 1) (p + 1) C.negLogTheta

/-- The exponent `Ξ₁ = -g^♭(ϖ z) / c_ϖ`, where `g^♭ = C.negLogThetaPart` and
`c_ϖ = ϖ ^ (p + 1) / p`. -/
noncomputable def exponentSeries (ϖ : ℂ_[p]) : ℂ_[p]⟦X⟧ :=
  -(ϖ ^ (p + 1) / p)⁻¹ • rescale ϖ C.negLogThetaPart

lemma constantCoeff_negLogThetaPart : constantCoeff C.negLogThetaPart = (0 : ℂ_[p]) := by
  rw [← coeff_zero_eq_constantCoeff_apply, negLogThetaPart, congruencePart, coeff_mk,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_negLogTheta, ite_self]

/-- Let `g = -log θ` and let `g^♭` be its part in the degrees `≡ p + 1` mod `q_p - 1`. The series
`θ exp g^♭ = exp (g^♭ - g)`, with `exp a` written `expSubst a`, lies in the ring `𝒪[[y]]` of series
with coefficients of norm at most one in the Taylor series of `y = C.translatedY`. -/
lemma expSubst_negLogThetaPart_sub_mem :
    expSubst (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) ∈ C.integralSeriesRing := by
  -- Its `(q_p - 1)`-th power is the product of the `exp (ζ ^ (-p - 1) g(ζ z) - g(z))` over the
  -- `(q_p - 1)`-th roots of unity `ζ`, and `q_p - 1` is prime to `p`.
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ_[p] (primeNorm d p - 1)
  let term (i : ℕ) : ℂ_[p]⟦X⟧ :=
    (ζ ^ i)⁻¹ ^ (p + 1) • rescale (ζ ^ i) C.negLogTheta - C.negLogTheta
  have h_zero : constantCoeff (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) = 0 := by
    simp [constantCoeff_negLogThetaPart, constantCoeff_negLogTheta]
  have h_term_zero (i : ℕ) : constantCoeff (term i) = 0 := by
    simp [term, constantCoeff_negLogTheta]
  have h_sum : ∑ _i ∈ range (primeNorm d p - 1), (C.negLogThetaPart - C.negLogTheta) =
      ∑ i ∈ range (primeNorm d p - 1), term i := by
    rw [sum_sub_distrib, sum_sub_distrib, negLogThetaPart, congruencePart_eq_sum hζ, sum_const,
      card_range, ← Nat.cast_smul_eq_nsmul ℂ_[p], smul_inv_smul₀ (NeZero.ne _)]
  have h_prod : expSubst (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) ^ (primeNorm d p - 1) =
      ∏ i ∈ range (primeNorm d p - 1), expSubst (term i) := by
    rw [← expSubst_sum h_term_zero, ← h_sum, expSubst_sum fun _ ↦ h_zero, prod_const, card_range]
  refine C.isSeriesGenerator_translatedY.expSubst_mem_of_pow_mem
    (coprime_primeNorm_sub_one d p) h_zero ?_
  rw [h_prod]
  exact prod_mem fun i _ ↦ C.expSubst_rescale_sub_mem_of_pow_eq_one
    (by rw [pow_right_comm, hζ.pow_eq_one, one_pow])

/-- For `ϖ ≠ 0` the exponent `Ξ₁ = C.exponentSeries ϖ` satisfies `c_ϖ Ξ₁ = -g^♭(ϖ z)`, where
`c_ϖ = ϖ ^ (p + 1) / p` and `g^♭ = C.negLogThetaPart`. -/
lemma smul_exponentSeries {ϖ : ℂ_[p]} (hϖ0 : ϖ ≠ 0) :
    (ϖ ^ (p + 1) / p) • C.exponentSeries ϖ = -rescale ϖ C.negLogThetaPart := by
  simp [exponentSeries, smul_smul, hϖ0, (Fact.out : p.Prime).ne_zero]

/-- Let `θ` be the Taylor series of `C.θ`, the twisted translate of the sigma function of `C` by the
point `C.t` of order two, normalised to `θ(0) = 1` and read in `ℂ_p` by the embedding `ιₚ`. Let
`ϖ ≠ 0` have valuation at least `ρ_p = v(π_p) / (q_p - 1)`. Then `θ(ϖ z) = W exp (c_ϖ Ξ₁)` for a
series `W` over the integers of `ℂ_p`. -/
lemma exists_rescale_theta_eq_mul_expSubst {ϖ : ℂ_[p]} (hϖ0 : ϖ ≠ 0)
    (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p)) :
    ∃ W : (valRingCp p)⟦X⟧, rescale ϖ (taylorVia ιₚ C.θ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • C.exponentSeries ϖ) := by
  obtain ⟨W, hW⟩ := C.rescale_mem_range_seriesToCp hϖ C.expSubst_negLogThetaPart_sub_mem
  have h_flat_zero : constantCoeff (-C.negLogThetaPart : ℂ_[p]⟦X⟧) = 0 := by
    simp [constantCoeff_negLogThetaPart]
  have h_theta : taylorVia ιₚ C.θ = expSubst (C.negLogThetaPart - C.negLogTheta : ℂ_[p]⟦X⟧) *
      expSubst (-C.negLogThetaPart : ℂ_[p]⟦X⟧) := by
    rw [← expSubst_add _ (by simp [constantCoeff_negLogThetaPart, constantCoeff_negLogTheta])
      h_flat_zero, taylorVia_theta_eq_expSubst, ← sub_eq_add_neg, sub_sub_cancel_left]
  refine ⟨W, ?_⟩
  rw [h_theta, map_mul, hW, smul_exponentSeries C hϖ0, rescale_subst h_flat_zero, map_neg]

/-! ## Step 2: the functional equation -/

/-- Let `T = C.formalParam` be the formal parameter, the part in the degrees `≡ 1` mod `q_p - 1` of
the Taylor series of `C.translatedY`, so that `C.integralSeriesRing = 𝒪[[T]]`. Let `i < q_p - 1`.
For `H ∈ 𝒪[[T]]` the part of `H` in the degrees `≡ i` mod `q_p - 1` has the form
`l T ^ i + T ^ (i + q_p - 1) H'` with `l ∈ 𝒪` and `H' ∈ 𝒪[[T]]`. -/
lemma exists_congruencePart_eq_smul_formalParam_pow_add {i : ℕ} (hi : i < primeNorm d p - 1)
    {H : ℂ_[p]⟦X⟧} (hH : H ∈ C.integralSeriesRing) :
    ∃ l : valRingCp p, ∃ H' ∈ C.integralSeriesRing,
      congruencePart (primeNorm d p - 1) i H =
        (l : ℂ_[p]) • C.formalParam ^ i + C.formalParam ^ (i + (primeNorm d p - 1)) * H' := by
  have h_subst : HasSubst (C.formalParam : ℂ_[p]⟦X⟧) :=
    .of_constantCoeff_zero' C.constantCoeff_formalParam
  obtain ⟨G, rfl⟩ := C.mem_integralSeriesRing_iff_exists_subst_formalParam.1 hH
  -- Split the series `G` in `X` and then substitute `X = T`.
  obtain ⟨l, G', hG⟩ := exists_congruencePart_eq_smul_X_pow_add hi G
  refine ⟨l, subst C.formalParam (seriesToCp G'),
    C.mem_integralSeriesRing_iff_exists_subst_formalParam.2 ⟨G', rfl⟩, ?_⟩
  rw [congruencePart_subst_formalParam, hG, subst_add h_subst, subst_smul h_subst,
    subst_mul h_subst, subst_pow h_subst, subst_pow h_subst, subst_X h_subst]

/-- The Frobenius congruence for `g^♭ = C.negLogThetaPart`, the part of `g = -log θ` in the degrees
`≡ p + 1` mod `q_p - 1`. Let `d ≡ 7` mod `8` be a prime and `p` a prime that does not split in
`ℚ(√-d)`. The numbers `π_p = piPrime d p`, `q_p = primeNorm d p`, `i₀ = leastFlatDegree d p` are
`√-d`, `p`, `2` if `p = d`, and `p`, `p²`, `p + 1` if `p` is inert. The formal parameter
`T = C.formalParam` is the part in the degrees `≡ 1` mod `q_p - 1` of the Taylor series of the
coordinate function `y = C.translatedY`. Then `q_p g^♭(z) - g^♭(ιₚ π_p z) = ιₚ π_p (l T ^ i₀ + T ^
(i₀ + q_p - 1) H)` for some `l ∈ 𝒪` and `H ∈ 𝒪[[T]]`. -/
lemma exists_smul_negLogThetaPart_sub_rescale_eq (hp : chiK d p ≠ 1) :
    ∃ l : valRingCp p, ∃ H ∈ C.integralSeriesRing,
      (primeNorm d p : ℂ_[p]) • C.negLogThetaPart - rescale (ιₚ (piPrime d p)) C.negLogThetaPart =
        ιₚ (piPrime d p) • ((l : ℂ_[p]) • C.formalParam ^ leastFlatDegree d p +
          C.formalParam ^ (leastFlatDegree d p + (primeNorm d p - 1)) * H) := by
  obtain ⟨G, hG, h_frob⟩ : ∃ G ∈ C.integralSeriesRing,
      (primeNorm d p : ℂ_[p]) • C.negLogTheta - rescale (ιₚ (piPrime d p)) C.negLogTheta =
        ιₚ (piPrime d p) • G :=
    C.exists_negLogTheta_frobenius_congruence hp
  obtain ⟨l, H, hH, h_part⟩ :=
    C.exists_congruencePart_eq_smul_formalParam_pow_add (leastFlatDegree_lt hp) hG
  refine ⟨l, H, hH, ?_⟩
  have h_mod (n : ℕ) :
      n ≡ p + 1 [MOD primeNorm d p - 1] ↔ n ≡ leastFlatDegree d p [MOD primeNorm d p - 1] :=
    ⟨(·.trans (add_one_modEq_leastFlatDegree hp)),
      (·.trans (add_one_modEq_leastFlatDegree hp).symm)⟩
  rw [← h_part]
  ext n
  have h_coeff : primeNorm d p * coeff n C.negLogTheta -
      ιₚ (piPrime d p) ^ n * coeff n C.negLogTheta = ιₚ (piPrime d p) * coeff n G := by
    simpa only [map_sub, coeff_smul, coeff_rescale, smul_eq_mul] using congrArg (coeff n) h_frob
  simp only [negLogThetaPart, congruencePart, map_sub, coeff_smul, coeff_rescale, coeff_mk,
    smul_eq_mul, mul_ite, mul_zero, h_mod]
  split_ifs
  · exact h_coeff
  · exact sub_zero _

/-- The Frobenius congruence for `f(z) = g^♭(ϖ z)`. Let `p` be a prime that does not split in
`ℚ(√-d)`. The numbers `π_p = piPrime d p`, `q_p = primeNorm d p`, `i₀ = leastFlatDegree d p`,
`ρ_p = varpiValuation d p` are `√-d`, `p`, `2`, `1 / (2 p - 2)` if `p = d`, and `p`, `p²`, `p + 1`,
`1 / (p² - 1)` if `p` is inert. If `‖ϖ‖ ≤ p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with `Y ∈ 𝒪[[z]]`, then
`q_p f(z) - f(π_p z) = π_p ϖ ^ i₀ (λ' Y ^ i₀ + ϖ ^ (q_p - 1) R)` for some `λ' ∈ 𝒪` and
`R ∈ 𝒪[[z]]`. -/
lemma exists_smul_rescale_negLogThetaPart_sub_rescale_eq {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hp : chiK d p ≠ 1) (hϖ : ‖ϖ‖ ≤ p ^ (-varpiValuation d p))
    (hY : rescale ϖ C.formalParam = ϖ • seriesToCp Y) :
    ∃ (l : valRingCp p) (R : (valRingCp p)⟦X⟧),
      (primeNorm d p : ℂ_[p]) • rescale ϖ C.negLogThetaPart -
          rescale (ιₚ (piPrime d p)) (rescale ϖ C.negLogThetaPart) =
        (ιₚ (piPrime d p) * ϖ ^ leastFlatDegree d p) •
          ((l : ℂ_[p]) • seriesToCp (Y ^ leastFlatDegree d p) +
            ϖ ^ (primeNorm d p - 1) • seriesToCp R) := by
  set π : ℂ_[p] := ιₚ (piPrime d p)
  set q : ℕ := primeNorm d p
  set i : ℕ := leastFlatDegree d p
  obtain ⟨l, H, hH, h_frob⟩ : ∃ l : valRingCp p, ∃ H ∈ C.integralSeriesRing,
      (q : ℂ_[p]) • C.negLogThetaPart - rescale π C.negLogThetaPart =
        π • ((l : ℂ_[p]) • C.formalParam ^ i + C.formalParam ^ (i + (q - 1)) * H) :=
    C.exists_smul_negLogThetaPart_sub_rescale_eq hp
  obtain ⟨V, hV⟩ : ∃ V : (valRingCp p)⟦X⟧, seriesToCp V = rescale ϖ H :=
    C.rescale_mem_range_seriesToCp hϖ hH
  refine ⟨l, Y ^ (i + (q - 1)) * V, ?_⟩
  calc
    _ = rescale ϖ ((q : ℂ_[p]) • C.negLogThetaPart - rescale π C.negLogThetaPart) := by
      rw [map_sub, rescale_smul, rescale_rescale, rescale_rescale, mul_comm]
    _ = π • ((l : ℂ_[p]) • (ϖ • seriesToCp Y) ^ i +
          (ϖ • seriesToCp Y) ^ (i + (q - 1)) * seriesToCp V) := by
      simp only [h_frob, map_mul, map_add, map_pow, rescale_smul, hY, hV]
    _ = _ := by
      simp only [map_mul, map_pow, smul_pow, smul_mul_assoc]
      module

/-- The functional equation, modulo `π_p`, for the exponent `Ξ₁`. Let `p` be a prime that does not
split in `ℚ(√-d)`. The numbers `π_p = piPrime d p`, `q_p = primeNorm d p`,
`i₀ = leastFlatDegree d p`, `ρ_p = varpiValuation d p` are `√-d`, `p`, `2`, `1 / (2 p - 2)` if
`p = d`, and `p`, `p²`, `p + 1`, `1 / (p² - 1)` if `p` is inert. If `‖ϖ‖ = p ^ (-ρ_p)` and
`T(ϖ z) = ϖ Y` with `Y ∈ 𝒪[[z]]`, then there is `λ ∈ 𝒪` with
`(1 - π_p ^ n / q_p) [z ^ n] Ξ₁ ≡ λ [z ^ n] Y ^ i₀` modulo `π_p 𝒪` for all `n`. -/
lemma exists_functional_equation_exponentSeries {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hp : chiK d p ≠ 1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hY : rescale ϖ C.formalParam = ϖ • seriesToCp Y) :
    ∃ l : valRingCp p, ∀ n : ℕ,
      ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) -
        (l * coeff n (Y ^ leastFlatDegree d p)).val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  -- Divide the Frobenius congruence for `g^♭(ϖ z)` by `-q c_ϖ`. On the right a unit `u` appears,
  -- and the second term has the factor `ϖ ^ (q - 1)`, of norm `‖π‖`.
  set π : ℂ_[p] := ιₚ (piPrime d p)
  set q : ℕ := primeNorm d p
  set i : ℕ := leastFlatDegree d p
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hq0 : (q : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_primeNorm d p).ne_bot
  have hϖ0 : ϖ ≠ 0 := ne_zero_of_norm_eq_rpow hϖ
  have hϖπ : ‖ϖ‖ ^ (q - 1) = ‖π‖ := by rw [hϖ, norm_piPrime_eq_rpow_pow]
  obtain ⟨l, R, h_scaled⟩ : ∃ (l : valRingCp p) (R : (valRingCp p)⟦X⟧),
      (q : ℂ_[p]) • rescale ϖ C.negLogThetaPart - rescale π (rescale ϖ C.negLogThetaPart) =
        (π * ϖ ^ i) • ((l : ℂ_[p]) • seriesToCp (Y ^ i) + ϖ ^ (q - 1) • seriesToCp R) :=
    C.exists_smul_rescale_negLogThetaPart_sub_rescale_eq hp hϖ.le hY
  let u : ℂ_[p] := -(π * ϖ ^ i / (q * (ϖ ^ (p + 1) / p)))
  have hu : ‖u‖ = 1 := (norm_neg _).trans (norm_piPrime_mul_pow_leastFlatDegree_div hp hϖ0 hϖπ)
  refine ⟨⟨u, hu.le⟩ * l, fun n ↦ ?_⟩
  have h_scaled_coeff : q * coeff n (rescale ϖ C.negLogThetaPart) -
      π ^ n * coeff n (rescale ϖ C.negLogThetaPart) =
        π * ϖ ^ i * (l * (coeff n (Y ^ i)).val + ϖ ^ (q - 1) * (coeff n R).val) := by
    simpa only [map_sub, map_add, coeff_smul, coeff_rescale _ π, smul_eq_mul, coeff_seriesToCp]
      using congrArg (coeff n) h_scaled
  have h_coeff : (1 - π ^ n / q) * coeff n (C.exponentSeries ϖ) - u * l * (coeff n (Y ^ i)).val =
      u * ϖ ^ (q - 1) * (coeff n R).val := by
    simp only [exponentSeries, coeff_smul, smul_eq_mul, u]
    rw [← mul_right_inj' hq0]
    linear_combination (norm := field) -(ϖ ^ (p + 1) / p)⁻¹ * h_scaled_coeff
  calc ‖(1 - π ^ n / q) * coeff n (C.exponentSeries ϖ) - u * l * (coeff n (Y ^ i)).val‖
    _ = ‖π‖ * ‖(coeff n R).val‖ := by
      rw [h_coeff, norm_mul, norm_mul, hu, one_mul, norm_pow, hϖπ]
    _ ≤ ‖π‖ := mul_le_of_le_one_right (norm_nonneg π) (coeff n R).property

/-! ## Step 3: solving the functional equation -/

/-- Let `p` be non-split in `ℚ(√-d)`, that is, `chiK d p ≠ 1`, and `q_p = primeNorm d p`. For any
`ϖ`, the exponent `Ξ₁ = C.exponentSeries ϖ` has no terms below the degree
`i₀ = leastFlatDegree d p`, the least positive degree congruent to `p + 1` mod `q_p - 1`. -/
lemma coeff_exponentSeries_eq_zero_of_lt {ϖ : ℂ_[p]} (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < leastFlatDegree d p) :
    coeff n (C.exponentSeries ϖ) = 0 := by
  have h_degree_lt : leastFlatDegree d p < primeNorm d p - 1 := leastFlatDegree_lt hp
  have h_not : ¬n ≡ p + 1 [MOD primeNorm d p - 1] := fun h ↦ by
    have h_modEq : n ≡ leastFlatDegree d p [MOD primeNorm d p - 1] :=
      h.trans (add_one_modEq_leastFlatDegree hp)
    exact hn.ne (h_modEq.eq_of_lt_of_lt (hn.trans h_degree_lt) h_degree_lt)
  simp [exponentSeries, negLogThetaPart, congruencePart, h_not]

/-- Let `p` be non-split (`chiK d p ≠ 1`), `π_p = piPrime d p`, `q_p = primeNorm d p`, and let
`a ∈ valRingCp p` satisfy `(1 - π_p ^ n / q_p) [z ^ n] Ξ₁ ≡ a` modulo `π_p` (through `ιₚ`) for the
exponent `Ξ₁ = C.exponentSeries ϖ`. Then `[z ^ n] Ξ₁ ≡ a` if `n > 2`, where the factor is `≡ 1`, and
if `n < leastFlatDegree d p`, where `Ξ₁` has no term of degree `n`. -/
lemma norm_coeff_exponentSeries_sub_le {ϖ : ℂ_[p]} (hp : chiK d p ≠ 1) {n : ℕ}
    (hn : n < leastFlatDegree d p ∨ 2 < n) {a : valRingCp p}
    (h_eq : ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) - a.val‖ ≤
      ‖ιₚ (piPrime d p)‖) :
    ‖coeff n (C.exponentSeries ϖ) - a.val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
  rcases hn with hn | hn
  · simpa only [C.coeff_exponentSeries_eq_zero_of_lt hp hn, mul_zero] using h_eq
  · exact norm_sub_le_of_norm_one_sub_mul_sub_le (norm_piPrime_lt_one d)
      (norm_piPrime_pow_div_le hp hn) a.property h_eq

/-- Let `p` be inert in `ℚ(√-d)`, that is, `chiK d p = (p / d) = -1`, so that `π_p = piPrimeInt d`
is `p`, `q_p = primeNorm d p` is `p²` and `ρ_p = varpiValuation d p` is `1 / (p² - 1)`. If
`‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with `Y ∈ 𝒪[[z]]`, then `Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]`
by the inclusion `seriesToCp`, and `Ξ ≡ λ Y ^ (p + 1)` modulo `π_p` for some `λ ∈ 𝒪`. -/
lemma exists_seriesToCp_eq_exponentSeries_of_inert {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (h_inert : chiK d p = -1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hY : rescale ϖ C.formalParam = ϖ • seriesToCp Y) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - l • Y ^ (p + 1) := by
  have hp : chiK d p ≠ 1 := by simp [h_inert]
  have hpd_ne : p ≠ d := fun hd ↦ by simp [chiK_eq_zero_of_ramified hd] at h_inert
  have hp_two_le : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h_degree : leastFlatDegree d p = p + 1 := ite_eq_right hpd_ne
  obtain ⟨l, hl⟩ : ∃ l : valRingCp p, ∀ n : ℕ,
      ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) -
        (l * coeff n (Y ^ leastFlatDegree d p)).val‖ ≤ ‖ιₚ (piPrime d p)‖ :=
    C.exists_functional_equation_exponentSeries hp hϖ hY
  have h_coeff (n : ℕ) : ‖coeff n (C.exponentSeries ϖ) - (coeff n (l • Y ^ (p + 1))).val‖ ≤
      ‖ιₚ (piPrime d p)‖ :=
    C.norm_coeff_exponentSeries_sub_le hp (by omega)
      (by simpa only [h_degree, coeff_smul, smul_eq_mul] using hl n)
  obtain ⟨Ξ, hΞ, h_dvd⟩ := exists_seriesToCp_eq_and_C_dvd_sub (π := piPrimeInt d) h_coeff
  exact ⟨Ξ, l, hΞ, h_dvd⟩

/-- Let `p = d`, so that `π_p = piPrimeInt d` is `√-d`, `q_p = primeNorm d p` is `p` and
`ρ_p = varpiValuation d p` is `1 / (2 p - 2)`. Let `‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with
`Y ∈ 𝒪[[z]]` and `[z ^ 2] Y ^ 2 ≡ 1` modulo `π_p`, and let `half` be the inverse of `2` in `𝒪`. Then
`Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]` by the inclusion `seriesToCp`, and `Ξ ≡ λ (Y ^ 2 - z ^ 2 / 2)`
modulo `π_p` for some `λ ∈ 𝒪`. -/
lemma exists_seriesToCp_eq_exponentSeries_of_ramified {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hd : p = d) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hY : rescale ϖ C.formalParam = ϖ • seriesToCp Y)
    (hY_two : piPrimeInt d ∣ 1 - coeff 2 (Y ^ 2)) {half : valRingCp p} (h_half : 2 * half = 1) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - l • (Y ^ 2 - half • X ^ 2) := by
  have h_chi : chiK d p = 0 := chiK_eq_zero_of_ramified hd
  have hp : chiK d p ≠ 1 := by simp [h_chi]
  have hq : primeNorm d p = p := by simp [primeNorm, h_chi]
  have h_degree : leastFlatDegree d p = 2 := ite_eq_left hd
  obtain ⟨l, hl⟩ : ∃ l : valRingCp p, ∀ n : ℕ,
      ‖(1 - ιₚ (piPrime d p) ^ n / primeNorm d p) * coeff n (C.exponentSeries ϖ) -
        (l * coeff n (Y ^ 2)).val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
    simpa only [h_degree] using C.exists_functional_equation_exponentSeries hp hϖ hY
  suffices h_coeff : ∀ n : ℕ, ‖coeff n (C.exponentSeries ϖ) -
      (coeff n (l • (Y ^ 2 - half • X ^ 2))).val‖ ≤ ‖ιₚ (piPrime d p)‖ by
    obtain ⟨Ξ, hΞ, h_dvd⟩ := exists_seriesToCp_eq_and_C_dvd_sub (π := piPrimeInt d) h_coeff
    exact ⟨Ξ, l, hΞ, h_dvd⟩
  intro n
  rw [coeff_smul, map_sub, coeff_smul, coeff_X_pow, smul_eq_mul, smul_eq_mul]
  obtain rfl | hn := eq_or_ne n 2
  · -- In degree `2` the factor is `2`: from `2 x ≡ λ c` and `c ≡ 1` follows `x ≡ λ (c - 1 / 2)`.
    rw [ite_eq_left rfl, mul_one]
    set x : ℂ_[p] := coeff 2 (C.exponentSeries ϖ)
    set c : valRingCp p := coeff 2 (Y ^ 2)
    have h_factor : 1 - ιₚ (piPrime d p) ^ 2 / primeNorm d p = 2 := by
      rw [hq, piPrime_sq_of_ramified hd, neg_div, div_self (NeZero.ne _), sub_neg_eq_add,
        one_add_one_eq_two]
    have h_double : ‖2 * x - (l * c).val‖ ≤ ‖ιₚ (piPrime d p)‖ := by
      simpa only [h_factor] using hl 2
    have h_one : ‖(l * (1 - c)).val‖ ≤ ‖ιₚ (piPrime d p)‖ := dvd_iff_norm_le.1 (hY_two.mul_left l)
    have h_eq : x - (l * (c - half)).val =
        half.val * ((2 * x - (l * c).val) + (l * (1 - c)).val) := by
      have h_coe : 2 * half.val = 1 := congrArg Subtype.val h_half
      push_cast
      linear_combination -(x - l * c) * h_coe
    rw [h_eq, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) half.property).trans
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h_double h_one))
  · rw [ite_eq_right hn, mul_zero, sub_zero]
    exact C.norm_coeff_exponentSeries_sub_le hp (by omega) (hl n)

end CMLattice

section Reduction
variable {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d] [PadicPlace p]

/-- The reduction map `𝒪 → 𝒪 / π_p`, where `𝒪 = valRingCp p` and `π_p = piPrimeInt d`. -/
noncomputable abbrev reducePiPrime (d : ℕ) [PrimeSevenModEight d] :
    valRingCp p →+* valRingCp p ⧸ Ideal.span {piPrimeInt d} :=
  Ideal.Quotient.mk (Ideal.span {piPrimeInt d})

lemma reducePiPrime_eq_iff {a b : valRingCp p} :
    reducePiPrime d a = reducePiPrime d b ↔ piPrimeInt d ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

/-- The ring `𝒪 / π_p` is nontrivial, because `π_p` has norm less than one. -/
instance : Nontrivial (valRingCp p ⧸ Ideal.span {(piPrimeInt d : valRingCp p)}) := by
  rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top,
    isUnit_integer_iff_norm_eq_one]
  exact (norm_piPrime_lt_one d).ne

/-- The ring `𝒪 / π_p` has characteristic `p`, because `π_p` divides `p`. -/
instance : CharP (valRingCp p ⧸ Ideal.span {(piPrimeInt d : valRingCp p)}) p := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (reducePiPrime d),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact piPrimeInt_dvd_natCast d

lemma map_reducePiPrime_eq_iff {F G : (valRingCp p)⟦X⟧} :
    F.map (reducePiPrime d) = G.map (reducePiPrime d) ↔ C (piPrimeInt d) ∣ F - G := by
  simp only [PowerSeries.ext_iff, coeff_map, reducePiPrime_eq_iff, C_dvd_iff_dvd_coeff, map_sub]

open scoped Classical in
/-- Let `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, where `q_p = primeNorm d p` and `π_p = piPrimeInt d`.
If the powers of `q_p` are the `p ^ i` with `i ∈ I`, then `Y` reduces to `∑_{i ∈ I} z ^ p ^ i`. -/
lemma map_reducePiPrime_eq_primePowerSeries {Y : (valRingCp p)⟦X⟧}
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    {I : Set ℕ} (hI : ∀ n : ℕ, (∃ j : ℕ, n = primeNorm d p ^ j) ↔ ∃ i ∈ I, n = p ^ i) :
    Y.map (reducePiPrime d) = primePowerSeries (valRingCp p ⧸ Ideal.span {piPrimeInt d}) p I := by
  ext n
  rw [coeff_map, reducePiPrime_eq_iff.2 (hY n), primePowerSeries, coeff_mk,
    apply_ite (reducePiPrime d), map_one, map_zero]
  exact if_congr (hI n) rfl rfl

open scoped Classical in
/-- Let `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, where `q_p = primeNorm d p` and `π_p = piPrimeInt d`.
If `q_p = p ^ 2`, as for inert `p`, then `Y ^ p Y` is congruent to the product of
`∑_{i odd} z ^ p ^ i` and `∑_{i even} z ^ p ^ i`. -/
lemma C_dvd_pow_sub_primePowerSeries_odd_mul_even {Y : (valRingCp p)⟦X⟧}
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    (hq : primeNorm d p = p ^ 2) :
    C (piPrimeInt d) ∣ Y ^ (p + 1) - primePowerSeries (valRingCp p) p {i : ℕ | Odd i} *
      primePowerSeries (valRingCp p) p {i : ℕ | Even i} := by
  have h_powers (n : ℕ) :
      (∃ j : ℕ, n = primeNorm d p ^ j) ↔ ∃ i ∈ {i : ℕ | Even i}, n = p ^ i := by
    simp [hq, ← pow_mul, even_iff_exists_two_mul]
  rw [← map_reducePiPrime_eq_iff, map_pow, map_reducePiPrime_eq_primePowerSeries hY h_powers,
    pow_succ, primePowerSeries_even_pow, map_mul, map_primePowerSeries, map_primePowerSeries]

open scoped Classical in
/-- Let `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, where `q_p = primeNorm d p` and `π_p = piPrimeInt d`.
If `q_p = p`, as for `p = d`, then `Y ^ 2` is congruent to the square of `∑_i z ^ p ^ i`. -/
lemma C_dvd_sq_sub_primePowerSeries_univ_sq {Y : (valRingCp p)⟦X⟧}
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    (hq : primeNorm d p = p) :
    C (piPrimeInt d) ∣ Y ^ 2 - primePowerSeries (valRingCp p) p Set.univ ^ 2 := by
  rw [← map_reducePiPrime_eq_iff, map_pow, map_pow, map_primePowerSeries,
    map_reducePiPrime_eq_primePowerSeries (I := Set.univ) hY fun n ↦ by simp [hq]]

/-!
## Step 4: the unit

The coefficient of `z ^ (p + 1)` in `Ξ₁` is a unit multiple of that of `z ^ (p - 1)` in `x`, which
is a unit by `New.CMLattice.norm_coeff_taylorVia_translatedX_eq_one`.
-/

/-- Let `d ≡ 7` mod `8` be a prime, `C` a lattice stable under the ring of integers of `ℚ(√-d)`, and
`p` a prime that is inert there. For `ϖ ≠ 0` the coefficient of `z ^ (p + 1)` in
`Ξ₁ = C.exponentSeries ϖ = -(p / ϖ ^ (p + 1)) g^♭(ϖ z)` has norm one. -/
lemma CMLattice.norm_coeff_exponentSeries_eq_one {p : ℕ} [Fact p.Prime] {d : ℕ}
    [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p] {ϖ : ℂ_[p]}
    (h_inert : chiK d p = -1) (hϖ0 : ϖ ≠ 0) :
    ‖coeff (p + 1) (C.exponentSeries ϖ)‖ = 1 := by
  have h_exponent : coeff (p + 1) (C.exponentSeries ϖ) = -(p * coeff (p + 1) C.negLogTheta) := by
    rw [exponentSeries, coeff_smul, coeff_rescale, negLogThetaPart, congruencePart, coeff_mk,
      ite_eq_left (Nat.ModEq.refl _), smul_eq_mul]
    field
  -- Up to its constant term, `x` is the second derivative of `g`.
  have h_deriv : coeff (p - 1) (taylorVia ιₚ C.translatedX) =
      p * coeff (p + 1) C.negLogTheta * (p + 1 : ℕ) := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := Nat.exists_eq_add_of_le' (Fact.out : p.Prime).two_le
    have h_coeff := congrArg (coeff (k + 1)) C.derivative_derivative_negLogTheta
    rw [map_add, coeff_succ_C, zero_add, coeff_derivative, coeff_derivative] at h_coeff
    simp only [Nat.add_one_sub_one, ← h_coeff]
    push_cast
    ring
  have h_unit : ‖((p + 1 : ℕ) : ℂ_[p])‖ = 1 :=
    (Nat.coprime_self_add_right.2 (Nat.coprime_one_right p)).norm_natCast_eq_one ℂ_[p]
  calc ‖coeff (p + 1) (C.exponentSeries ϖ)‖
    _ = ‖p * coeff (p + 1) C.negLogTheta * ((p + 1 : ℕ) : ℂ_[p])‖ := by
      rw [h_exponent, norm_neg, norm_mul _ ((p + 1 : ℕ) : ℂ_[p]), h_unit, mul_one]
    _ = 1 := by rw [← h_deriv, C.norm_coeff_taylorVia_translatedX_eq_one h_inert]

lemma isUnit_of_piPrimeInt_dvd_sub {a b : valRingCp p} (ha : IsUnit a)
    (h_dvd : piPrimeInt d ∣ a - b) : IsUnit b := by
  have h_local : IsLocalHom (reducePiPrime (p := p) d) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  rw [← isUnit_map_iff (reducePiPrime d), ← reducePiPrime_eq_iff.2 h_dvd]
  exact ha.map _

end Reduction

open WithPiTopology

variable {p : ℕ} [Fact p.Prime]

/-- For any set `S` of exponents and any coefficients `λ_{e j}` in the valuation ring of `ℂ_p`, the
family `λ_{e j} (X ^ p ^ e X) ^ p ^ j` over `e ∈ S` and `j ∈ ℕ` is summable in the topology of
coefficientwise convergence. -/
lemma summable_smul_X_pow_mul_X_pow (S : Set ℕ) (l : ℕ → ℕ → valRingCp p) :
    Summable fun x : S × ℕ ↦
      l x.1 x.2 • (X ^ p ^ (x.1 : ℕ) * X : (valRingCp p)⟦X⟧) ^ p ^ x.2 := by
  have h_order (e : ℕ) :
      ((p ^ e + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (X ^ p ^ e * X : (valRingCp p)⟦X⟧) := by
    rw [← pow_succ]
    exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ constantCoeff_X
  exact summable_smul_pow_pow (Fact.out : p.Prime).one_lt h_order S l

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p]

open scoped Classical in
/-- The exponent modulo `π_p` at an inert prime. Let `p` be inert in `ℚ(√-d)`, that is,
`chiK d p = (p / d) = -1`, so that `π_p = piPrimeInt d` is `p`, `q_p = primeNorm d p` is `p²` and
`ρ_p = varpiValuation d p` is `1 / (p² - 1)`. Let `‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with
`Y ∈ 𝒪[[z]]` and `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`. Then `Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]` by
the inclusion `seriesToCp`, and `Ξ ≡ ∑_{e odd} ∑_j λ (z ^ p ^ e z) ^ p ^ j` modulo `π_p` for a unit
`λ` of `𝒪`. -/
lemma CMLattice.exists_eq_exponentSeries_dvd_sub_tsum_of_inert {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (h_inert : chiK d p = -1) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hTY : rescale ϖ C.formalParam = ϖ • seriesToCp Y)
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣
        Ξ - ∑' x : {e : ℕ | Odd e} × ℕ, l • (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 ∧
      IsUnit l := by
  have hp_ne_two : p ≠ 2 := ne_two_of_chiK_ne_one (d := d) (by simp [h_inert])
  obtain ⟨Ξ, l, hΞ, hΞ_congr⟩ : ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - l • Y ^ (p + 1) :=
    C.exists_seriesToCp_eq_exponentSeries_of_inert h_inert hϖ hTY
  set P : (valRingCp p)⟦X⟧ := primePowerSeries (valRingCp p) p {i : ℕ | Odd i} *
    primePowerSeries (valRingCp p) p {i : ℕ | Even i}
  have hY_pow_congr : PowerSeries.C (piPrimeInt d) ∣ Y ^ (p + 1) - P :=
    C_dvd_pow_sub_primePowerSeries_odd_mul_even hY (by rw [primeNorm, ite_eq_left h_inert])
  have h_dvd : PowerSeries.C (piPrimeInt d) ∣ Ξ - l • P :=
    dvd_sub_smul_of_dvd_sub hΞ_congr hY_pow_congr
  refine ⟨Ξ, l, hΞ, ?_, ?_⟩
  · rwa [(hasSum_primePowerSeries_odd_mul_even hp_ne_two l).tsum_eq]
  · -- The number `λ` is congruent to the coefficient of `z ^ (p + 1)` in `Ξ`.
    have h_coeff : coeff (p + 1) P = 1 := by
      simpa using coeff_primePowerSeries_odd_mul_even (R := valRingCp p) hp_ne_two odd_one 0
    have h_unit : IsUnit (coeff (p + 1) Ξ) := by
      rw [isUnit_integer_iff_norm_eq_one, ← coeff_seriesToCp, hΞ]
      exact C.norm_coeff_exponentSeries_eq_one h_inert (ne_zero_of_norm_eq_rpow hϖ)
    refine isUnit_of_piPrimeInt_dvd_sub (d := d) h_unit ?_
    simpa only [map_sub, coeff_smul, h_coeff, smul_eq_mul, mul_one]
      using C_dvd_iff_dvd_coeff.1 h_dvd (p + 1)

open scoped Classical in
/-- The exponent modulo `π_p` at the ramified prime. Let `p = d`, so that `π_p = piPrimeInt d` is
`√-d`, `q_p = primeNorm d p` is `p` and `ρ_p = varpiValuation d p` is `1 / (2 p - 2)`. Let
`‖ϖ‖ = p ^ (-ρ_p)` and `T(ϖ z) = ϖ Y` with `Y ∈ 𝒪[[z]]` and `Y ≡ ∑_j z ^ q_p ^ j` modulo `π_p`, and
let `half` be the inverse of `2` in `𝒪`. Then `Ξ₁` comes from a series `Ξ ∈ 𝒪[[z]]` by the inclusion
`seriesToCp`, and there is `λ ∈ 𝒪` with `Ξ ≡ ∑_e ∑_j λ_{e j} (z ^ p ^ e z) ^ p ^ j` modulo `π_p`,
where `λ_{0 0} = λ / 2`, `λ_{0 j} = λ` for `j ≥ 1`, and `λ_{e j} = 2 λ` for `e ≥ 1`. -/
lemma CMLattice.exists_exponentSeries_tsum_of_ramified {ϖ : ℂ_[p]} {Y : (valRingCp p)⟦X⟧}
    (hd : p = d) (hϖ : ‖ϖ‖ = p ^ (-varpiValuation d p))
    (hTY : rescale ϖ C.formalParam = ϖ • seriesToCp Y)
    (hY : ∀ n : ℕ, piPrimeInt d ∣ coeff n Y - if ∃ j : ℕ, n = primeNorm d p ^ j then 1 else 0)
    {half : valRingCp p} (h_half : 2 * half = 1) :
    ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - ∑' x : ↥(Set.univ : Set ℕ) × ℕ,
        (if (x.1 : ℕ) = 0 then if x.2 = 0 then l * half else l else 2 * l) •
          (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 := by
  have h_chi : chiK d p = 0 := chiK_eq_zero_of_ramified hd
  have hp : chiK d p ≠ 1 := by simp [h_chi]
  have hq : primeNorm d p = p := by simp [primeNorm, h_chi]
  have hp_ne_two : p ≠ 2 := ne_two_of_chiK_ne_one hp
  set P : (valRingCp p)⟦X⟧ := primePowerSeries (valRingCp p) p Set.univ
  have hY_sq_congr : PowerSeries.C (piPrimeInt d) ∣ Y ^ 2 - P ^ 2 :=
    C_dvd_sq_sub_primePowerSeries_univ_sq hY hq
  have h_coeff : coeff 2 (P ^ 2) = 1 := by
    simpa using coeff_primePowerSeries_univ_sq (R := valRingCp p) hp_ne_two 0 0
  have hY_two : piPrimeInt d ∣ 1 - coeff 2 (Y ^ 2) := by
    rw [dvd_sub_comm, ← h_coeff, ← map_sub]
    exact C_dvd_iff_dvd_coeff.1 hY_sq_congr 2
  obtain ⟨Ξ, l, hΞ, hΞ_congr⟩ : ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
      seriesToCp Ξ = C.exponentSeries ϖ ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - l • (Y ^ 2 - half • X ^ 2) :=
    C.exists_seriesToCp_eq_exponentSeries_of_ramified hd hϖ hTY hY_two h_half
  refine ⟨Ξ, l, hΞ, ?_⟩
  rw [(hasSum_primePowerSeries_univ_sq_sub hp_ne_two h_half l).tsum_eq]
  exact dvd_sub_smul_of_dvd_sub hΞ_congr (by rwa [sub_sub_sub_cancel_right])

/-- Let `d ≡ 7` mod `8` be a prime, `C` a lattice with complex multiplication by the ring of
integers of `ℚ(√-d)`, and `p` a prime that does not split there. There are `ϖ ∈ ℂ_p` with
`‖ϖ‖ = p ^ (-ρ_p)` (where `‖p‖ = p⁻¹`), series `Ξ`, `W` over the ring `𝒪 = valRingCp p` of integers
of `ℂ_p` with `Ξ(0) = 0`, and numbers `λ_{e j} ∈ 𝒪` such that `θ(ϖ z) = W exp (c_ϖ Ξ)` and
`Ξ ≡ ∑_e ∑_j λ_{e j} (z ^ p ^ e z) ^ p ^ j` modulo `π_p`. Here `θ` is the Taylor series of the theta
function of `C`, read in `ℂ_p` by the embedding `ιₚ` that `PadicPlace p` fixes,
`c_ϖ = ϖ ^ (p + 1) / p`, `exp a` is written `expSubst a`, and `e` runs over
`I_p° = partnerExponents d p`: the odd numbers, or all if `p = d`. If `p` is inert, the `λ_{e 0}`
with `e` odd are units. -/
theorem CMLattice.exists_exponent_tsum (hp : chiK d p ≠ 1) :
    ∃ (ϖ : ℂ_[p]) (Ξ W : (valRingCp p)⟦X⟧) (l : ℕ → ℕ → valRingCp p),
      ‖ϖ‖ = p ^ (-varpiValuation d p) ∧
      constantCoeff Ξ = 0 ∧
      rescale ϖ (taylorVia ιₚ C.θ) = seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • seriesToCp Ξ) ∧
      PowerSeries.C (piPrimeInt d) ∣ Ξ - ∑' x : partnerExponents d p × ℕ,
        l x.1 x.2 • (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 ∧
      (chiK d p = -1 → ∀ e : ℕ, Odd e → IsUnit (l e 0)) := by
  -- Scale by `ϖ` so that `Y = T(ϖ z) / ϖ` is integral, and split `exp (c_ϖ Ξ₁)` off `θ(ϖ z)`.
  obtain ⟨ϖ, Y, hϖ, hTY, -, hY⟩ := C.exists_scaled_formalParam (p := p)
  obtain ⟨W, hW⟩ : ∃ W : (valRingCp p)⟦X⟧, rescale ϖ (taylorVia ιₚ C.θ) =
      seriesToCp W * expSubst ((ϖ ^ (p + 1) / p) • C.exponentSeries ϖ) :=
    C.exists_rescale_theta_eq_mul_expSubst (ne_zero_of_norm_eq_rpow hϖ) hϖ.le
  have h_zero {Ξ : (valRingCp p)⟦X⟧} (hΞ : seriesToCp Ξ = C.exponentSeries ϖ) :
      constantCoeff Ξ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← ZeroMemClass.coe_eq_zero, ← coeff_seriesToCp, hΞ,
      C.coeff_exponentSeries_eq_zero_of_lt hp (leastFlatDegree_pos d p)]
  rcases ramified_or_inert hp with ⟨hd, -⟩ | ⟨-, h_inert, -⟩
  · -- Take `λ_{0 0} = λ / 2`, `λ_{0 j} = λ` for `j ≥ 1`, and `λ_{e j} = 2 λ` for `e ≥ 1`.
    have h_all : partnerExponents d p = Set.univ := by simp [partnerExponents, hd]
    have h_not_inert : chiK d p ≠ -1 := by simp [chiK_eq_zero_of_ramified hd]
    have h_coprime : p.Coprime 2 :=
      (Nat.coprime_primes Fact.out Nat.prime_two).2 (ne_two_of_chiK_ne_one hp)
    have h_two : IsUnit ((2 : ℕ) : valRingCp p) :=
      isUnit_integer_iff_norm_eq_one.2 (h_coprime.norm_natCast_eq_one ℂ_[p])
    obtain ⟨half, h_half⟩ : ∃ half : valRingCp p, 2 * half = 1 := h_two.exists_right_inv
    obtain ⟨Ξ, l, hΞ, h_dvd⟩ : ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
        seriesToCp Ξ = C.exponentSeries ϖ ∧
        PowerSeries.C (piPrimeInt d) ∣ Ξ - ∑' x : ↥(Set.univ : Set ℕ) × ℕ,
          (if (x.1 : ℕ) = 0 then if x.2 = 0 then l * half else l else 2 * l) •
            (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 :=
      C.exists_exponentSeries_tsum_of_ramified hd hϖ hTY hY h_half
    let coef (e j : ℕ) : valRingCp p := if e = 0 then if j = 0 then l * half else l else 2 * l
    rw [← hΞ] at hW
    refine ⟨ϖ, Ξ, W, coef, hϖ, h_zero hΞ, hW, ?_, fun h_inert ↦ absurd h_inert h_not_inert⟩
    rwa [h_all]
  · -- Take `λ_{e j} = λ`.
    obtain ⟨Ξ, l, hΞ, h_dvd, h_unit⟩ : ∃ (Ξ : (valRingCp p)⟦X⟧) (l : valRingCp p),
        seriesToCp Ξ = C.exponentSeries ϖ ∧
        PowerSeries.C (piPrimeInt d) ∣
          Ξ - ∑' x : {e : ℕ | Odd e} × ℕ, l • (X ^ p ^ (x.1 : ℕ) * X) ^ p ^ x.2 ∧
        IsUnit l :=
      C.exists_eq_exponentSeries_dvd_sub_tsum_of_inert h_inert hϖ hTY hY
    rw [← hΞ] at hW
    refine ⟨ϖ, Ξ, W, fun _ _ ↦ l, hϖ, h_zero hΞ, hW, ?_, fun _ _ _ ↦ h_unit⟩
    rwa [partnerExponents_of_inert h_inert]

end New
