import Lib.Analytic.PrimeNumberTheorem.ZeroFreeRegion

/-!
# Primes congruent to `1` modulo `M ^ k` with logarithm in a prescribed window

Let `4 ∣ M` and let `A` be fixed. For large `W` there is a prime `p ≡ 1` modulo `M ^ k` with `log p`
in `[U, U + W]`, uniformly for `1 < k`, `M ^ k ≤ W ^ A` and `W ≤ U ≤ W ^ A`
(`New.exists_prime_modEq_one_log_mem`).

The characters modulo `M ^ k` with trivial square come from the fixed modulus `M ^ 2`, so the
zero-free region gives a disc about `1` without zeros, uniformly in `k`. Newman's contour argument
on its boundary yields the prime.

Independently, the first section proves `n ≤ φ n * (2 * log n + 1)` (`New.le_totient_mul_log`).

Notions from other files:
* `entireL χ` is `L(s, χ)`, times `s - 1` if `χ` is principal;
* `regularL χ` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal.

## Relation to the literature

Known result: primes congruent to `1` modulo `M ^ k` with logarithm in a prescribed window. It is a
consequence of the Siegel–Walfisz theorem. Only one prime is found, in a long window, and only for
moduli that are powers of a fixed multiple of `4`. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Cor. 11.19.
-/

/-! ## A lower bound for Euler's totient -/

section TotientBound

open Finset Real Nat Prime

/-- If every element of a finite set `S` of natural numbers exceeds `a`, then
`∏ p ∈ S, (1 - p⁻¹) ≥ a / (a + #S)`. -/
lemma New.div_add_card_le_prod_one_sub_inv (S : Finset ℕ) (a : ℕ) (ha : ∀ p ∈ S, a < p) :
    (a : ℚ) / (a + #S) ≤ ∏ p ∈ S, (1 - (p : ℚ)⁻¹) := by
  -- Remove the least element `b` of `S`: by induction the product is at least
  -- `(1 - b⁻¹) * b / (b + #S - 1) = (b - 1) / (b + #S - 1)`, and `a ≤ b - 1`.
  induction S using Finset.induction_on_min generalizing a with
  | empty => simp [div_self_le_one]
  | insert b S b_min ih =>
    have hab : (a : ℚ) + 1 ≤ b := mod_cast ha b (mem_insert_self b S)
    have hb : 0 < (b : ℚ) := lt_of_lt_of_le (by positivity) hab
    have hb_notMem : b ∉ S := fun h ↦ (b_min b h).false
    rw [prod_insert hb_notMem, card_insert_of_notMem hb_notMem, Nat.cast_succ]
    calc
      (a : ℚ) / (a + (#S + 1)) ≤ (b - 1) / (b + #S) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      _ = (1 - (b : ℚ)⁻¹) * (b / (b + #S)) := by field_simp
      _ ≤ (1 - (b : ℚ)⁻¹) * ∏ p ∈ S, (1 - (p : ℚ)⁻¹) :=
        mul_le_mul_of_nonneg_left (ih b b_min) (sub_nonneg.2 (cast_inv_le_one b))

/-- Every positive integer satisfies `n ≤ φ n * (2 * log n + 1)`. -/
lemma New.le_totient_mul_log {n : ℕ} (hn : 0 < n) : n ≤ φ n * (2 * Real.log n + 1) := by
  -- If `n` has `j` distinct prime factors, then `2 ^ j ≤ n`, so `j ≤ 2 * log n`, and
  -- `φ n / n = ∏ (1 - p⁻¹) ≥ 1 / (1 + j)`.
  set j : ℕ := #n.primeFactors
  have two_pow_le : 2 ^ j ≤ n :=
    (pow_card_le_prod _ _ 2 fun _ hp ↦ (prime_of_mem_primeFactors hp).two_le).trans
      (le_of_dvd hn n.prod_primeFactors_dvd)
  have card_le : j * Real.log 2 ≤ Real.log n := by grw [← two_pow_le]; simp
  have totient_ge : (n : ℝ) ≤ φ n * (1 + j) := by
    have h_prod : ((1 : ℕ) : ℚ) / ((1 : ℕ) + j) ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
      div_add_card_le_prod_one_sub_inv _ 1 fun _ hp ↦ (prime_of_mem_primeFactors hp).one_lt
    suffices h_rat : (n : ℚ) ≤ φ n * (1 + j) from mod_cast h_rat
    rw [totient_eq_mul_prod_factors, mul_assoc]
    exact le_mul_of_one_le_right (by positivity)
      ((div_le_iff₀ (by positivity)).1 (mod_cast h_prod))
  refine totient_ge.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  nlinarith [log_two_gt_d9]

end TotientBound

/-!
## Primes congruent to 1 mod M^k in a logarithmic window via Newman's method
-/

section AuxiliaryPrimes

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory LSeries Finset Real
  Topology vonMangoldt Chebyshev Polynomial ZMod MulChar

/-- If `4 ∣ M` and `2 ≤ k`, a character mod `M ^ k` whose square is trivial factors through modulus
`M ^ 2`, since every unit congruent to `1` mod `M ^ 2` is a square. -/
lemma New.factorsThrough_sq_of_sq_eq_one {M k : ℕ} [NeZero M] (hM : 4 ∣ M) (hk : 2 ≤ k)
    {χ : DirichletCharacter ℂ (M ^ k)} (hχ : χ ^ 2 = 1) :
    χ.FactorsThrough (M ^ 2) := by
  refine (χ.factorsThrough_iff_ker_unitsMap (pow_dvd_pow M hk)).mpr fun u hu ↦ ?_
  obtain ⟨m, hm⟩ := hM
  obtain ⟨t, ht⟩ : (↑(M ^ 2) : ℤ) ∣ 1 - (u : ZMod (M ^ k)).cast :=
    (intCast_eq_intCast_iff_dvd_sub u.val.cast 1 (M ^ 2)).mp
      (by simpa [unitsMap_def] using congrArg Units.val (MonoidHom.mem_ker.1 hu))
  have u_lin : 1 - (u : ZMod (M ^ k)) = M ^ 2 * t := by
    simpa using congrArg (Int.cast : ℤ → ZMod (M ^ k)) ht
  -- Newton's iteration from `0` solves `c ^ 2 + c = -M * m * t`, as the right side is nilpotent;
  -- then `(1 + 2 * c) ^ 2 = 1 - 4 * M * m * t = u`
  obtain ⟨c, hc⟩ : ∃ c : ZMod (M ^ k), M * m * t + c ^ 2 + c = 0 := by
    have h_nil : IsNilpotent ((M : ZMod (M ^ k)) * m * t) :=
      ⟨k, by simp [mul_pow, natCast_pow_eq_zero_of_le]⟩
    obtain ⟨c, ⟨-, hc⟩, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero (x := (0 : ZMod (M ^ k)))
      (P := C ((M : ZMod (M ^ k)) * m * t) + X ^ 2 + X) (by simpa using h_nil) (by simp)
    exact ⟨c, by simpa using hc⟩
  have hM_cast : (M : ZMod (M ^ k)) = 4 * m := by simp [hm]
  have u_eq : u = (1 + 2 * c) ^ 2 := by linear_combination -u_lin - 4 * hc - M * t * hM_cast
  refine Units.ext ?_
  simpa [u_eq, ← pow_apply', hχ] using one_apply_coe u

/-- If `4 ∣ M` and `2 ≤ k`, then for a character `χ` mod `M ^ k` with trivial square there is a
character `χ₀` mod `M ^ 2` with `regularL χ = regularL χ₀`, as the two moduli have the same prime
factors. Here `regularL χ` is `L(s, χ)`, times `(s - 1) / s` if `χ` is principal. -/
lemma New.exists_regularL_eq_of_sq_eq_one {M k : ℕ} [NeZero M] (hM : 4 ∣ M) (hk : 2 ≤ k)
    {χ : DirichletCharacter ℂ (M ^ k)} (hχ : χ ^ 2 = 1) :
    ∃ χ₀ : DirichletCharacter ℂ (M ^ 2), regularL χ = regularL χ₀ := by
  obtain ⟨h_dvd, χ₀, hχ₀⟩ := factorsThrough_sq_of_sq_eq_one hM hk hχ
  have h_one : χ = 1 ↔ χ₀ = 1 := by rw [hχ₀, changeLevel_eq_one_iff]
  have h_primes : (M ^ k).primeFactors = (M ^ 2).primeFactors := by
    simp [Nat.primeFactors_pow M (show k ≠ 0 by lia), Nat.primeFactors_pow M two_ne_zero]
  -- Changing the level multiplies by Euler factors at new primes, and there are none.
  have h_LFunction {z : ℂ} (h : χ₀ ≠ 1 ∨ z ≠ 1) : χ.LFunction z = χ₀.LFunction z := by
    rw [hχ₀, LFunction_changeLevel h_dvd χ₀ h, h_primes, Finset.prod_eq_one, mul_one]
    simp +contextual [ZMod.isUnit_prime_iff_not_dvd]
  have h_entire (z : ℂ) : entireL χ₀ z = entireL χ z := by
    by_cases hχ₀_one : χ₀ = 1
    · subst χ₀
      by_cases hz : z = 1 <;>
        simp [entireL, LFunctionTrivChar₁, LFunctionTrivChar, h_one.2 rfl, hz, h_primes,
          ← h_LFunction]
    · simp [entireL, hχ₀_one, mt h_one.1 hχ₀_one, h_LFunction (.inl hχ₀_one)]
  exact ⟨χ₀, funext fun z ↦ by by_cases h : χ₀ = 1 <;> simp [regularL, ← h_entire, h_one, h]⟩

/-- For `4 ∣ M` and `A` fixed, for all large `X` the following holds for every `k > 1`, every
Dirichlet character `χ` mod `M ^ k` with `M ^ k ≤ X ^ A`, and every `s` with `|s - 1| ≤ 1 / X`:
`entireL χ s ≠ 0` and `|logDeriv (entireL χ) s| ≤ X`. Here `entireL χ` is the entire function equal
to `L(s, χ)` for non-principal `χ`, and to the continuation of `(s - 1) L(s, χ)` for principal `χ`.
No exceptional zero can occur, because the real characters come from the fixed modulus `M ^ 2`. -/
lemma New.eventually_norm_logDeriv_entireL_le_near_one (A : ℕ) {M : ℕ} [NeZero M] (hM : 4 ∣ M) :
    ∀ᶠ X : ℝ in atTop, ∀ k : ℕ, 1 < k → ∀ (χ : DirichletCharacter ℂ (M ^ k)) (s : ℂ),
      (M : ℝ) ^ k ≤ X ^ A → ‖s - 1‖ ≤ X⁻¹ → entireL χ s ≠ 0 ∧ ‖logDeriv (entireL χ) s‖ ≤ X := by
  -- Apply the zero-free region with `l = (A + 1) log X`, for which `e ^ l = X ^ (A + 1)`.
  have h_log : Tendsto (fun X : ℝ ↦ (A + 1 : ℕ) * X.log) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop (by positivity)
  have h_inv : Tendsto (fun X : ℝ ↦ 1 / ((A + 1 : ℕ) * X.log)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h_log
  have h_small : (fun X : ℝ ↦ 2 * ((A + 1 : ℕ) * X.log) ^ 25) =o[atTop] id := by
    simpa only [mul_pow, ← mul_assoc] using
      (isLittleO_pow_log_id_atTop (n := 25)).const_mul_left (2 * ((A + 1 : ℕ) : ℝ) ^ 25)
  filter_upwards [h_log.eventually_ge_atTop (10 ^ 10), h_small.eventuallyLE, eventually_ge_atTop 2,
    h_inv.eventually (eventually_all.2 fun χ₀ : DirichletCharacter ℂ (M ^ 2) ↦
      eventually_le_norm_regularL χ₀)] with X hl h_pow hX h_near k hk χ s hq hs
  set l : ℝ := (A + 1 : ℕ) * X.log with l_def
  have hX_pos : 0 < X := by linarith
  have hl_pow : 0 < l ^ 25 := pow_pos (by linarith) 25
  replace h_pow : 2 * l ^ 25 ≤ X := (le_abs_self _).trans (h_pow.trans_eq (abs_of_pos hX_pos))
  have h_exp : rexp l = X ^ A * X := by
    rw [l_def, Real.exp_nat_mul, Real.exp_log hX_pos, pow_succ]
  have h_one : 1 ≤ X ^ A := one_le_pow₀ (by linarith)
  have h_re_lower : 1 - 1 / l ^ 25 ≤ s.re := by
    have h_inv_le : X⁻¹ ≤ 1 / l ^ 25 := by
      simpa using inv_anti₀ hl_pow (show l ^ 25 ≤ X by linarith)
    have h_re : |s.re - 1| ≤ X⁻¹ := by simpa using (abs_re_le_norm (s - 1)).trans hs
    linarith [abs_le.1 h_re]
  have h_norm : ‖s‖ ≤ 2 := by
    linarith [norm_le_norm_sub_add s 1, norm_one (α := ℂ),
      inv_le_one_of_one_le₀ (show 1 ≤ X by linarith)]
  have h_level : ((M ^ k : ℕ) : ℝ) ≤ rexp l := by push_cast; nlinarith
  have h_not_small : χ ^ 2 = 1 → ∀ z : ℂ, ‖z - 1‖ ≤ 1 / l → 1 / l ≤ ‖regularL χ z‖ := fun hχ ↦ by
    obtain ⟨χ₀, h_eq⟩ := exists_regularL_eq_of_sq_eq_one hM hk hχ
    simpa only [h_eq] using h_near χ₀
  exact (norm_logDeriv_entireL_le χ hl h_level h_not_small h_re_lower (by nlinarith)).imp_right
    fun h_le ↦ h_le.trans h_pow

/-- If `log n * (σ - re z) ≤ E`, then moving the `n`-th term of the Dirichlet series of `a` from
`1 + z` to the real point `1 + σ` costs at most the factor `exp E`. -/
lemma New.norm_term_le_exp_mul (a : ℕ → ℂ) {z : ℂ} (σ E : ℝ) {n : ℕ}
    (h_le : Real.log n * (σ - z.re) ≤ E) :
    ‖term a (1 + z) n‖ ≤ Real.exp E * ‖term a (1 + σ) n‖ := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  -- `↓cpow_add` must fire before simp rewrites the exponent.
  have h_eq : ‖term a (1 + z) n‖ = Real.exp (Real.log n * (σ - z.re)) * ‖term a (1 + σ) n‖ := by
    simp [hn, ↓cpow_add, cpow_def, norm_exp, field, mul_sub, Real.exp_sub, ← natCast_log]
  grw [h_eq, h_le]

/-- The Dirichlet series of the function that is `Λ n` at the numbers `n` that are not prime and
`0` at the primes converges absolutely at `3 / 4 = 1 + -4⁻¹`, because Chebyshev's functions satisfy
`ψ - θ = O(√x)`. -/
lemma New.summable_vonMangoldt_not_prime : Summable fun n : ℕ ↦
    ‖term (fun m : ℕ ↦ ((if m.Prime then 0 else vonMangoldt m : ℝ) : ℂ)) (1 + -4⁻¹) n‖ := by
  have h_bigO : (fun n : ℕ ↦ ∑ m ∈ Finset.Icc 1 n, if m.Prime then 0 else vonMangoldt m) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (2⁻¹ : ℝ) := by
    simpa [Function.comp_def, psi_sub_theta_eq_sum_not_prime, sum_filter, sqrt_eq_rpow,
      ← Finset.Icc_add_one_left_eq_Ioc] using isBigO_psi_sub_theta_sqrt.natCast_atTop
  exact (LSeriesSummable_of_sum_norm_bigO_and_nonneg h_bigO
    (fun m ↦ by split_ifs <;> simp [vonMangoldt_nonneg]) (by simp) (by norm_num)).norm

/-- For `0 < re z` the Dirichlet series of `Λ` on the class `1` mod `q` has at `1 + z` the sum
`(1 - z * ∑ χ, L_χ'/L_χ (1 + z)) / φ(q) / z`. Here `L_χ = entireL χ` is `L(s, χ)` with the pole
removed. -/
lemma New.hasSum_residueClass_one (q : ℕ) [NeZero q] {z : ℂ} (hz : 0 < z.re) :
    LSeriesHasSum (fun n : ℕ ↦ residueClass (1 : ZMod q) n) (1 + z)
      ((1 - z * ∑ χ : DirichletCharacter ℂ q, logDeriv (entireL χ) (1 + z)) / q.totient / z) := by
  -- Use orthogonality of characters; the pole term `1 / z` comes from `χ = 1`.
  have h_re : 1 < (1 + z).re := by simpa using hz
  have h_coeff : (fun n : ℕ ↦ (residueClass (1 : ZMod q) n : ℂ)) =
      (q.totient : ℂ)⁻¹ • ∑ χ : DirichletCharacter ℂ q, fun n : ℕ ↦ χ n * vonMangoldt n := by
    ext n
    simp [residueClass_apply]
  have h_value : (1 - z * ∑ χ : DirichletCharacter ℂ q, logDeriv (entireL χ) (1 + z)) / q.totient /
      z = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ((if χ = 1 then 1 else 0) / (1 + z - 1) - logDeriv (entireL χ) (1 + z)) := by
    simp [ite_div]
    field_simp [ne_zero_of_re_pos hz]
  rw [h_coeff, h_value]
  exact (LSeriesHasSum.sum fun χ _ ↦ LSeriesHasSum_mul_vonMangoldt χ h_re).smul _

/-- There are `φ(q) ≥ 1` characters mod `q`, so `‖1 - ∑ χ, z * c χ‖ ≤ 2 φ(q)` if each term of the
sum has norm at most `1`. -/
lemma New.norm_one_sub_mul_sum_div_totient_le {q : ℕ} [NeZero q] {z : ℂ}
    {c : DirichletCharacter ℂ q → ℂ} (hc : ∀ χ : DirichletCharacter ℂ q, ‖z * c χ‖ ≤ 1) :
    ‖(1 - z * ∑ χ : DirichletCharacter ℂ q, c χ) / q.totient‖ ≤ 2 := by
  have h_pos : 1 ≤ (q.totient : ℝ) := mod_cast Nat.totient_pos.2 (NeZero.pos q)
  have h_sum : ∑ χ : DirichletCharacter ℂ q, ‖z * c χ‖ ≤ q.totient := by
    grw [sum_le_card_nsmul _ _ 1 fun χ _ ↦ hc χ]
    simp [← card_eq_totient_of_hasEnoughRootsOfUnity ℂ]
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith), mul_sum]
  grw [norm_sub_le, norm_sum_le, norm_one]
  linarith

/-- On the circle `‖z‖ = 1 / X` the real part of `2 - U z - X (1 + X z)² / 4`, the exponent in
Newman's method, is at least (in fact equal to) that of `2 - (U + t) z` for some `t ∈ [0, X ^ 2]`,
namely `t = X ^ 2 / 2 * (1 + X * re z)`: the quadratic term acts as a shift of `U` by `t`. -/
lemma New.exists_shift_le_re_exponent (U : ℝ) {X : ℝ} (hX : 0 < X) {z : ℂ} (hz : ‖z‖ = X⁻¹) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ X ^ 2 ∧
      2 - (U + t) * z.re ≤ (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2 : ℂ).re := by
  refine ⟨X ^ 2 / 2 * (1 + X * z.re), ?_⟩
  obtain ⟨h_lower, h_upper⟩ : -1 ≤ X * z.re ∧ X * z.re ≤ 1 := by
    rw [← abs_le, abs_mul, abs_of_pos hX]
    grw [z.abs_re_le_norm, hz, mul_inv_cancel₀ hX.ne']
  have h_im : X ^ 2 * z.im ^ 2 = 1 - (X * z.re) ^ 2 := by
    rw [← z.sq_norm_sub_sq_re, hz]
    field_simp
  have h_exponent : (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2 : ℂ).re =
      2 - U * z.re - X / 4 * ((1 + X * z.re) ^ 2 - X ^ 2 * z.im ^ 2) := by simp [sq]; ring
  refine ⟨mul_nonneg (by positivity) (by linarith), by nlinarith, le_of_eq ?_⟩
  linear_combination -h_exponent - X / 4 * h_im

section Circle

variable {a : ℕ → ℝ} {b : ℕ → ℂ} {F : ℂ → ℂ} {X U C : ℝ}

/-- Let `a ≥ 0` have the Dirichlet series `F z / z` at `1 + z` for `0 < re z`, with `‖F‖ ≤ 2` on
`‖z‖ ≤ 1 / X`, and let the series of `b` at `3 / 4` have absolute sum `C ≤ X`, where `200 ≤ X` and
`X² ≤ U`. If on a set of `n` the terms of the series of `a` at `1 + z` are at most `e ^ E` times
the sum of those of `a` at `1 + 1 / U` and those of `b` at `3 / 4`, then this part of the series is
at most `3 U e ^ E`. -/
lemma New.norm_le_of_term_le_majorant (ha : ∀ n : ℕ, 0 ≤ a n)
    (h_series : ∀ z : ℂ, 0 < z.re → LSeriesHasSum (fun n : ℕ ↦ (a n : ℂ)) (1 + z) (F z / z))
    (hF : ∀ z : ℂ, ‖z‖ ≤ X⁻¹ → ‖F z‖ ≤ 2) (hC : HasSum (fun n : ℕ ↦ ‖term b (1 + -4⁻¹) n‖) C)
    (hCX : C ≤ X) (hX : 200 ≤ X) (hU : X ^ 2 ≤ U) {z S : ℂ} {E : ℝ} {s : Set ℕ}
    (hS : HasSum (fun n : s ↦ term (fun n : ℕ ↦ (a n : ℂ)) (1 + z) n) S)
    (h_le : ∀ n ∈ s, ‖term (fun n : ℕ ↦ (a n : ℂ)) (1 + z) n‖ ≤
      rexp E * (‖term (fun n : ℕ ↦ (a n : ℂ)) (1 + (U⁻¹ : ℝ)) n‖ + ‖term b (1 + -4⁻¹) n‖)) :
    ‖S‖ ≤ rexp E * (3 * U) := by
  -- The whole series of `a` at `1 + 1 / U` is `U F (1 / U) ≤ 2 U`.
  have hXU : X ≤ U := by nlinarith
  have hU_pos : 0 < U := by linarith
  have hX_pos' : 0 < X := by linarith
  have h_norm : HasSum (fun n : ℕ ↦ (‖term (fun n : ℕ ↦ (a n : ℂ)) (1 + (U⁻¹ : ℝ)) n‖ : ℂ))
      (F (U⁻¹ : ℝ) / (U⁻¹ : ℝ)) := by
    refine (h_series _ (by simpa using hU_pos)).congr_fun fun n ↦ ?_
    -- The order on `ℂ` is not in scope, so the two facts `0 ≤ _` in `ℂ` are left to `mod_cast`.
    exact norm_of_nonneg' (mod_cast term_nonneg (mod_cast ha n) (1 + U⁻¹))
  have h_total : (F (U⁻¹ : ℝ) / (U⁻¹ : ℝ)).re ≤ 2 * U := by
    have h_abs : ‖((U⁻¹ : ℝ) : ℂ)‖ = U⁻¹ := by simp [hU_pos.le]
    grw [re_le_norm, norm_div, hF _ (h_abs.trans_le (inv_anti₀ hX_pos' hXU)), h_abs, div_inv_eq_mul]
  have h_part : HasSum (s.indicator (term (fun n : ℕ ↦ (a n : ℂ)) (1 + z))) S :=
    hasSum_subtype_iff_indicator.1 hS
  have h_bound (n : ℕ) : ‖s.indicator (term (fun n : ℕ ↦ (a n : ℂ)) (1 + z)) n‖ ≤
      rexp E * (‖term (fun n : ℕ ↦ (a n : ℂ)) (1 + (U⁻¹ : ℝ)) n‖ + ‖term b (1 + -4⁻¹) n‖) := by
    rw [norm_indicator_eq_indicator_norm]
    exact indicator_le' h_le (fun _ _ ↦ by positivity) n
  calc
    ‖S‖ ≤ rexp E * ((F (U⁻¹ : ℝ) / (U⁻¹ : ℝ)).re + C) :=
      h_part.norm_le_of_bounded (((hasSum_re h_norm).add hC).mul_left _) h_bound
    _ ≤ rexp E * (3 * U) := by
      gcongr
      linarith

/-- The bound on the circle in Newman's method. Let `a ≥ 0` have the Dirichlet series `F z / z` at
`1 + z` for `0 < re z` (here `term a s n` is the summand `a n / n ^ s`), with `‖F‖ ≤ 2` on
`‖z‖ ≤ 1 / X`. Let the series of `b` at `3 / 4` have absolute sum `C ≤ X`, let `200 ≤ X` and
`X² ≤ U`, and let `|a n| ≤ |b n|` whenever `log n` lies in `[U, U + X²]`. Then on `‖z‖ = 1 / X` we
have `‖F z - z P z‖ ≤ 3 U e ^ E`, where `P z` is the part with `n < e ^ U` of the series of `a`
and `E` is the real part of `2 - U z - X (1 + X z)² / 4`. -/
lemma New.norm_sub_mul_sum_term_le (ha : ∀ n : ℕ, 0 ≤ a n)
    (h_series : ∀ z : ℂ, 0 < z.re → LSeriesHasSum (fun n : ℕ ↦ (a n : ℂ)) (1 + z) (F z / z))
    (hF : ∀ z : ℂ, ‖z‖ ≤ X⁻¹ → ‖F z‖ ≤ 2) (hC : HasSum (fun n : ℕ ↦ ‖term b (1 + -4⁻¹) n‖) C)
    (hCX : C ≤ X) (hX : 200 ≤ X) (hU : X ^ 2 ≤ U)
    (h_window : ∀ n : ℕ, Real.log n ∈ Set.Icc U (U + X ^ 2) → ‖(a n : ℂ)‖ ≤ ‖b n‖) {z : ℂ}
    (hz : ‖z‖ = X⁻¹) :
    ‖F z - z * ∑ n ∈ .range ⌈rexp U⌉₊, term (fun n : ℕ ↦ (a n : ℂ)) (1 + z) n‖ ≤
      rexp (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2 : ℂ).re * (3 * U) := by
  have hX_pos : 0 < X := by linarith
  have hU_pos : 0 < U := (pow_pos hX_pos 2).trans_le hU
  have hz_small : ‖z‖ ≤ 200⁻¹ := hz.trans_le (inv_anti₀ (by simp) hX)
  set E : ℝ := (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2 : ℂ).re
  set P : ℂ := ∑ n ∈ .range ⌈rexp U⌉₊, term (fun n : ℕ ↦ (a n : ℂ)) (1 + z) n
  -- On the circle the Gaussian factor shifts the cut from `U` to a point `U + t` of the window.
  obtain ⟨t, ht_nonneg, ht_le, hE⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ X ^ 2 ∧ 2 - (U + t) * z.re ≤ E :=
    exists_shift_le_re_exponent U hX_pos hz
  have h_unit : U * U⁻¹ = 1 := mul_inv_cancel₀ hU_pos.ne'
  have h_shift : t * U⁻¹ ≤ 1 := (div_le_one hU_pos).2 (ht_le.trans hU)
  have h_term_le_sum {n : ℕ} (h : Real.log n * (U⁻¹ - z.re) ≤ E) :
      ‖term (fun n : ℕ ↦ (a n : ℂ)) (1 + z) n‖ ≤ rexp E *
        (‖term (fun n : ℕ ↦ (a n : ℂ)) (1 + (U⁻¹ : ℝ)) n‖ + ‖term b (1 + -4⁻¹) n‖) :=
    (norm_term_le_exp_mul _ U⁻¹ E h).trans (by gcongr; simp)
  rcases le_total z.re U⁻¹ with h_left | h_right
  · -- If `re z ≤ 1 / U`, then `E ≥ 0`, and we bound `F` and the finite sum `P` separately.
    have hU_re : U * z.re ≤ 1 := (mul_le_mul_of_nonneg_left h_left hU_pos.le).trans_eq h_unit
    have ht_re : t * z.re ≤ 1 := (mul_le_mul_of_nonneg_left h_left ht_nonneg).trans h_shift
    have hE_nonneg : 0 ≤ E := by linarith
    have hP : ‖P‖ ≤ rexp E * (3 * U) := by
      refine norm_le_of_term_le_majorant ha h_series hF hC hCX hX hU (Finset.hasSum ..) fun n hn ↦
        h_term_le_sum ?_
      have hn_lt : n < rexp U := Nat.lt_ceil.1 (mem_range.1 hn)
      have h_log : Real.log n ≤ U := by
        obtain rfl | hn_pos := n.eq_zero_or_pos
        · simpa using hU_pos.le
        · exact ((log_lt_iff_lt_exp (mod_cast hn_pos)).2 hn_lt).le
      have h_exponent : Real.log n * (U⁻¹ - z.re) ≤ U * (U⁻¹ - z.re) :=
        mul_le_mul_of_nonneg_right h_log (sub_nonneg.2 h_left)
      linarith
    calc
      ‖F z - z * P‖ ≤ ‖F z‖ + ‖z‖ * ‖P‖ := by grw [norm_sub_le, norm_mul]
      _ ≤ 2 + 200⁻¹ * (rexp E * (3 * U)) := by grw [hF z hz.le, hz_small, hP]
      _ ≤ rexp E * (3 * U) := by nlinarith only [E.one_le_exp hE_nonneg, hU, hX]
  · -- If `re z ≥ 1 / U`, then `F z - z P` is `z` times the tail `n ≥ e ^ U` of the series.
    have h_pos : 0 < z.re := (inv_pos.2 hU_pos).trans_le h_right
    have h_tail : ‖F z / z - P‖ ≤ rexp E * (3 * U) := by
      refine norm_le_of_term_le_majorant ha h_series hF hC hCX hX hU
        ((Finset.hasSum_iff_compl _).1 (h_series z h_pos)) fun n hn ↦ ?_
      have hn_ge : rexp U ≤ n := Nat.ceil_le.1 (not_lt.1 (mt Finset.mem_range.2 hn))
      have h_log : U ≤ Real.log n := (le_log_iff_exp_le (U.exp_pos.trans_le hn_ge)).2 hn_ge
      rcases le_total (Real.log n) (U + X ^ 2) with h_in | h_out
      · -- In the window compare with the series of `b`.
        have ht_re : t * z.re ≤ U * 200⁻¹ :=
          mul_le_mul (ht_le.trans hU) (z.re_le_norm.trans hz_small) h_pos.le hU_pos.le
        have h_exponent_le : Real.log n * (-4⁻¹ - z.re) ≤ E := by
          have h_move : Real.log n * (-4⁻¹ - z.re) ≤ U * (-4⁻¹ - z.re) :=
            mul_le_mul_of_nonpos_right h_log (by linarith)
          linarith
        grw [← norm_term_le (f := fun n : ℕ ↦ (a n : ℂ)) (g := b) _ (h_window n ⟨h_log, h_in⟩),
          norm_term_le_exp_mul _ _ E h_exponent_le]
        simp [exp_pos]
      · -- Beyond the window we have `log n ≥ U + X² ≥ U + t`.
        refine h_term_le_sum ?_
        have h_move : Real.log n * (U⁻¹ - z.re) ≤ (U + t) * (U⁻¹ - z.re) :=
          mul_le_mul_of_nonpos_right (by linarith) (sub_nonpos.2 h_right)
        linarith
    calc
      ‖F z - z * P‖ = ‖z * (F z / z - P)‖ := by
        rw [mul_sub, mul_div_cancel₀ _ (ne_zero_of_re_pos h_pos)]
      _ ≤ rexp E * (3 * U) := by grw [norm_mul, h_tail, show ‖z‖ ≤ 1 by linarith, one_mul]

end Circle

/-- The function `F z - z P z` of Newman's method is analytic on a disc on which no
`entireL χ (1 + z)` vanishes: here `F z = (1 - z * ∑ χ, L_χ'/L_χ (1 + z)) / φ(q)`, with
`L_χ = entireL χ`, and `P z` is the part with `n < N` of the Dirichlet series at `1 + z` of `Λ` on
the class `1` mod `q` (`residueClass`). -/
lemma New.analyticOnNhd_sub_mul_sum_term (q : ℕ) [NeZero q] (N : ℕ) {r : ℝ}
    (h_ne : ∀ z : ℂ, ‖z‖ ≤ r → ∀ χ : DirichletCharacter ℂ q, entireL χ (1 + z) ≠ 0) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦
      (1 - z * ∑ χ : DirichletCharacter ℂ q, logDeriv (entireL χ) (1 + z)) / q.totient -
        z * ∑ n ∈ .range N, term (fun n : ℕ ↦ (residueClass (1 : ZMod q) n : ℂ)) (1 + z) n)
      (Metric.closedBall 0 r) := by
  intro z hz
  have hz_ne (χ : DirichletCharacter ℂ q) : entireL χ (1 + z) ≠ 0 := h_ne z (by simpa using hz) χ
  have h_term (i : ℕ) : AnalyticAt ℂ
      (fun s : ℂ ↦ term (fun n : ℕ ↦ (residueClass (1 : ZMod q) n : ℂ)) s i) (1 + z) :=
    Differentiable.analyticAt (fun s ↦ (hasDerivAt_term _ i s).differentiableAt) _
  fun_prop (disch := simp_all) [logDeriv]

/-- Let `4 ∣ M` and let `A` be fixed. For all large `W` there is a prime `p ≡ 1` mod `M ^ k` with
`U ≤ log p ≤ U + W`, whenever `1 < k`, `M ^ k ≤ W ^ A` and `W ≤ U ≤ W ^ A`. This is a consequence
of the Siegel–Walfisz theorem, proved here directly by Newman's contour method. -/
theorem New.exists_prime_modEq_one_log_mem (M A : ℕ) [NeZero M] (hM : 4 ∣ M) :
    ∀ᶠ W : ℝ in atTop, ∀ k : ℕ, 1 < k → (M : ℝ) ^ k ≤ W ^ A → ∀ U : ℝ, U ∈ Set.Icc W (W ^ A) →
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD M ^ k] ∧ Real.log p ∈ Set.Icc U (U + W) := by
  -- Write `W = X ^ 2`, `q = M ^ k`. Let `F z / z` be the Dirichlet series of `Λ` on `1 mod q` at
  -- `1 + z`, and `P` its part with `n < e ^ U`. If the window has no prime, `F z - z P z` over
  -- `exp (2 - U z - X (1 + X z)² / 4)` is at most `3 U` on `‖z‖ = 1 / X`, yet of size
  -- `e ^ (X / 4 - 2) / φ(q)` at `0`.
  let b (n : ℕ) : ℂ := ↑(if n.Prime then 0 else vonMangoldt n : ℝ)
  obtain ⟨C, hC⟩ : Summable fun n ↦ ‖term b (1 + -4⁻¹) n‖ := summable_vonMangoldt_not_prime
  -- Take `X` large: `q, U ≤ X ^ (2 * A)`, so `3 * U * q ≤ 3 * X ^ (4 * A) < e ^ (X / 4 - 2)`.
  -- The substitution `W = X ^ 2` turns "for large `W`" into "for large `X = √W`".
  rw [← comap_sqrt_atTop, eventually_comap]
  filter_upwards [eventually_norm_logDeriv_entireL_le_near_one (2 * A) hM,
    (tendsto_exp_mul_div_rpow_atTop ↑(4 * A) 4⁻¹ (by simp)).eventually_gt_atTop (.exp 2 * 3),
    eventually_ge_atTop 200, eventually_ge_atTop C, eventually_gt_atTop 0] with
    X h_free h_exp hX200 hXC hX W hW k hk hq U ⟨hWU, hU⟩
  obtain rfl : W = X ^ 2 := by rw [← hW, sq_sqrt (sqrt_pos.1 (hX.trans_eq hW.symm)).le]
  have hU_pos : 0 < U := (pow_pos hX 2).trans_le hWU
  set q : ℕ := M ^ k
  simp only [← pow_mul, rpow_natCast, ← natCast_eq_natCast_iff, Nat.cast_one,
    Set.mem_Icc] at hq hU h_exp ⊢
  have hq_cast : (q : ℝ) ≤ X ^ (2 * A) := by simpa [q] using hq
  let a (n : ℕ) : ℂ := residueClass (1 : ZMod q) n
  let F (z : ℂ) : ℂ :=
    (1 - z * ∑ χ : DirichletCharacter ℂ q, logDeriv (entireL χ) (1 + z)) / q.totient
  have h_series (z : ℂ) (hz : 0 < z.re) : LSeriesHasSum a (1 + z) (F z / z) :=
    hasSum_residueClass_one q hz
  -- For `‖z‖ ≤ 1 / X` each `z * logDeriv (entireL χ)` has norm at most `1`, so `‖F‖ ≤ 2`.
  have h_disc {z : ℂ} (hz : ‖z‖ ≤ X⁻¹) (χ : DirichletCharacter ℂ q) :
      entireL χ (1 + z) ≠ 0 ∧ ‖logDeriv (entireL χ) (1 + z)‖ ≤ X :=
    h_free k hk χ (1 + z) hq (by simpa)
  have hF (z : ℂ) (hz : ‖z‖ ≤ X⁻¹) : ‖F z‖ ≤ 2 := norm_one_sub_mul_sum_div_totient_le fun χ ↦ by
    grw [norm_mul, hz, (h_disc hz χ).2, inv_mul_cancel₀ hX.ne']
  by_contra h_none
  let P (z : ℂ) : ℂ := ∑ n ∈ .range ⌈U.exp⌉₊, term a (1 + z) n
  let G (z : ℂ) : ℂ := (F z - z * P z) / (2 - U * z - 4⁻¹ * X * (1 + X * z) ^ 2).exp
  -- A bound on the circle bounds `G 0`, which is too large.
  suffices h_circle : ∀ z : ℂ, ‖z‖ = X⁻¹ → ‖G z‖ ≤ 3 * U by
    have hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 X⁻¹) := fun s hs ↦
      (analyticOnNhd_sub_mul_sum_term q ⌈U.exp⌉₊ (fun z hz χ ↦ (h_disc hz χ).1) s hs).div
        (by fun_prop) (Complex.exp_ne_zero _)
    have h_zero : ‖G 0‖ ≤ 3 * U := by
      simpa using norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0 (inv_pos.2 hX)
        (hG.differentiableOn.diffContOnCl_ball le_rfl) (by simpa using h_circle)
    have h_value : ‖G 0‖ = rexp (4⁻¹ * X) / rexp 2 / q.totient := by
      simp [G, F, norm_exp, Real.exp_sub, field]
    have h_large : 3 * U < rexp (4⁻¹ * X) / rexp 2 / q.totient := by
      rw [lt_div_iff₀ (mod_cast Nat.totient_pos.2 (NeZero.pos q)), lt_div_iff₀ (exp_pos 2)]
      calc
        3 * U * q.totient * rexp 2 ≤ 3 * X ^ (2 * A) * X ^ (2 * A) * rexp 2 := by
          grw [Nat.totient_le, hq_cast, hU]
        _ = rexp 2 * 3 * X ^ (4 * A) := by ring
        _ < rexp (4⁻¹ * X) := (lt_div_iff₀ (by positivity)).1 h_exp
    linarith
  intro z hz
  rw [norm_div, norm_exp, div_le_iff₀' (by bound)]
  refine norm_sub_mul_sum_term_le (residueClass_nonneg _) h_series hF hC hXC hX200 hWU
    (fun n hn ↦ ?_) hz
  -- In the window no `n ≡ 1` is prime, so `Λ` on the class is at most `Λ` on the non-primes.
  by_cases h_prime : n.Prime
  · have h_class : (n : ZMod q) ≠ 1 := fun h ↦ h_none ⟨n, h_prime, h, hn⟩
    simp [residueClass, h_class]
  · simpa [b, h_prime, abs_of_nonneg, residueClass_nonneg] using residueClass_le (1 : ZMod q) n

end AuxiliaryPrimes
