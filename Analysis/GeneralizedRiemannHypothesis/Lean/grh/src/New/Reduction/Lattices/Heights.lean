import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# The height of a family over all places: products, monotonicity and the product formula

A height for families of complex numbers indexed by the pairs `ι` of a prime `l` and an isomorphism
`ℂ ≃+* ℚ̄_l` (`New.PrimePadicIso`).

* `New.HeightLe c y`: for some multiplier `H ≠ 0` and some `h l ≥ 0`, the conjugates of `H` are
  bounded by `exp α`, the numbers `H * y ι` are bounded `l`-adically by `l ^ h l`, and
  `α + ∑ h l * log l ≤ c` over every finite set of primes.
* `New.HeightLe.of_mul_le`, `New.HeightLe.of_le`, `New.HeightLe.mono`, `New.HeightLe.mul`,
  `New.HeightLe.prod`, `New.HeightLe.pow`: the calculus of heights.
* `New.HeightLe.nonneg_of_one`: the constant family `1` has height at least `0`, by the product
  formula (`New.log_product_formula`) for the norm of `H`. `New.HeightLe.neg_le_of_norm_map_le` is
  the form for a number `z ≠ 0`.

## Relation to the literature

The multiplier H, and so the bound at infinity, does not depend on ι, while y ι may; so each prime
may use its own twist. Related work: Gaudron, Pentes des fibrés vectoriels adéliques sur un corps
global, 2006; Bombieri–Gubler, Heights in Diophantine Geometry, ch. 1, 2006.
-/

open Algebra Module Real Finset Filter IntermediateField AdjoinSimple Padic PadicAlgCl

namespace New

/-- A prime `l` together with an isomorphism of `ℂ` with the algebraic closure `ℚ̄_l` of `ℚ_l`. -/
structure PrimePadicIso : Type where
  /-- The prime `l`. -/
  prime : Nat.Primes
  /-- The isomorphism `ℂ ≃+* ℚ̄_l`. -/
  iso : ℂ ≃+* PadicAlgCl prime

variable {c c' : ℝ} {y y' : PrimePadicIso → ℂ}

/-- The family `y`, with one complex number for each pair `ι` of a prime `l` and an isomorphism
`ℂ ≃+* ℚ̄_l`, has height at most `c`: there are a multiplier `H ≠ 0` and real numbers `h_∞ = α` and
`h_l = h l ≥ 0` with the three properties below. -/
def HeightLe (c : ℝ) (y : PrimePadicIso → ℂ) : Prop :=
  ∃ (H : ℂ) (α : ℝ) (h : ℕ → ℝ), H ≠ 0 ∧ (∀ l : ℕ, 0 ≤ h l) ∧
    -- `log |σ H| ≤ h_∞` for all `σ`
    (∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp α) ∧
    -- `v_ι(H y_ι) ≥ -h_l` for all `ι`, with `l = ι.prime`
    (∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ ((ι.prime : ℕ) : ℝ) ^ h ι.prime) ∧
    -- `h_∞ + ∑ h_l log l ≤ c`, for the sum over every finite set of primes
    ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → α + ∑ l ∈ T, h l * log l ≤ c

/-- The product formula for `ℚ`, in logarithms: `log |q| + ∑ log |q|_p = 0` (`log q` is `log |q|`
and `log 0 = 0`), the sum taken over the primes below any bound `M` that exceeds the absolute value
of the numerator of `q` and the denominator of `q`. -/
lemma log_product_formula {M : ℕ} {q : ℚ} (h_num_lt : q.num.natAbs < M) (h_den_lt : q.den < M) :
    log q + ∑ p ∈ range M with p.Prime, log (padicNorm p q) = 0 := by
  -- Factor the numerator and the denominator into primes and take logarithms; the term of `p`
  -- in `log |q|` is `v_p(q) * log p`, which cancels `log |q|_p = -v_p(q) * log p`.
  obtain rfl | hq := eq_or_ne q 0
  · simp
  have log_nat {n : ℕ} (hn : n ≠ 0) (hnM : n < M) :
      log n = ∑ p ∈ range M with p.Prime, padicValNat p n * log p := by
    conv_lhs => rw [← Nat.prod_pow_prime_padicValNat n hn M hnM]
    simp +contextual [log_prod, Nat.Prime.ne_zero]
  have log_q : log q = log q.num.natAbs - log q.den := by simp [q.cast_def, log_div, hq]
  have log_norm (p : ℕ) :
      log (padicNorm p q) = (padicValNat p q.den - padicValNat p q.num.natAbs) * log p := by
    simp [padicNorm.eq_zpow_of_nonzero hq, padicValRat, padicValInt]
  rw [log_q, log_nat (by simpa using hq) h_num_lt, log_nat q.den_nz h_den_lt]
  simp [log_norm, sub_mul]

namespace HeightLe

/-! ### The calculus of heights -/

/-- Let `y`, `y'` be families of complex numbers indexed by the pairs `ι` of a prime `l` and an
isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`. If `y` has height at most `c ≤ c'`, and `y' ι` is `l`-adically no
larger than `y ι` under each `ι.iso`, then `y'` has height at most `c'`. -/
lemma mono (hy : HeightLe c y) (hc : c ≤ c')
    (h_le : ∀ ι : PrimePadicIso, ‖ι.iso (y' ι)‖ ≤ ‖ι.iso (y ι)‖) : HeightLe c' y' := by
  obtain ⟨H, α, e, hH, he_nonneg, hα, he, h_sum⟩ := hy
  refine ⟨H, α, e, hH, he_nonneg, hα, fun ι ↦ ?_, fun T hT ↦ (h_sum T hT).trans hc⟩
  calc ‖ι.iso (H * y' ι)‖ ≤ ‖ι.iso (H * y ι)‖ := by
        simpa only [map_mul, norm_mul] using mul_le_mul_of_nonneg_left (h_le ι) (norm_nonneg _)
    _ ≤ ((ι.prime : ℕ) : ℝ) ^ e ι.prime := he ι

/-- Let `y` be a family of complex numbers indexed by the pairs `ι` of a prime `l` and an
isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`, of height at most `c ≤ c'`. Multiplying `y ι` by a rational power
`N ι ^ e ι` of a natural number `N ι` prime to `l` gives a family of height at most `c'`. -/
lemma rpow_mul (hy : HeightLe c y) (hc : c ≤ c') {N : PrimePadicIso → ℕ}
    (hN : ∀ ι : PrimePadicIso, Nat.Coprime ι.prime (N ι)) (e : PrimePadicIso → ℚ) :
    HeightLe c' fun ι : PrimePadicIso ↦ ((N ι : ℝ) ^ (e ι : ℝ) : ℝ) * y ι := by
  -- The positive integral power `(N ι ^ e ι) ^ (e ι).den` is an integral power of `N ι`, which is
  -- a unit at the prime of `ι`; so `N ι ^ e ι` has norm `1` under `ι.iso`.
  refine hy.mono hc fun ι ↦ ?_
  have h_exp : (e ι : ℝ) * (e ι).den = (e ι).num := mod_cast (e ι).mul_den_eq_num
  have h_pow : (((N ι : ℝ) ^ (e ι : ℝ) : ℝ) : ℂ) ^ (e ι).den = (N ι : ℂ) ^ (e ι).num := by
    simp [← Complex.ofReal_pow, ← rpow_mul_natCast, h_exp]
  have h_unit : ‖ι.iso ((N ι : ℝ) ^ (e ι : ℝ) : ℝ)‖ = 1 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) (e ι).den_nz, ← norm_pow, ← map_pow, h_pow]
    simp [(hN ι).norm_natCast_eq_one]
  rw [map_mul, norm_mul, h_unit, one_mul]

/-- Let `y` be a family of complex numbers indexed by the pairs `ι` of a prime `l` and an
isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`. Suppose `H ≠ 0` has `|σ H| ≤ exp α` for all automorphisms `σ` of
`ℂ`, `H * y ι` has `l`-adic norm at most `exp (e l)` under each `ι.iso`, and `α + ∑ e l ≤ c` for the
sum over every finite set of primes. Then `y` has height at most `c`. The `e l` may have any
sign. -/
lemma of_mul_le {H : ℂ} {α : ℝ} {e : ℕ → ℝ} (hH : H ≠ 0) (hα : ∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp α)
    (he : ∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ exp (e ι.prime))
    (h_sum : ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → α + ∑ l ∈ T, e l ≤ c) : HeightLe c y := by
  -- Take `h_l = (e l)₊ / log l`. The sum of `(e l)₊` over `T` is that of `e l` over a part of `T`.
  have h_cancel {l : ℕ} (hl : l.Prime) : (e l)⁺ / log l * log l = (e l)⁺ := by simp [hl.log_pos.ne']
  refine ⟨H, α, fun l ↦ (e l)⁺ / log l, hH, fun l ↦ by positivity, hα, fun ι ↦ ?_, fun T hT ↦ ?_⟩
  · rw [rpow_def_of_pos (mod_cast ι.prime.prop.pos), mul_comm (log _), h_cancel ι.prime.prop]
    exact (he ι).trans (exp_le_exp.2 (le_posPart _))
  · calc α + ∑ l ∈ T, (e l)⁺ / log l * log l = α + ∑ l ∈ T with 0 ≤ e l, e l := by
          rw [sum_filter, sum_congr rfl fun l hl ↦ h_cancel (hT l hl)]
          simp only [posPart_def, max_def'] -- `(e l)⁺` is `e l` if `0 ≤ e l`, and else `0`
      _ ≤ c := h_sum _ fun l hl ↦ hT l (mem_filter.1 hl).1

/-- If reals `e l` have sum at most `c` over every finite set of primes, and `y ι` has `l`-adic norm
at most `exp (e l)` under `ι.iso` for every pair `ι` of a prime `l = ι.prime` and an isomorphism
`ι.iso : ℂ ≃+* ℚ̄_l`, then the family `y` has height at most `c`: some `H ≠ 0`, `α` and `h l ≥ 0`
satisfy `|σ H| ≤ exp α` for all automorphisms `σ` of `ℂ`, `‖ι.iso (H * y ι)‖ ≤ l ^ h l` for all `ι`,
and `α + ∑ h l * log l ≤ c` over finite sets of primes. -/
lemma of_le {e : ℕ → ℝ} (h_sum : ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, e l ≤ c)
    (h_norm : ∀ ι : PrimePadicIso, ‖ι.iso (y ι)‖ ≤ exp (e ι.prime)) : HeightLe c y :=
  of_mul_le (α := 0) one_ne_zero (by simp) (by simpa using h_norm) (by simpa using h_sum)

/-- If `H ≠ 0` and `|σ H| ≤ exp c` for all automorphisms `σ` of `ℂ`, then the constant family `H⁻¹`,
indexed by the pairs `ι` of a prime `l` and an isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`, has height at most
`c`: some `H' ≠ 0`, `α` and `h l ≥ 0` satisfy `|σ H'| ≤ exp α` for all `σ`,
`‖ι.iso (H' * H⁻¹)‖ ≤ l ^ h l` for all `ι`, and `α + ∑ h l * log l ≤ c` over finite sets of
primes. -/
lemma inv_const {H : ℂ} (hH : H ≠ 0) (h_conj : ∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ exp c) :
    HeightLe c fun _ : PrimePadicIso ↦ H⁻¹ :=
  of_mul_le (e := 0) hH h_conj (by simp [hH]) (by simp)

/-- Let `y`, `y'` be families of complex numbers indexed by the pairs `ι` of a prime `l` and an
isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`, of height at most `c` and `c'`; then the pointwise product
`y * y'` has height at most `c + c'`. -/
lemma mul (hy : HeightLe c y) (hy' : HeightLe c' y') : HeightLe (c + c') (y * y') := by
  obtain ⟨H, α, e, hH, he_nonneg, hα, he, h_sum⟩ := hy
  obtain ⟨H', α', e', hH', he_nonneg', hα', he', h_sum'⟩ := hy'
  -- Multiply the two multipliers and add the exponents at every place.
  refine ⟨H * H', α + α', e + e', mul_ne_zero hH hH',
    fun l ↦ add_nonneg (he_nonneg l) (he_nonneg' l), fun σ ↦ ?_, fun ι ↦ ?_, fun T hT ↦ ?_⟩
  · simpa [exp_add] using mul_le_mul (hα σ) (hα' σ) (norm_nonneg _) (exp_nonneg _)
  · calc ‖ι.iso (H * H' * (y * y') ι)‖ = ‖ι.iso (H * y ι)‖ * ‖ι.iso (H' * y' ι)‖ := by
          rw [Pi.mul_apply, mul_mul_mul_comm, map_mul, norm_mul]
      _ ≤ ((ι.prime : ℕ) : ℝ) ^ e ι.prime * ((ι.prime : ℕ) : ℝ) ^ e' ι.prime :=
        mul_le_mul (he ι) (he' ι) (norm_nonneg _) (by positivity)
      _ = ((ι.prime : ℕ) : ℝ) ^ (e + e') ι.prime := (rpow_add (mod_cast ι.prime.prop.pos) _ _).symm
  · simp only [Pi.add_apply, add_mul, sum_add_distrib]
    linarith [h_sum T hT, h_sum' T hT]

/-- Heights add in finite products: if each `y i`, a family indexed by the pairs `ι` of a prime `l`
and an isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`, has height at most `c i`, then the pointwise product of the
`y i` has height at most the sum of the `c i`. -/
lemma prod {κ : Type*} {s : Finset κ} {c : κ → ℝ} {y : κ → PrimePadicIso → ℂ}
    (hy : ∀ i ∈ s, HeightLe (c i) (y i)) : HeightLe (∑ i ∈ s, c i) (∏ i ∈ s, y i) := by
  induction s using cons_induction with
  | empty => exact of_le (e := 0) (by simp) (by simp)
  | cons i s hi ih =>
    simpa using (hy i (mem_cons_self i s)).mul (ih fun j hj ↦ hy j (mem_cons_of_mem hj))

/-- Let `y` be a family of complex numbers indexed by the pairs `ι` of a prime `l` and an
isomorphism `ι.iso : ℂ ≃+* ℚ̄_l`, of height at most `c`; then its pointwise power `y ^ n` has height
at most `n * c`. -/
lemma pow (hy : HeightLe c y) (n : ℕ) : HeightLe (n * c) (y ^ n) := by
  simpa using prod (s := range n) fun _ _ ↦ hy

/-- Let `H` be an algebraic number of degree `n` and `F` an algebraically closed normed field of
characteristic zero with the cardinality of `ℂ`. If `‖ι H‖ ≤ exp b` for all isomorphisms
`ι : ℂ ≃+* F`, then the norm of `H` from `ℚ(H)` to `ℚ` has size at most `exp (n * b)` in `F`. -/
lemma norm_algebraMap_norm_gen_le {F : Type} [NormedField F] [CharZero F] [IsAlgClosed F]
    (hF : Cardinal.mk ℂ = Cardinal.mk F) {H : ℂ} (h_alg : IsAlgebraic ℚ H) {b : ℝ}
    (hb : ∀ ι : ℂ ≃+* F, ‖ι H‖ ≤ exp b) :
    ‖algebraMap ℚ F (Algebra.norm ℚ (AdjoinSimple.gen ℚ H))‖ ≤ exp (finrank ℚ ℚ⟮H⟯ * b) := by
  have : NumberField ℚ⟮H⟯ := { to_finiteDimensional := adjoin.finiteDimensional h_alg.isIntegral }
  -- Each conjugate of `H` in `F` is `ι H` for some isomorphism `ι`.
  have conj_le (σ : ℚ⟮H⟯ →ₐ[ℚ] F) : ‖σ (gen ℚ H)‖ ≤ exp b := by
    obtain ⟨ι, hι⟩ : ∃ ι : ℂ ≃+* F, ∀ a : ℚ⟮H⟯, ι a = σ a :=
      exists_ringEquiv_extend hF ℚ⟮H⟯.val.toRingHom σ Subtype.val_injective σ.injective
    simpa [← hι] using hb ι
  calc _ = ∏ σ : ℚ⟮H⟯ →ₐ[ℚ] F, ‖σ (gen ℚ H)‖ := by rw [norm_eq_prod_embeddings, norm_prod]
    _ ≤ ∏ _σ : ℚ⟮H⟯ →ₐ[ℚ] F, exp b := prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun σ _ ↦ conj_le σ
    _ = exp (finrank ℚ ℚ⟮H⟯ * b) := by simp [exp_nat_mul]

/-- If the constant family `1` has height at most `c`, then `0 ≤ c`. This is a form of the product
formula. -/
lemma nonneg_of_one (h_one : HeightLe c 1) : 0 ≤ c := by
  -- Let `q` be the norm of `H` from `ℚ(H)` to `ℚ` and `n` the degree. At every place `q` is a
  -- product of `n` conjugates of `H`, so `log |q| ≤ n α` and `log |q|_l ≤ n (e l) log l`.
  -- The product formula for `q` then gives `0 ≤ n * c`.
  obtain ⟨H, α, e, hH, -, hα, he, h_sum⟩ := h_one
  have h_padic (l : ℕ) [hl : Fact l.Prime] (ι : ℂ ≃+* PadicAlgCl l) :
      ‖ι H‖ ≤ exp (e l * log l) := by
    simpa [rpow_def_of_pos, hl.out.pos, mul_comm] using he ⟨⟨l, hl.out⟩, ι⟩
  -- `H` is algebraic, because its `2`-adic size is bounded uniformly in `ι`.
  have h_alg : IsAlgebraic ℚ H := isAlgebraic_of_norm_complexToCp_le (by simpa using h_padic 2)
  have : FiniteDimensional ℚ ℚ⟮H⟯ := adjoin.finiteDimensional h_alg.isIntegral
  let q : ℚ := Algebra.norm ℚ (gen ℚ H)
  let n : ℕ := finrank ℚ ℚ⟮H⟯
  have hq : q ≠ 0 := norm_ne_zero_iff.2 (by simpa [Subtype.ext_iff] using hH)
  have h_inf : log q ≤ n * α := by
    rw [← log_abs, log_le_iff_le_exp (by simpa using hq)]
    simpa using norm_algebraMap_norm_gen_le rfl h_alg hα
  have h_fin (l : ℕ) (hl : l.Prime) : log (padicNorm l q) ≤ n * (e l * log l) := by
    have : Fact l.Prime := ⟨hl⟩
    rw [← Padic.eq_padicNorm, log_le_iff_le_exp (norm_pos_iff.2 (Rat.cast_ne_zero.2 hq)),
      ← PadicAlgCl.norm_extends]
    exact norm_algebraMap_norm_gen_le mk_complex_eq_mk_padicAlgCl h_alg (h_padic l)
  -- Sum over the primes below a number `N` that exceeds the numerator and the denominator.
  let N : ℕ := q.num.natAbs + q.den + 1
  refine nonneg_of_mul_nonneg_right ?_ (Nat.cast_pos.2 (finrank_pos : 0 < n))
  calc 0 = log q + ∑ l ∈ range N with l.Prime, log (padicNorm l q) :=
      (log_product_formula (by omega) (by omega)).symm
    _ ≤ n * α + ∑ l ∈ range N with l.Prime, n * (e l * log l) :=
      add_le_add h_inf (sum_le_sum fun l hl ↦ h_fin l (mem_filter.1 hl).2)
    _ = n * (α + ∑ l ∈ range N with l.Prime, e l * log l) := by rw [mul_add, mul_sum]
    _ ≤ n * c := mul_le_mul_of_nonneg_left (h_sum _ fun l hl ↦ (mem_filter.1 hl).2) n.cast_nonneg

/-- A consequence of the product formula: if `z ≠ 0`, the constant family `z` has height at most
`c`, and `|σ z| ≤ exp c'` for all automorphisms `σ` of `ℂ`, then `-c ≤ c'`. -/
lemma neg_le_of_norm_map_le {z : ℂ} (h_height : HeightLe c fun _ : PrimePadicIso ↦ z) (hz : z ≠ 0)
    (h_conj : ∀ σ : ℂ ≃+* ℂ, ‖σ z‖ ≤ exp c') : -c ≤ c' := by
  -- The product of the constant families `z⁻¹` and `z` is the constant family `1`.
  have h_one : HeightLe (c' + c) 1 := by
    simpa [Pi.mul_def, Pi.one_def, hz] using (inv_const hz h_conj).mul h_height
  linarith [h_one.nonneg_of_one]

end HeightLe

end New
