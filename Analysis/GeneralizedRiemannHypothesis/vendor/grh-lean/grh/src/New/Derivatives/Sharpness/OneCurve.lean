import New.Derivatives.FormalGroup.ThetaProducts

/-!
# Derivatives of integral expansions

* `New.exists_monomial_max_norm_coeff`: among the integral series in the `f i`, times a fixed
  series, a monomial of degree at most `|α|` has the largest coefficient at `α`.
* `New.CMLattice.katz_divisibility_limit`: for every `n` some `g ∈ 𝒪[[y]]` has `v(g⁽ⁿ⁾(0)) ≤ γ_p n`,
  where `γ_p = 1 / (p - 1) - ρ_p`.

The least valuation of `g⁽ⁿ⁾(0)` is superadditive in `n`, by the integrality of the group law, and
the formal parameter bounds it when `n` is a power of `q_p`. We work with absolute values, so that
least valuations become greatest norms and sums become products.

## Notation

* `d` is a prime congruent to `7` mod `8` (`PrimeSevenModEight d`), and a ring homomorphism
  `ιₚ : ℂ →+* ℂ_[p]` is fixed (`PadicPlace p`).
* `C : CMLattice d` is a lattice `Λ` stable under the integers of `ℚ(√-d)`, with a point `t` of
  order two modulo `Λ` and a square root `a₁` of `12 ℘(t)`.
* `y = taylorVia ιₚ C.translatedY` is the Taylor series at `0` of
  `(℘'(z + t) - a₁ (℘(z + t) - ℘(t))) / 2`, carried to `ℂ_p` by the chosen map `ιₚ : ℂ →+* ℂ_[p]`.
* `C.integralSeriesRing` is `𝒪[[y]]`, the power series in `y` over the valuation ring `𝒪` of `ℂ_p`.
* `primeNorm d p` is `q_p`, the norm of a prime of `ℚ(√-d)` above `p`, and `varpiValuation d p` is
  `ρ_p = 1 / (e (q_p - 1))`, with `e` the ramification index; `gammaPrime d p` is the rate
  `γ_p = 1 / (p - 1) - ρ_p`.

## Relation to the literature

At inert primes the rate `γ_p` is that of Katz, Divisibilities, congruences, and Cartier duality.
-/

section LargestCoefficient

open Finset MvPowerSeries IsUltrametricDist Finsupp

namespace New

variable {p : ℕ} [Fact p.Prime] {I X : Type} [Fintype X]

/-- Let the `f i` be finitely many series over `ℂ_p` without constant term (`HasSubst f`), and let
`s` be a series. There is a monomial `∏ f i ^ m i` with `|m| ≤ |α|` such that the coefficient at `α`
of `(∏ f i ^ m i) * s` is at least as large in norm as that of `G(f) * s`, for every series `G` over
the valuation ring of `ℂ_p`; `seriesToCp G` is `G` read over `ℂ_p`. -/
lemma exists_monomial_max_norm_coeff [Fintype I] {f : I → MvPowerSeries X ℂ_[p]} (hf : HasSubst f)
    (s : MvPowerSeries X ℂ_[p]) (α : X →₀ ℕ) :
    ∃ m : I →₀ ℕ, m.degree ≤ α.degree ∧ ∀ G : MvPowerSeries I (valRingCp p),
      ‖coeff α ((seriesToCp G).subst f * s)‖ ≤ ‖coeff α ((∏ i : I, f i ^ m i) * s)‖ := by
  -- Only the monomials of degree at most `|α|` contribute to the coefficient at `α`. Take the one
  -- with the largest contribution; integral combinations are no larger (ultrametric inequality).
  let a (d : I →₀ ℕ) : ℂ_[p] := coeff α ((∏ i : I, f i ^ d i) * s)
  obtain ⟨m, hm_deg, hm_max⟩ : ∃ m ∈ {d : I →₀ ℕ | d.degree ≤ α.degree},
      ∀ d ∈ {d : I →₀ ℕ | d.degree ≤ α.degree}, ‖a d‖ ≤ ‖a m‖ :=
    Set.exists_max_image _ _ (finite_of_degree_le _) ⟨0, by simp⟩
  refine ⟨m, hm_deg, fun G ↦ ?_⟩
  have h_trunc (x : MvPowerSeries X ℂ_[p]) :
      (truncTotal (α.degree + 1) x * truncTotal (α.degree + 1) s).coeff α = coeff α (x * s) :=
    coeff_truncTotal_mul_truncTotal_eq_coeff_mul x s α.degree.lt_add_one
  -- As the `f i` have no constant term, `G` may be cut down to its terms of degree `≤ |α|`.
  have h_sum : coeff α ((seriesToCp G).subst f * s) =
      ∑ d ∈ (finite_of_degree_lt (α.degree + 1)).toFinset, coeff d (seriesToCp G) * a d := by
    rw [← h_trunc, truncTotal_subst_eq_truncTotal_truncTotal_subst
      fun i ↦ (hf.const_coeff i).eq_zero, h_trunc]
    simp [a, subst_coe, truncTotal, truncFinset, Finset.sum_mul, MvPolynomial.aeval_monomial,
      Finsupp.prod_pow, ← Algebra.smul_def]
  rw [h_sum]
  refine norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d hd ↦ ?_
  have hd_deg : d.degree ≤ α.degree := by simpa [Nat.lt_succ_iff] using hd
  have h_coeff : ‖coeff d (seriesToCp G)‖ ≤ 1 := (coeff d G).property
  simpa only [one_mul] using norm_mul_le_of_le h_coeff (hm_max d hd_deg)

end New

end LargestCoefficient

open Nat PowerSeries

namespace New

/-- Let `0 < b ≤ 1`, and let `c` be a submultiplicative sequence in `[0, 1]` with `c 0 = 1`. If
`b ^ q ≤ c q` for arbitrarily large `q`, then `b ^ n ≤ c n` for all `n` (a form of Fekete's
lemma). -/
lemma pow_le_of_submultiplicative {c : ℕ → ℝ} {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ 1)
    (hc_zero : c 0 = 1) (hc_nonneg : ∀ n : ℕ, 0 ≤ c n) (hc_le : ∀ n : ℕ, c n ≤ 1)
    (hc_add : ∀ m n : ℕ, c (m + n) ≤ c m * c n) (h_large : ∀ M : ℕ, ∃ q ≥ M, b ^ q ≤ c q)
    (n : ℕ) : b ^ n ≤ c n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [hc_zero]
  have hc_mul (k : ℕ) : c (n * k) ≤ c n ^ k := by
    induction k with
    | zero => simp [hc_zero]
    | succ k ih => grw [mul_add_one, hc_add, pow_succ, mul_le_mul_of_nonneg_right ih (hc_nonneg n)]
  -- Write `q = n * (q / n) + q % n`.
  have h_div (q : ℕ) (hq : b ^ q ≤ c q) : b ^ n * (b ^ n) ^ (q / n) ≤ c n ^ (q / n) :=
    calc b ^ n * (b ^ n) ^ (q / n) = b ^ (n * (q / n + 1)) := by ring
      _ ≤ b ^ q := pow_le_pow_of_le_one hb_pos.le hb_le (Nat.lt_mul_div_succ q hn).le
      _ ≤ c (n * (q / n) + q % n) := by rwa [Nat.div_add_mod]
      _ ≤ c (n * (q / n)) * c (q % n) := hc_add _ _
      _ ≤ c (n * (q / n)) := mul_le_of_le_one_right (hc_nonneg _) (hc_le _)
      _ ≤ c n ^ (q / n) := hc_mul _
  -- If `c n / b ^ n` were less than `1`, its powers would fall below `b ^ n` as `q → ∞`.
  by_contra! h_lt
  have hbn : 0 < b ^ n := pow_pos hb_pos n
  have h_ratio : c n / b ^ n < 1 := (div_lt_one hbn).2 h_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hbn h_ratio
  obtain ⟨q, hq_ge, hq⟩ := h_large (k * n)
  refine hk.not_ge ?_
  calc b ^ n ≤ (c n / b ^ n) ^ (q / n) := by
        rw [div_pow, le_div_iff₀ (pow_pos hbn _)]
        exact h_div q hq
    _ ≤ (c n / b ^ n) ^ k := pow_le_pow_of_le_one (div_nonneg (hc_nonneg n) hbn.le) h_ratio.le
        ((Nat.le_div_iff_mul_le hn).2 hq_ge)

variable {p : ℕ} [Fact p.Prime]

/-- Legendre's bound `v((n + 1)!) ≤ n / (p - 1)`, for the norm of `ℂ_p`. -/
lemma rpow_pow_le_norm_factorial_succ (n : ℕ) :
    ((p : ℝ) ^ (-(1 / (p - 1)) : ℝ)) ^ n ≤ ‖((n + 1)! : ℂ_[p])‖ := by
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have h_legendre : ((p : ℝ) - 1) * padicValNat p (n + 1)! ≤ n := by
    rw [← Nat.cast_pred (Fact.out : p.Prime).pos]
    exact mod_cast Nat.le_of_lt_succ
      (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p n.succ_ne_zero)
  calc ((p : ℝ) ^ (-(1 / (p - 1)) : ℝ)) ^ n = (p : ℝ) ^ (-(n / (p - 1)) : ℝ) := by
        rw [← Real.rpow_mul_natCast (by positivity), neg_mul, one_div_mul_eq_div]
    _ ≤ (p : ℝ) ^ (-(padicValNat p (n + 1)! : ℝ)) := Real.rpow_le_rpow_of_exponent_le hp.le
      (neg_le_neg ((le_div_iff₀' (sub_pos.2 hp)).2 h_legendre))
    _ = ‖((n + 1)! : ℂ_[p])‖ := by
        simp [norm_natCast_eq_inv_pow_padicValNat, factorial_ne_zero, Real.rpow_neg]

/-- Differentiating `g(z₀ + z₁)` `m` times in `z₀` and `n` times in `z₁` at `0` gives
`g⁽ᵐ⁺ⁿ⁾(0)`. Here `linearSeries ![1, 1]` is the linear form `z₀ + z₁`. -/
lemma factorial_mul_coeff_subst_add (g : ℂ_[p]⟦X⟧) (m n : ℕ) :
    m ! * n ! * MvPowerSeries.coeff (.single 0 m + .single 1 n) (g.subst (linearSeries ![1, 1])) =
      (m + n)! * coeff (m + n) g := by
  simp [coeff_subst_linearSeries, factorial_ne_zero, mul_div_cancel₀]

/-- The coefficient of `z₀ ^ m z₁ ^ n` in `g(z₀) h(z₁)` is the product of the `m`-th coefficient
of `g` and the `n`-th coefficient of `h`. Here `linearSeries ![1, 0]` and `linearSeries ![0, 1]` are
the linear forms `z₀` and `z₁`. -/
lemma coeff_subst_mul_subst (g h : ℂ_[p]⟦X⟧) (m n : ℕ) :
    MvPowerSeries.coeff (.single 0 m + .single 1 n)
      (g.subst (linearSeries ![1, 0]) * h.subst (linearSeries ![0, 1])) =
      coeff m g * coeff n h := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (.single 0 m, .single 1 n) (by simp)]
  · simp [coeff_subst_linearSeries, factorial_ne_zero]
  · -- In any other term `z₁` occurs in the first factor or `z₀` in the second.
    rintro ⟨a, b⟩ h_mem h_ne
    have h_add : a 0 + b 0 = m ∧ a 1 + b 1 = n := by simpa [Finsupp.ext_iff] using h_mem
    have h_not : ¬(a 0 = m ∧ a 1 = 0 ∧ b 0 = 0 ∧ b 1 = n) := by simpa [Finsupp.ext_iff] using h_ne
    obtain ha | hb : a 1 ≠ 0 ∨ b 0 ≠ 0 := by omega
    · simp [coeff_subst_linearSeries, ha]
    · simp [coeff_subst_linearSeries, hb]

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) [PadicPlace p]

/-- The greatest norm of `g⁽ⁿ⁾(0) = n! · coeff n g` for `g` in `𝒪[[y]] = C.integralSeriesRing`; it
is `p ^ (-v)` for the least valuation `v` of these derivatives. -/
noncomputable def maxDerivNorm (n : ℕ) : ℝ :=
  sSup ((fun g : ℂ_[p]⟦X⟧ ↦ ‖n ! * coeff n g‖) '' C.integralSeriesRing)

/-- Among the `g` in `C.integralSeriesRing`, the power series in `y` over the valuation ring of
`ℂ_p`, the greatest norm of `g⁽ⁿ⁾(0) = n! · coeff n g` is attained by a power of `y`. -/
lemma exists_isGreatest_norm_deriv (n : ℕ) : ∃ i : ℕ, IsGreatest
    ((fun g : ℂ_[p]⟦X⟧ ↦ ‖n ! * coeff n g‖) '' C.integralSeriesRing)
    ‖n ! * coeff n (taylorVia ιₚ C.translatedY ^ i)‖ := by
  obtain ⟨i, h_max⟩ : ∃ i : ℕ, ∀ g ∈ C.integralSeriesRing,
      ‖coeff n g‖ ≤ ‖coeff n (taylorVia ιₚ C.translatedY ^ i)‖ := by
    have hy : HasSubst (taylorVia ιₚ C.translatedY) := .of_constantCoeff_zero' (by simp)
    obtain ⟨e, -, he⟩ := exists_monomial_max_norm_coeff hy.const 1 (.single () n)
    refine ⟨e (), fun g hg ↦ ?_⟩
    obtain ⟨G, rfl⟩ := C.mem_integralSeriesRing.1 hg
    simpa [PowerSeries.subst, PowerSeries.coeff] using he G
  refine ⟨i, Set.mem_image_of_mem _ (pow_mem C.isSeriesGenerator_translatedY.generator_mem i),
    Set.forall_mem_image.2 fun g hg ↦ ?_⟩
  simpa [norm_mul] using mul_le_mul_of_nonneg_left (h_max g hg) (norm_nonneg _)

/-- The greatest norm `C.maxDerivNorm n` of `g⁽ⁿ⁾(0) = n! · coeff n g` is attained by some `g` in
`𝒪[[y]] = C.integralSeriesRing`. -/
lemma exists_norm_deriv_eq_maxDerivNorm (n : ℕ) :
    ∃ g ∈ C.integralSeriesRing, ‖n ! * coeff n g‖ = C.maxDerivNorm (p := p) n :=
  (C.exists_isGreatest_norm_deriv n).elim fun _i hi ↦ hi.csSup_mem

variable {C} in
/-- For `g` in `𝒪[[y]] = C.integralSeriesRing`, the norm of `g⁽ⁿ⁾(0) = n! · coeff n g` is at most
`C.maxDerivNorm n`. -/
lemma norm_deriv_le_maxDerivNorm {g : ℂ_[p]⟦X⟧} (hg : g ∈ C.integralSeriesRing) (n : ℕ) :
    ‖n ! * coeff n g‖ ≤ C.maxDerivNorm n :=
  (C.exists_isGreatest_norm_deriv n).elim fun _i hi ↦
    le_csSup hi.bddAbove (Set.mem_image_of_mem _ hg)

lemma maxDerivNorm_nonneg (n : ℕ) : 0 ≤ C.maxDerivNorm (p := p) n :=
  (norm_nonneg _).trans (norm_deriv_le_maxDerivNorm (zero_mem C.integralSeriesRing) n)

variable [PrimeSevenModEight d]

variable {C} in
/-- If `g` lies in `C.integralSeriesRing`, the power series in `y` over the valuation ring of `ℂ_p`,
then `g⁽ⁿ⁾(0) = n! · coeff n g` has norm at most `1`, as this ring is stable under
differentiation. -/
lemma norm_deriv_le_one {g : ℂ_[p]⟦X⟧} (hg : g ∈ C.integralSeriesRing) (n : ℕ) :
    ‖n ! * coeff n g‖ ≤ 1 := by
  induction n generalizing g with
  | zero =>
    simpa using (C.isSeriesGenerator_translatedY.norm_constantCoeff_le_one_and_norm_coeff_one_le_one
      hg).1
  | succ n ih =>
    have h_deriv : ((n + 1)! : ℂ_[p]) * coeff (n + 1) g = n ! * coeff n (d⁄dX g) := by
      simp [coeff_derivative, factorial_succ, mul_assoc, mul_comm]
    simpa [h_deriv] using ih (C.derivative_mem_integralSeriesRing hg)

lemma maxDerivNorm_le_one (n : ℕ) : C.maxDerivNorm (p := p) n ≤ 1 :=
  (C.exists_norm_deriv_eq_maxDerivNorm n).elim fun _g ⟨hg, h_eq⟩ ↦
    h_eq.ge.trans (norm_deriv_le_one hg n)

/-- The greatest norm `C.maxDerivNorm 0` of `g(0)`, for `g` in `𝒪[[y]] = C.integralSeriesRing`, is
`1`, attained by the series `1`. -/
lemma maxDerivNorm_zero : C.maxDerivNorm (p := p) 0 = 1 :=
  (C.maxDerivNorm_le_one 0).antisymm (by simpa using norm_deriv_le_maxDerivNorm (one_mem _) 0)

omit [PrimeSevenModEight d] in
/-- Let `μ_i z = linearSeries (μ i)` be the linear form with coefficients `μ i`. For some monomial
`∏ y(μ_i z) ^ e i`, the norm of its coefficient at `α` bounds that of every element of
`C.multiSeriesRing μ`, the ring of power series in the `y(μ_i z)` over the valuation ring of
`ℂ_p`. -/
lemma exists_norm_coeff_le_norm_coeff_prod_pow {I σ : Type} [Fintype I] [Fintype σ]
    (μ : I → σ → ℂ_[p]) (α : σ →₀ ℕ) : ∃ e : I → ℕ, ∀ g ∈ C.multiSeriesRing μ,
    ‖MvPowerSeries.coeff α g‖ ≤ ‖MvPowerSeries.coeff α
      (∏ i : I, (taylorVia ιₚ C.translatedY).subst (linearSeries (μ i)) ^ e i)‖ := by
  obtain ⟨e, -, he⟩ := exists_monomial_max_norm_coeff (C.hasSubst_translatedY_subst μ) 1 α
  refine ⟨e, fun g hg ↦ ?_⟩
  obtain ⟨G, rfl⟩ := C.mem_multiSeriesRing_iff.1 hg
  simpa only [mul_one] using he G

/-- Substituting `linearSeries ![1, 1]` replaces `z` by `z₀ + z₁`. The coefficient of
`z₀ ^ m z₁ ^ n` in `y(z₀ + z₁) ^ j` has norm at most that of `coeff m (y ^ a) * coeff n (y ^ b)` for
some `a` and `b`. -/
lemma exists_norm_coeff_subst_add_le (j m n : ℕ) : ∃ a b : ℕ,
    ‖MvPowerSeries.coeff (.single 0 m + .single 1 n)
      ((taylorVia ιₚ C.translatedY ^ j).subst (linearSeries ![(1 : ℂ_[p]), 1]))‖ ≤
      ‖coeff m (taylorVia ιₚ C.translatedY ^ a) * coeff n (taylorVia ιₚ C.translatedY ^ b)‖ := by
  set y : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedY
  have h_mem : (y ^ j).subst (linearSeries ![(1 : ℂ_[p]), 1]) ∈ C.multiSeriesRing
      ![![1, 0], ![0, 1]] := by
    rw [subst_pow (by simp), show (![1, 1] : Fin 2 → ℂ_[p]) = 1 by simp [funext_iff]]
    exact pow_mem C.translatedY_add_mem_multiSeriesRing j
  obtain ⟨e, he⟩ : ∃ e : Fin 2 → ℕ, ∀ g ∈ C.multiSeriesRing ![![1, 0], ![0, 1]],
      ‖MvPowerSeries.coeff (.single 0 m + .single 1 n) g‖ ≤
        ‖MvPowerSeries.coeff (.single 0 m + .single 1 n) (∏ i : Fin 2,
          y.subst (linearSeries (![![(1 : ℂ_[p]), 0], ![0, 1]] i)) ^ e i)‖ :=
    C.exists_norm_coeff_le_norm_coeff_prod_pow _ _
  refine ⟨e 0, e 1, (he _ h_mem).trans_eq ?_⟩
  simp [Fin.prod_univ_two, ← subst_pow, coeff_subst_mul_subst]

/-- The greatest norm `C.maxDerivNorm n` of `g⁽ⁿ⁾(0)`, for `g` a power series in `y` over the
valuation ring of `ℂ_p`, is submultiplicative in `n`: the least valuation is superadditive. -/
lemma maxDerivNorm_add_le (m n : ℕ) :
    C.maxDerivNorm (p := p) (m + n) ≤ C.maxDerivNorm (p := p) m * C.maxDerivNorm (p := p) n := by
  -- Differentiate `y(z₀ + z₁) ^ j`, an integral series in `y(z₀)` and `y(z₁)`, `m` times in `z₀`
  -- and `n` times in `z₁`.
  let y : ℂ_[p]⟦X⟧ := taylorVia ιₚ C.translatedY
  have hy : y ∈ C.integralSeriesRing := C.isSeriesGenerator_translatedY.generator_mem
  obtain ⟨j, hj⟩ := C.exists_isGreatest_norm_deriv (p := p) (m + n)
  obtain ⟨a, b, h_coeff⟩ := C.exists_norm_coeff_subst_add_le (p := p) j m n
  calc C.maxDerivNorm (m + n) = ‖(m + n)! * coeff (m + n) (y ^ j)‖ := hj.csSup_eq
    _ = ‖(m ! * n ! : ℂ_[p])‖ * ‖MvPowerSeries.coeff (.single 0 m + .single 1 n)
          ((y ^ j).subst (linearSeries ![(1 : ℂ_[p]), 1]))‖ := by
      rw [← factorial_mul_coeff_subst_add, norm_mul]
    _ ≤ ‖(m ! * n ! : ℂ_[p])‖ * ‖coeff m (y ^ a) * coeff n (y ^ b)‖ := by gcongr
    _ = ‖m ! * coeff m (y ^ a)‖ * ‖n ! * coeff n (y ^ b)‖ := by simp [mul_mul_mul_comm]
    _ ≤ C.maxDerivNorm m * C.maxDerivNorm n :=
      mul_le_mul (norm_deriv_le_maxDerivNorm (pow_mem hy a) m)
        (norm_deriv_le_maxDerivNorm (pow_mem hy b) n) (norm_nonneg _) (C.maxDerivNorm_nonneg m)

/-- Let `π_p` be `√-d` if `p = d` and `p` otherwise, and let `piPrimeInt d` be its image under the
map `ιₚ : ℂ →+* ℂ_[p]` of `PadicPlace p`, an integer of norm less than `1`. An integer of `ℂ_p`
that is `1` modulo `piPrimeInt d` has norm `1`. -/
lemma norm_eq_one_of_piPrimeInt_dvd_sub_one {x : valRingCp p} (hx : piPrimeInt d ∣ x - 1) :
    ‖(x : ℂ_[p])‖ = 1 := by
  obtain ⟨c, hc⟩ := hx
  set a : ℂ_[p] := ((piPrimeInt d * c : valRingCp p) : ℂ_[p]) with ha
  have h_small : ‖a‖ < ‖(1 : ℂ_[p])‖ := by
    rw [ha, Subring.coe_mul, norm_mul, norm_one]
    exact (mul_le_of_le_one_right (norm_nonneg _) c.property).trans_lt (norm_piPrime_lt_one d)
  calc ‖(x : ℂ_[p])‖ = ‖a + 1‖ := by rw [eq_add_of_sub_eq hc, Subring.coe_add, Subring.coe_one]
    _ = max ‖a‖ ‖(1 : ℂ_[p])‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_small.ne
    _ = 1 := by rw [max_eq_right h_small.le, norm_one]

/-- Let `q = primeNorm d p` be the norm of a prime of `ℚ(√-d)` above `p`. If `n + 1` is a power of
`q`, then the coefficient of `z ^ (n + 1)` in `C.formalParam`, the part of `y` in degrees `≡ 1` mod
`q - 1`, has valuation `-n ρ_p`. -/
lemma norm_coeff_formalParam_of_eq_primeNorm_pow {n j : ℕ} (hn : n + 1 = primeNorm d p ^ j) :
    ‖coeff (n + 1) C.formalParam‖ = ((p : ℝ) ^ varpiValuation d p) ^ n := by
  -- Take `ϖ` of valuation `ρ_p`. The series `Y(z) = C.formalParam(ϖ z) / ϖ` is integral, and its
  -- coefficient of `z ^ (n + 1)` is `1` modulo `piPrimeInt d`, which has norm less than `1`.
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  obtain ⟨ϖ, Y, hϖ, h_scale, -, h_coeff⟩ := C.exists_scaled_formalParam
  have h_dvd : piPrimeInt d ∣ coeff (n + 1) Y - 1 := by
    simpa only [ite_eq_left (⟨j, hn⟩ : ∃ i : ℕ, n + 1 = primeNorm d p ^ i)] using h_coeff (n + 1)
  have h_eq : ϖ ^ (n + 1) * coeff (n + 1) C.formalParam = ϖ * (coeff (n + 1) Y : valRingCp p) := by
    rw [← coeff_rescale, h_scale, coeff_smul, coeff_seriesToCp, smul_eq_mul]
  have h_norm : ‖ϖ‖ * (‖ϖ‖ ^ n * ‖coeff (n + 1) C.formalParam‖) = ‖ϖ‖ * 1 := by
    rw [← norm_eq_one_of_piPrimeInt_dvd_sub_one h_dvd, ← norm_mul ϖ, ← h_eq, norm_mul, norm_pow]
    ring
  calc ‖coeff (n + 1) C.formalParam‖ = (‖ϖ‖ ^ n)⁻¹ := eq_inv_of_mul_eq_one_right
        (mul_left_cancel₀ (hϖ.trans_ne (Real.rpow_pos_of_pos hp _).ne') h_norm)
    _ = ((p : ℝ) ^ varpiValuation d p) ^ n := by rw [hϖ, Real.rpow_neg hp.le, inv_pow, inv_inv]

/-- Let `q = primeNorm d p` be the norm of a prime of `ℚ(√-d)` above `p`. If `n + 1` is a power of
`q`, then the greatest norm `C.maxDerivNorm (n + 1)` of `g⁽ⁿ⁺¹⁾(0)`, for `g` a power series in `y`
over the valuation ring of `ℂ_p`, is at least `p ^ (-n γ_p)`. -/
lemma pow_le_maxDerivNorm_of_eq_primeNorm_pow {n j : ℕ} (hn : n + 1 = primeNorm d p ^ j) :
    ((p : ℝ) ^ (-gammaPrime d p)) ^ n ≤ C.maxDerivNorm (p := p) (n + 1) := by
  have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
  calc ((p : ℝ) ^ (-gammaPrime d p)) ^ n
      = ((p : ℝ) ^ (-(1 / (p - 1)) : ℝ)) ^ n * ((p : ℝ) ^ varpiValuation d p) ^ n := by
        rw [← mul_pow, ← Real.rpow_add hp, neg_add_eq_sub, gammaPrime, neg_sub]
    _ ≤ ‖(n + 1)! * coeff (n + 1) C.formalParam‖ := by
        grw [norm_mul, C.norm_coeff_formalParam_of_eq_primeNorm_pow hn,
          rpow_pow_le_norm_factorial_succ]
    _ ≤ C.maxDerivNorm (n + 1) :=
        norm_deriv_le_maxDerivNorm C.isSeriesGenerator_formalParam.generator_mem _

/-- The limit on Katz's divisibility of derivatives: no divisibility better than the rate `γ_p`
holds for all series.

For every `n` there is `f` in `C.integralSeriesRing`, the power series in `y` over the valuation
ring of `ℂ_p`, whose derivative `f⁽ⁿ⁾(0) = n! · coeff n f` has norm at least `p ^ (-n γ_p)`. -/
lemma katz_divisibility_limit (n : ℕ) : ∃ f ∈ C.integralSeriesRing (p := p),
    ((p : ℝ) ^ (-gammaPrime d p)) ^ n ≤ ‖n ! * coeff n f‖ := by
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  -- With `b = p ^ (-γ_p)`, the bound `b ^ q ≤ C.maxDerivNorm q` holds at the powers of
  -- `primeNorm d p`, and submultiplicativity carries it to every `n`.
  set b : ℝ := p ^ (-gammaPrime d p)
  have hb_pos : 0 < b := by positivity
  have hb_le : b ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp.le (neg_nonpos.2 (gammaPrime_nonneg d p))
  have h_large (M : ℕ) : ∃ q ≥ M, b ^ q ≤ C.maxDerivNorm q := by
    have hM : M < primeNorm d p ^ M := Nat.lt_pow_self (one_lt_primeNorm d p)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 1 = primeNorm d p ^ M := Nat.exists_add_one_eq.2 hM.pos
    refine ⟨m + 1, hM.le.trans hm.ge, ?_⟩
    calc b ^ (m + 1) ≤ b ^ m := pow_le_pow_of_le_one hb_pos.le hb_le m.le_succ
      _ ≤ C.maxDerivNorm (m + 1) := C.pow_le_maxDerivNorm_of_eq_primeNorm_pow hm
  have h_le : b ^ n ≤ C.maxDerivNorm n :=
    pow_le_of_submultiplicative hb_pos hb_le C.maxDerivNorm_zero C.maxDerivNorm_nonneg
      C.maxDerivNorm_le_one C.maxDerivNorm_add_le h_large n
  obtain ⟨f, hf, h_eq⟩ : ∃ f ∈ C.integralSeriesRing (p := p),
      ‖n ! * coeff n f‖ = C.maxDerivNorm n := C.exists_norm_deriv_eq_maxDerivNorm n
  exact ⟨f, hf, h_le.trans h_eq.ge⟩

end CMLattice

end New
