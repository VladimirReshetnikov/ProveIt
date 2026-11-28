import Lib.CM.FormalGroup.IntegralParameter
import Lib.General.Algebra.AbsIntegrallyClosed

/-!
# Integrality of exponentials, logarithms and roots of power series

The file first shows that, over an algebraically closed valued field, there is an integral point at
which finitely many given polynomials are at least as large as all their coefficients. It then
bounds the coefficients of power series built by exponentials, logarithms and roots over `ℂ_[p]`.
There `v` denotes the additive valuation with `v(p) = 1`, so that `‖c‖ = p ^ (-v(c))`, and `v(g)`
for a series `g` is the infimum of the valuations of its coefficients. `expSubst g` is `exp ℂ_[p]`
substituted at `g`, written `exp g`, and `logOf f` is `log ℂ_[p]`, the series of `log (1 + X)`,
substituted at `f - 1`, written `log f`. For `g(0) = 0` it proves that `exp g` is integral when
`v(g) ≥ 1 / (p - 1)`, gives a divisibility criterion for `exp g - 1`, and shows that `exp g` lies in
a ring `𝒪[[T]]` if its `m`-th power does, for `m` prime to `p`.

The imported notions used in the statements are these.

* `seriesToCp` is the inclusion of the series with integral coefficients into all series over
  `ℂ_[p]`. Its range consists of the series whose coefficients have norm at most `1`.
* `IsSeriesGenerator B T` says that `T = X + ⋯` and that `B` is the ring of all integral series in
  `T`, written `B = 𝒪[[T]]`.

## Main definitions and results

* `New.exists_val_coeff_le_val_eval`: at one integral point, finitely many polynomials are at least
  as large as all their coefficients.
* `New.norm_coeff_expSubst_le_one`: `exp g` is integral if `g(0) = 0` and `v(g) ≥ 1 / (p - 1)`,
  degree by degree.
* `New.norm_coeff_expSubst_sub_one_le`, `New.IsSeriesGenerator.mem_of_expSubst_smul_eq`: for
  `v(c) ≥ 1 / (p - 1)` and `g(0) = 0`, the number `c` divides `exp g - 1` if it divides `g`, and,
  for `c ≠ 0` and in a ring `𝒪[[T]]`, `c` divides `g` if it divides `exp g - 1`.
* `New.IsSeriesGenerator.expSubst_mem_of_pow_mem`: if `g(0) = 0` and `(exp g) ^ m ∈ 𝒪[[T]]` with `m`
  prime to `p`, then `exp g ∈ 𝒪[[T]]`.

## Relation to the literature

Known result: the Gauss norm equals the supremum norm on the unit polydisc over an algebraically
closed valued field. Source: Bosch, Güntzer and Remmert, *Non-Archimedean Analysis*.

Known result: the integrality of the `p`-adic exponential and logarithm on series of large enough
valuation, and of the binomial series with exponent in `ℤ_p`.
-/

/-!
## A general integral point

Each polynomial is a constant times a polynomial with nonzero reduction. As the residue field is
infinite, there is a point at which none of the reductions vanishes.
-/

section IntegralityPrinciple

open Finset IsLocalRing MvPolynomial New.Variety.IsAbsIntegrallyClosed

/-- Over an algebraically closed valued field there is an integral point at which each of finitely
many polynomials takes a value at least as large as all its coefficients. -/
lemma New.exists_val_coeff_le_val_eval {K σ : Type*} {n : ℕ} [Field K] [IsAlgClosed K]
    (v : Valuation K NNReal) (f : Fin n → MvPolynomial σ K) :
    ∃ y : σ → v.valuationSubring,
      ∀ (i : Fin n) (m : σ →₀ ℕ),
        v ((f i).coeff m) ≤ v (eval (algebraMap v.valuationSubring K ∘ y) (f i)) := by
  classical
  -- Write `f i = c i • g i` with `g i` over `V` of nonzero reduction. The residue field is
  -- algebraically closed, hence infinite, so at some `y` no reduction vanishes: each `g i` takes
  -- a unit value at `y`.
  set V : ValuationSubring K := v.valuationSubring
  have h_scale (q : MvPolynomial σ K) :
      ∃ (c : K) (g : MvPolynomial σ V), map (residue V) g ≠ 0 ∧ q = c • g.map (algebraMap V K) := by
    -- A coefficient `q.coeff k` of largest valuation divides the others, with quotients `w m`.
    obtain ⟨k, hk⟩ : ∃ k : σ →₀ ℕ, ∀ m ∈ q.support,
        V.valuation (q.coeff m) ≤ V.valuation (q.coeff k) :=
      Set.exists_upper_bound_image q.support (V.valuation ∘ q.coeff) (Set.toFinite _)
    have h_dvd : ∀ m ∈ q.support, ∃ w : V, (w : K) * q.coeff k = q.coeff m :=
      fun m hm ↦ (V.valuation_le_iff _ _).1 (hk m hm)
    choose! w hw using h_dvd
    let g : MvPolynomial σ V := monomial k 1 + ∑ d ∈ q.support.erase k, monomial d (w d)
    have h_coeff (d : σ →₀ ℕ) :
        g.coeff d = if k = d then 1 else if d ∈ q.support then w d else 0 := by
      obtain rfl | hkd := eq_or_ne k d <;> simp [g, coeff_monomial, eq_comm, *]
    refine ⟨q.coeff k, g, ne_of_apply_ne (·.coeff k) (by simp [coeff_map, h_coeff]), ?_⟩
    ext d
    rw [coeff_smul, coeff_map, h_coeff]
    split_ifs with hkd hd
    · simp [hkd]
    · simp [← hw d hd, mul_comm]
    · simpa using hd
  -- Now `f i = c i • g i`, and the reduction of each `g i` is not zero.
  choose c g hg hfg using fun i : Fin n ↦ h_scale (f i)
  have : IsAlgClosed (ResidueField V) :=
    ((of_isIntegrallyClosedIn K).of_surjective residue_surjective).isAlgClosed
  -- Over an infinite field a nonzero polynomial has a nonzero value.
  obtain ⟨y₀, hy₀⟩ :
      ∃ y₀ : σ → ResidueField V, eval y₀ (∏ i : Fin n, map (residue V) (g i)) ≠ eval y₀ 0 :=
    not_forall.1 fun h_eq ↦ prod_ne_zero_iff.2 (fun i _ ↦ hg i) (MvPolynomial.funext h_eq)
  obtain ⟨y, rfl⟩ : ∃ y : σ → V, residue V ∘ y = y₀ := residue_surjective.comp_left y₀
  have h_unit (i : Fin n) : IsUnit (eval y (g i)) := by
    rw [map_prod, map_zero, prod_ne_zero_iff] at hy₀
    rw [← residue_ne_zero_iff_isUnit]
    simpa [eval_map, ← eval₂_comp] using hy₀ i (mem_univ i)
  refine ⟨y, fun i m ↦ ?_⟩
  -- The factor `c i` is common, and the unit `eval y (g i)` divides every coefficient of `g i`.
  have h_le : v (algebraMap V K ((g i).coeff m)) ≤ v (algebraMap V K (eval y (g i))) :=
    (Valuation.integer.integers v).le_of_dvd (h_unit i).dvd
  grw [hfg i, coeff_smul, coeff_map, smul_eval, eval_map, ← eval₂_comp, smul_eq_mul, map_mul,
    map_mul, h_le]

end IntegralityPrinciple

/-!
## Bounds for exponentials, logarithms and roots

The bounds come from Legendre's formula for `v(j!)` and from the binomial series over `ℤ_p`.
-/

section SeriesBounds

open PowerSeries IsUltrametricDist

namespace New
variable {p : ℕ} [Fact p.Prime]

/-- If `g(0) = 0`, then `(exp g)' = exp g * g'`, where `exp g` is `expSubst g`. -/
lemma derivative_expSubst {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0) :
    d⁄dX (expSubst g) = expSubst g * d⁄dX g := by
  rw [expSubst, derivative_subst (.of_constantCoeff_zero' hg_zero), derivative_exp]

/-- If `g(0) = 0`, then `exp g` has constant term `1`. -/
lemma constantCoeff_expSubst {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0) :
    constantCoeff (expSubst g) = 1 :=
  (constantCoeff_subst_eq hg_zero).trans constantCoeff_exp

/-- If `g(0) = 0`, then `s g(X) - g(δ X)` has constant term `0`. -/
lemma constantCoeff_smul_sub_rescale {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0)
    (s δ : ℂ_[p]) : constantCoeff (s • g - rescale δ g) = 0 := by
  simp [constantCoeff_rescale, hg_zero]

/-- The logarithmic derivative: `f (log f)' = f'` if `f(0) = 1`. -/
lemma mul_derivative_logOf {f : ℂ_[p]⟦X⟧} (hf : constantCoeff f = 1) :
    f * d⁄dX (logOf f) = d⁄dX f := by
  have hs : HasSubst (f - 1) := .of_constantCoeff_zero' (by simp [hf])
  have h_geom : (1 + X) * d⁄dX (log ℂ_[p]) = 1 := by
    ext (_ | n) <;> simp [derivative_log, add_mul, coeff_succ_X_mul, pow_succ, coeff_one]
  -- Substitute `X = f - 1` in `(1 + X) log' (1 + X) = 1`.
  have h_subst : f * (d⁄dX (log ℂ_[p])).subst (f - 1) = 1 := by
    simpa [← coe_substAlgHom hs, substAlgHom_X] using congrArg (substAlgHom hs) h_geom
  simp [logOf_eq, derivative_subst hs, ← mul_assoc, h_subst]

/-- If `g(0) = 0`, then `log (exp g) = g`, where `exp g` is `expSubst g`. -/
lemma logOf_expSubst {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0) :
    logOf (expSubst g) = g := by
  have h_one : constantCoeff (expSubst g) = 1 := constantCoeff_expSubst hg_zero
  have h_ne : (expSubst g : ℂ_[p]⟦X⟧) ≠ 0 := fun h ↦ by simp [h] at h_one
  -- The constant terms agree, and so do the derivatives after multiplication by `exp g`.
  refine derivative.ext (mul_left_cancel₀ h_ne ?_) (by rw [constantCoeff_logOf h_one, hg_zero])
  rw [mul_derivative_logOf h_one, derivative_expSubst hg_zero]

/-- If `f(0) = 1`, then `exp (log f) = f`, where `exp` is `expSubst` and `log f` is `logOf f`. -/
lemma expSubst_logOf {f : ℂ_[p]⟦X⟧} (hf : constantCoeff f = 1) : expSubst (logOf f) = f := by
  have h_log : constantCoeff (logOf f) = 0 := constantCoeff_logOf hf
  have h_neg : constantCoeff (-logOf f) = 0 := by simp [h_log]
  -- Both sides are inverse to `exp (-log f)`: the product with `f` has derivative zero.
  have h_mul : expSubst (-logOf f) * f = 1 := by
    refine derivative.ext ?_ (by simp [constantCoeff_expSubst h_neg, hf])
    rw [Derivation.leibniz, derivative_expSubst h_neg, map_neg, derivative_one, smul_eq_mul,
      smul_eq_mul, ← mul_derivative_logOf hf]
    ring
  have h_expSubst : expSubst (logOf f) * expSubst (-logOf f) = 1 := by
    simp [← expSubst_add _ h_log h_neg, expSubst.eq_1 0, subst_zero_eq_C_constantCoeff]
  exact left_inv_eq_right_inv h_expSubst h_mul

section Bounds

/-- Let `g` be a series in any variables and `r ≥ 0`. If the coefficients of `g` in degrees `≤ l`
have norm at most `r`, those of `g ^ j` in these degrees have norm at most `r ^ j`. -/
lemma norm_coeff_pow_le {σ : Type} {g : MvPowerSeries σ ℂ_[p]} {l : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ m : σ →₀ ℕ, m.degree ≤ l → ‖g.coeff m‖ ≤ r) (j : ℕ)
    {m : σ →₀ ℕ} (hm : m.degree ≤ l) : ‖(g ^ j).coeff m‖ ≤ r ^ j := by
  classical
  induction j generalizing m with
  | zero => by_cases hm_zero : m = 0 <;> simp [MvPowerSeries.coeff_one, hm_zero]
  | succ j ih =>
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul]
    refine norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x hx ↦ ?_
    have h_deg : x.1.degree + x.2.degree ≤ l := by
      rwa [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
    grw [norm_mul, ih (m := x.1) (by omega), hg x.2 (by omega)]

/-- Let `g` be a series in any variables with `g(0) = 0`, with coefficients in degrees `≤ l` of
norm at most `r`, where `r ≥ 0`, and let `f = ∑ f_j X ^ j` satisfy `‖f_j‖ r ^ j ≤ s` for all `j`.
Then the coefficients of `f(g)` in degrees `≤ l` have norm at most `s`. -/
lemma norm_coeff_subst_le {σ : Type} {g : MvPowerSeries σ ℂ_[p]} {l : ℕ} {r s : ℝ}
    {f : ℂ_[p]⟦X⟧} (hg_zero : g.constantCoeff = 0) (hr : 0 ≤ r)
    (hg : ∀ m : σ →₀ ℕ, m.degree ≤ l → ‖g.coeff m‖ ≤ r) (hf : ∀ j : ℕ, ‖coeff j f‖ * r ^ j ≤ s)
    {m : σ →₀ ℕ} (hm : m.degree ≤ l) : ‖(f.subst g).coeff m‖ ≤ s := by
  have hs : 0 ≤ s := le_trans (by positivity) (hf 0)
  rw [coeff_subst (.of_constantCoeff_zero hg_zero)]
  -- The norm is ultrametric, so it suffices to bound each term `f_j (g ^ j)_m`.
  refine finsum_induction (‖·‖ ≤ s) (by rwa [norm_zero])
    (fun x y hx hy ↦ (norm_add_le_max x y).trans (max_le hx hy)) fun j ↦ ?_
  rw [smul_eq_mul, norm_mul]
  calc ‖coeff j f‖ * ‖(g ^ j).coeff m‖ ≤ ‖coeff j f‖ * r ^ j := by
        grw [norm_coeff_pow_le hr hg j hm]
    _ ≤ s := hf j

/-- Let `g(0) = 0`. If the coefficients of `g` in degrees `≤ l` have norm at most
`p ^ (-1 / (p - 1))`, that is, valuation at least `1 / (p - 1)`, then `exp g`, written `expSubst g`,
is integral in these degrees.

A consequence of the upper bound `v(j!) ≤ j / (p - 1)` given by Legendre's formula, applied to the
terms `g ^ j / j!` of the exponential series. -/
lemma norm_coeff_expSubst_le_one {σ : Type} {g : MvPowerSeries σ ℂ_[p]}
    (hg_zero : g.constantCoeff = 0) {l : ℕ}
    (hg : ∀ m : σ →₀ ℕ, m.degree ≤ l → ‖g.coeff m‖ ≤ p ^ (-(1 / (p - 1)) : ℝ))
    {m : σ →₀ ℕ} (hm : m.degree ≤ l) : ‖(expSubst g).coeff m‖ ≤ 1 := by
  refine norm_coeff_subst_le hg_zero (by positivity) hg (fun j ↦ ?_) hm
  -- The coefficients of `g ^ j` have valuation at least `j / (p - 1) ≥ v(j!)`.
  have h_fac : ((p : ℝ) ^ (-(1 / (p - 1)) : ℝ)) ^ j ≤ ‖(j.factorial : ℂ_[p])‖ := by
    rw [← Real.rpow_mul_natCast p.cast_nonneg, neg_mul, one_div_mul_eq_div]
    exact rpow_le_norm_factorial
  simpa [coeff_exp, inv_mul_eq_div] using div_le_one_of_le₀ h_fac (norm_nonneg _)

end Bounds

/-- If the coefficients of the series `g` in one variable below the degree `l` have norm at most
`r`, where `r ≥ 0`, those of `g ^ j` below the degree `l` have norm at most `r ^ j`. -/
lemma norm_coeff_pow_le_of_lt {g : ℂ_[p]⟦X⟧} {l : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hg : ∀ n < l, ‖coeff n g‖ ≤ r) (j : ℕ) {n : ℕ} (hn : n < l) : ‖coeff n (g ^ j)‖ ≤ r ^ j := by
  refine norm_coeff_pow_le (l := n) hr (fun m hm ↦ ?_) j (Finsupp.degree_single () n).le
  rw [Finsupp.unique_single m] at hm ⊢
  exact hg _ (by simpa using hm.trans_lt hn)

/-- Let `g` be a series in one variable with `g(0) = 0`, with coefficients below the degree `l`
of norm at most `r`, where `r ≥ 0`, and let `f = ∑ f_j X ^ j` satisfy `‖f_j‖ r ^ j ≤ s` for all
`j`. Then the coefficients of `f(g)` below the degree `l` have norm at most `s`. -/
lemma norm_coeff_subst_le_of_lt {f g : ℂ_[p]⟦X⟧} {l : ℕ} {r s : ℝ}
    (hg_zero : constantCoeff g = 0) (hr : 0 ≤ r) (hg : ∀ n < l, ‖coeff n g‖ ≤ r)
    (hf : ∀ j : ℕ, ‖coeff j f‖ * r ^ j ≤ s) {n : ℕ} (hn : n < l) : ‖coeff n (f.subst g)‖ ≤ s := by
  refine norm_coeff_subst_le (l := n) hg_zero hr (fun m hm ↦ ?_) hf (Finsupp.degree_single () n).le
  rw [Finsupp.unique_single m] at hm ⊢
  exact hg _ (by simpa using hm.trans_lt hn)

/-- A triangular system: let `x = X ^ 2 + ⋯` be integral below the degree `l` and `R` a polynomial.
If the coefficients of `R(x)` below the degree `l` have norm at most `s`, then so do the
coefficients `R_i` of `R` with `2 i < l`. -/
lemma norm_coeff_le_of_aeval {x : ℂ_[p]⟦X⟧} {l : ℕ} {s : ℝ} (h_dvd : X ^ 2 ∣ x)
    (h_two : coeff 2 x = 1) (hx : ∀ n < l, ‖coeff n x‖ ≤ 1) {R : Polynomial ℂ_[p]}
    (hR : ∀ n < l, ‖coeff n (R.aeval x)‖ ≤ s) {i : ℕ} (hi : 2 * i < l) : ‖R.coeff i‖ ≤ s := by
  -- Induction on `i`: in degree `2 i` only the powers `x ^ j` with `j ≤ i` contribute to `R(x)`,
  -- and `x ^ i` has the coefficient `1` there.
  obtain ⟨u, rfl⟩ := h_dvd
  have hu : constantCoeff u = 1 := by simpa [coeff_X_pow_mul'] using h_two
  have hs : HasSubst (X ^ 2 * u) := .of_constantCoeff_zero' (by simp)
  have h_pow (j n : ℕ) :
      coeff n ((X ^ 2 * u) ^ j) = if 2 * j ≤ n then coeff (n - 2 * j) (u ^ j) else 0 := by
    rw [mul_pow, ← pow_mul, coeff_X_pow_mul']
  induction i using Nat.strong_induction_on with | _ i ih => ?_
  have h_lead : coeff (2 * i) ((X ^ 2 * u) ^ i) = 1 := by simp [h_pow i, hu]
  have h_zero (j : ℕ) (hj : i < j) : coeff (2 * i) ((X ^ 2 * u) ^ j) = 0 := by
    rw [h_pow, ite_eq_right (by omega)]
  have h_sum : coeff (2 * i) (R.aeval (X ^ 2 * u)) =
      ∑ j ∈ Finset.range i, R.coeff j * coeff (2 * i) ((X ^ 2 * u) ^ j) + R.coeff i := by
    rw [← subst_coe hs, coeff_subst' hs,
      finsum_eq_sum_of_support_subset (s := Finset.range (i + 1)) _ fun j hj ↦ ?_,
      Finset.sum_range_succ, h_lead]
    · simp
    · by_contra h_not
      exact hj (by simp [h_zero j (by simpa using h_not)])
  have h_lower : ‖∑ j ∈ Finset.range i, R.coeff j * coeff (2 * i) ((X ^ 2 * u) ^ j)‖ ≤ s := by
    refine norm_sum_le_of_forall_le_of_nonneg ((norm_nonneg _).trans (hR _ hi)) fun j hj ↦ ?_
    have hj_lt : j < i := Finset.mem_range.1 hj
    have h_int : ‖coeff (2 * i) ((X ^ 2 * u) ^ j)‖ ≤ 1 :=
      (norm_coeff_pow_le_of_lt zero_le_one hx j hi).trans_eq (one_pow j)
    grw [norm_mul, h_int, mul_one, ih j hj_lt (by omega)]
  rw [eq_sub_of_add_eq' h_sum.symm, sub_eq_add_neg]
  exact (norm_add_le_max _ _).trans (max_le (hR _ hi) (by rwa [norm_neg]))

/-- If `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, then `c ^ j / (j + 1)!` is
integral, as `v((j + 1)!) ≤ j / (p - 1)`. -/
lemma norm_pow_le_norm_factorial_succ {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) (j : ℕ) :
    ‖c‖ ^ j ≤ ‖((j + 1).factorial : ℂ_[p])‖ := by
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  have h_val : (p - 1) * padicValNat p (j + 1).factorial ≤ j :=
    Nat.le_of_lt_succ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p j.succ_ne_zero)
  have h_real : (padicValNat p (j + 1).factorial : ℝ) ≤ j / (p - 1) := by
    rw [le_div_iff₀' (sub_pos.2 hp), ← Nat.cast_pred (Fact.out : p.Prime).pos]
    exact_mod_cast h_val
  calc ‖c‖ ^ j ≤ (p : ℝ) ^ (-(j / (p - 1)) : ℝ) := by
        grw [hc, ← Real.rpow_mul_natCast p.cast_nonneg, neg_mul, one_div_mul_eq_div]
    _ ≤ (p : ℝ) ^ (-(padicValNat p (j + 1).factorial : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp.le (neg_le_neg h_real)
    _ = ‖((j + 1).factorial : ℂ_[p])‖ := by
      simp [norm_natCast_eq_inv_pow_padicValNat (j + 1).factorial_ne_zero, Real.rpow_neg]

/-- If `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, then `c ^ j / (j + 1)` is
integral. -/
lemma norm_pow_le_norm_succ {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) (j : ℕ) :
    ‖c‖ ^ j ≤ ‖((j + 1 : ℕ) : ℂ_[p])‖ := by
  grw [norm_pow_le_norm_factorial_succ hc j, Nat.factorial_succ, Nat.cast_mul, norm_mul,
    norm_natCast_le_one ℂ_[p] j.factorial, mul_one]

/-- Let `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, and `g(0) = 0`. If `c` divides
the coefficients of `g` below the degree `l`, that is, they have norm at most `‖c‖`, then it also
divides those of `exp g - 1`, where `exp g` is `expSubst g`. -/
lemma norm_coeff_expSubst_sub_one_le {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ))
    {g : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0) {l : ℕ} (hg : ∀ n < l, ‖coeff n g‖ ≤ ‖c‖)
    {n : ℕ} (hn : n < l) : ‖coeff n (expSubst g - 1)‖ ≤ ‖c‖ := by
  have hs : HasSubst g := .of_constantCoeff_zero' hg_zero
  have h_subst : expSubst g - 1 = (exp ℂ_[p] - 1).subst g := by
    rw [subst_sub hs, ← coe_substAlgHom hs, map_one, coe_substAlgHom]
  rw [h_subst]
  refine norm_coeff_subst_le_of_lt hg_zero (norm_nonneg c) hg ?_ hn
  rintro (_ | j)
  · simp
  calc ‖coeff (j + 1) (exp ℂ_[p] - 1)‖ * ‖c‖ ^ (j + 1)
      = ‖c‖ ^ j / ‖((j + 1).factorial : ℂ_[p])‖ * ‖c‖ := by
        simp [coeff_one, coeff_exp, pow_succ, div_eq_inv_mul, mul_assoc]
    _ ≤ ‖c‖ := mul_le_of_le_one_left (norm_nonneg c)
      (div_le_one_of_le₀ (norm_pow_le_norm_factorial_succ hc j) (norm_nonneg _))

/-- If `v(c) ≥ 1 / (p - 1)`, that is, `‖c‖ ≤ p ^ (-1 / (p - 1))`, the series `log (1 + c X) / c`
is integral: it lies in the range of `seriesToCp`, the inclusion of the integral series. -/
lemma inv_smul_rescale_log_mem {c : ℂ_[p]} (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) :
    c⁻¹ • rescale c (log ℂ_[p]) ∈ seriesToCp.range := by
  rw [mem_range_seriesToCp]
  rintro (_ | j)
  · simp
  calc ‖coeff (j + 1) (c⁻¹ • rescale c (log ℂ_[p]))‖
      = ‖c‖⁻¹ * ‖c‖ * (‖c‖ ^ j / ‖((j + 1 : ℕ) : ℂ_[p])‖) := by
        simp [coeff_rescale, coeff_log, pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm]
    _ ≤ ‖c‖ ^ j / ‖((j + 1 : ℕ) : ℂ_[p])‖ :=
        mul_le_of_le_one_left (by positivity) (inv_mul_le_one_of_le₀ le_rfl (norm_nonneg c))
    _ ≤ 1 := div_le_one_of_le₀ (norm_pow_le_norm_succ hc j) (norm_nonneg _)

/-- For `m` prime to `p` the series `1 + X` has an `m`-th root with constant term `1` and integral
coefficients (it lies in the range of `seriesToCp`): the binomial series with exponent `1 / m`, as
its coefficients lie in `ℤ_p`. -/
lemma exists_pow_eq_one_add_X {m : ℕ} (hm : p.Coprime m) :
    ∃ b : ℂ_[p]⟦X⟧, b ∈ seriesToCp.range ∧ constantCoeff b = 1 ∧ b ^ m = 1 + X := by
  -- The exponent `r = 1 / m` lies in `ℤ_p`.
  obtain ⟨r, hr⟩ : ∃ r : ℤ_[p], m * r = 1 :=
    (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hm)).exists_right_inv
  let φ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom
  have h_pow (k : ℕ) : binomialSeries ℤ_[p] r ^ k = binomialSeries ℤ_[p] (k * r) := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, Nat.cast_succ, add_one_mul, binomialSeries_add]
  have h_norm (x : ℤ_[p]) : ‖φ x‖ ≤ 1 :=
    (norm_algebraMap' ℂ_[p] (x : ℚ_[p])).trans_le x.norm_le_one
  refine ⟨(binomialSeries ℤ_[p] r).map φ, mem_range_seriesToCp.2 fun n ↦ h_norm _, ?_, ?_⟩
  · simp [← coeff_zero_eq_constantCoeff_apply]
  · simpa [← map_pow, h_pow, hr] using congrArg (map φ) (binomialSeries_nat (A := ℤ_[p]) 1)

/-- Two series with constant term `1` and the same `m`-th power, `m ≠ 0`, are equal. -/
lemma eq_of_pow_eq_pow_of_constantCoeff_eq_one {f g : ℂ_[p]⟦X⟧} {m : ℕ} (hm : m ≠ 0)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h_pow : f ^ m = g ^ m) : f = g := by
  set S : ℂ_[p]⟦X⟧ := ∑ i ∈ Finset.range m, f ^ i * g ^ (m - 1 - i) with hS
  have h_geom : S * (f - g) = 0 := by rw [hS, (Commute.all f g).geom_sum₂_mul, h_pow, sub_self]
  have h_const : constantCoeff S = m := by simp [hS, hf, hg]
  have h_sum_ne : S ≠ 0 := fun h ↦ hm (by simpa [h, eq_comm] using h_const)
  simpa [h_sum_ne, sub_eq_zero] using h_geom

namespace IsSeriesGenerator

/-- Let `B = 𝒪[[T]]` (`IsSeriesGenerator B T`: `T = X + ⋯` and `B` is the ring of all integral
series in `T`), let `f` be a series with integral coefficients (an element of the range of
`seriesToCp`) and `h ∈ B` without constant term. Then `f(h) ∈ B`. -/
lemma subst_mem {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧} (hB : IsSeriesGenerator B T)
    {f h : ℂ_[p]⟦X⟧} (hf : f ∈ seriesToCp.range) (hh : h ∈ B) (hh_zero : constantCoeff h = 0) :
    f.subst h ∈ B := by
  -- With `Z` inverse to `T`, a series lies in `B` if and only if its value at `Z` is integral.
  obtain ⟨Z, hZ_zero, -, -, h_mem⟩ : ∃ Z : ℂ_[p]⟦X⟧, constantCoeff Z = 0 ∧ T.subst Z = X ∧
      Z.subst T = X ∧ ∀ {u : ℂ_[p]⟦X⟧}, u ∈ B ↔ u.subst Z ∈ seriesToCp.range :=
    hB.exists_subst_inverse
  have hZh_zero : constantCoeff (h.subst Z) = 0 := (constantCoeff_subst_eq hZ_zero).trans hh_zero
  have hZh_int (k : ℕ) : ‖coeff k (h.subst Z)‖ ≤ 1 := mem_range_seriesToCp.1 (h_mem.1 hh) k
  have hf_int (j : ℕ) : ‖coeff j f‖ * 1 ^ j ≤ 1 := by simpa using mem_range_seriesToCp.1 hf j
  rw [h_mem, subst_comp_subst_apply (.of_constantCoeff_zero' hh_zero)
    (.of_constantCoeff_zero' hZ_zero), mem_range_seriesToCp]
  exact fun n ↦ norm_coeff_subst_le_of_lt hZh_zero zero_le_one (fun k _ ↦ hZh_int k) hf_int
    n.lt_succ_self

/-- Let `B = 𝒪[[T]]` (`IsSeriesGenerator B T`), `c ≠ 0`, `v(c) ≥ 1 / (p - 1)`, that is,
`‖c‖ ≤ p ^ (-1 / (p - 1))`, and `g(0) = 0`. If `exp (c g) = 1 + c H` with `H ∈ B`, where `exp` is
`expSubst`, then `g ∈ B`. -/
lemma mem_of_expSubst_smul_eq {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}
    (hB : IsSeriesGenerator B T) {c : ℂ_[p]} (hc_ne : c ≠ 0)
    (hc : ‖c‖ ≤ p ^ (-(1 / (p - 1)) : ℝ)) {g H : ℂ_[p]⟦X⟧} (hg_zero : constantCoeff g = 0)
    (hH : H ∈ B) (h_exp : expSubst (c • g) = 1 + c • H) : g ∈ B := by
  -- Taking logarithms gives `g = (log (1 + c X) / c)(H)`, an integral series in `H`.
  have hcg : constantCoeff (c • g) = 0 := by simp [hg_zero]
  have hH_zero : constantCoeff H = 0 := by simpa [h_exp, hc_ne] using constantCoeff_expSubst hcg
  have hs : HasSubst H := .of_constantCoeff_zero' hH_zero
  have h_log : (c⁻¹ • rescale c (log ℂ_[p])).subst H = g :=
    calc _ = c⁻¹ • logOf (1 + c • H) := by
          rw [subst_smul hs, subst_rescale_eq_subst_smul _ hs, logOf_eq, add_sub_cancel_left]
      _ = g := by rw [← h_exp, logOf_expSubst hcg, inv_smul_smul₀ hc_ne]
  rw [← h_log]
  exact hB.subst_mem (inv_smul_rescale_log_mem hc) hH hH_zero

/-- Let `B = 𝒪[[T]]` (`IsSeriesGenerator B T`: `T = X + ⋯` and `B` is the ring of all integral
series in `T`), `m` prime to `p` and `g(0) = 0`. If `(exp g) ^ m ∈ B`, where `exp g` is
`expSubst g`, then `exp g ∈ B`. -/
lemma expSubst_mem_of_pow_mem {B : Subring ℂ_[p]⟦X⟧} {T : ℂ_[p]⟦X⟧}
    (hB : IsSeriesGenerator B T) {m : ℕ} (hm : p.Coprime m) {g : ℂ_[p]⟦X⟧}
    (hg_zero : constantCoeff g = 0) (h_pow : expSubst g ^ m ∈ B) : expSubst g ∈ B := by
  -- If `b(0) = 1` and `b ^ m = 1 + X`, then `exp g` is `b` at `(exp g) ^ m - 1`.
  obtain ⟨b, hb_mem, hb_one, hb_pow⟩ := exists_pow_eq_one_add_X hm
  have hm_ne : m ≠ 0 := fun h ↦ (Fact.out : p.Prime).ne_one (by simpa [h] using hm)
  set u : ℂ_[p]⟦X⟧ := expSubst g ^ m - 1 with hu
  have hu_zero : constantCoeff u = 0 := by simp [hu, constantCoeff_expSubst hg_zero]
  have hs : HasSubst u := .of_constantCoeff_zero' hu_zero
  have h_root : b.subst u = expSubst g := by
    refine eq_of_pow_eq_pow_of_constantCoeff_eq_one hm_ne
      ((constantCoeff_subst_eq hu_zero).trans hb_one)
      (constantCoeff_expSubst hg_zero) ?_
    rw [← subst_pow hs, hb_pow, ← coe_substAlgHom hs, map_add, map_one, substAlgHom_X, hu]
    ring
  rw [← h_root]
  exact hB.subst_mem hb_mem (sub_mem h_pow (one_mem B)) hu_zero

end IsSeriesGenerator

end New

end SeriesBounds
