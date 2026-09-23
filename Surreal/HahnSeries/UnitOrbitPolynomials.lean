import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Filter.Cofinite
import Surreal.HahnSeries.PolynomialGaussValuation

/-!
# Polynomial valuations along integer and geometric orbits

This file formalizes `hol:lem:integer`, `hol:lem:affine` and `hol:thm:unitorbit`, together
with `hol:lem:bivariate`, from
`docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`.

The exponent group `Γ` is an arbitrary linearly ordered abelian group; neither divisibility nor
`Γ ≠ 0` is used, and no Archimedean or rank-one argument occurs. The coefficient field `ℂ` of
the source is generalized to an arbitrary field `K`, with characteristic zero assumed exactly
where the source uses it. The valuation `v` is `HahnSeries.orderTop` (value `⊤` at zero);
statements with values in `Γ` use `HahnSeries.order` (junk value `0` at zero) together with
explicit eventual nonvanishing, proved in the same statement or, for
`eventualPeriod_order_eval_pow_dvd`, in `exists_forall_ge_order_eval_pow_residueClass`.

* Initial-form evaluation. `orderTop_eval_eq_of_gaussInitial_eval_ne_zero`: if `v(y) ≥ ρ` and
  the initial polynomial `Surreal.HahnSeries.gaussInitial 0 ρ P` does not vanish at the
  coefficient of `y` at `ρ`, then `v(P(y)) = min_k (v(p_k) + kρ)`. This is the common core of
  the three proofs; `coeff_eval_of_le` identifies the coefficient of `P(y)` at the weighted
  minimum with that value.
* `hol:lem:integer`: `eventually_cofinite_eval_natCast` (for all but finitely many `n`,
  `P(n) ≠ 0` and `v(P(n)) = β(P) = min_{p_k ≠ 0} v(p_k)`) and its threshold form
  `exists_forall_ge_eval_natCast`, over any field of characteristic zero;
  `isRoot_gaussInitial_of_orderTop_eval_natCast_ne` shows that the exceptions are integer
  roots of the residue polynomial `P̄`.
* `hol:lem:affine`: `exists_eventually_order_eval_pow`, over any field. The pairwise-order
  argument is `exists_eventually_sign_affine`, `exists_eventually_lt_or_gt_affine`,
  `exists_eventually_unique_min_affine` (the minimizing index need not be the least one, as in
  `hol:rem:shortcut`) and `exists_eventually_order_sum_affine`.
* `hol:thm:unitorbit` (a): `eventually_cofinite_eval_pow_of_not_isOfFinOrder` and
  `exists_forall_ge_eval_pow_of_not_isOfFinOrder`, over any field. If `v(q) = 0` and
  `res(q)` is not a root of unity, `v(P(q^n))` is eventually the minimum valuation of the
  coefficients of `P`. The hypothesis that `q` has infinite order is implied and not assumed.
  `isRoot_gaussInitial_of_orderTop_eval_pow_ne` shows that every exception `n` satisfies
  `P̄(ζ^n) = 0`.
* `hol:thm:unitorbit` (b), over any field of characteristic zero, for `v(q) = 0`, `q` of
  infinite multiplicative order and `res(q)^h = 1` with `h > 0` (in particular for `h` the
  exact order of `res(q)`): `exists_forall_ge_orderTop_eval_pow_eq_unitClassValue` gives
  eventually `v(P(q^n)) = β_{n mod h}` with the explicit class valuation `unitClassValue` of
  `hol:eq:betar`, computed from `unitClassPoly`, the polynomial `P(ζ^r(1 + Y))` of
  `hol:eq:unitexpand`. `isRoot_gaussInitial_unitClassPoly_of_orderTop_eval_pow_ne` shows that
  every exception `n` satisfies `R_r(n) = 0` for the residue polynomial `R_r` of
  `hol:eq:residuepoly`, `r = n mod h`, written as the initial polynomial
  `gaussInitial 0 η (unitClassPoly q P r)` evaluated at `n · lc(u)`.
  `exists_forall_ge_order_eval_pow_residueClass` is the `Γ`-valued form, and
  `eventualPeriod_order_eval_pow_dvd` proves that the `Γ`-valued sequence is eventually
  `h`-periodic and that its least eventual period divides `h`. The binomial step
  `hol:eq:yn` is `le_orderTop_and_coeff_one_add_pow_sub_one` and
  `orderTop_and_leadingCoeff_one_add_pow_sub_one`.
* `hol:thm:unitorbit`, first sentence: `exists_eventually_periodic_order_eval_pow` (the
  valuation is eventually finite and periodic, with period `1` when `res(q)` is not a root of
  unity and `orderOf (res q)` otherwise), over any field of characteristic zero.
* `hol:lem:bivariate`: `exists_eventually_order_evalEval`, over any field of characteristic
  zero, for `P(U, X) ∈ K⟦Γ⟧[U][X]` evaluated by `Polynomial.evalEval`.

`EventuallyPeriodic` and `exists_eventualPeriod_dvd` are generic facts about sequences on `ℕ`.
The examples `hol:ex:unitperiod` and `hol:ex:unitexception` and the remarks
`hol:rem:shortcut` and `hol:rem:unitalt` are not formalized separately.
-/

namespace Surreal.HolonomicOrbit

open scoped Polynomial
open _root_.HahnSeries

noncomputable section

section AffineComparison

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- An affine function `n ↦ a + n • c` with positive slope has eventually constant strict
sign: it is either eventually positive or eventually negative. -/
theorem exists_eventually_sign_of_pos (a c : Γ) (hc : 0 < c) :
    ∃ N : ℕ, (∀ n, N ≤ n → 0 < a + n • c) ∨ (∀ n, N ≤ n → a + n • c < 0) := by
  by_cases h : ∃ n₀ : ℕ, 0 < a + n₀ • c
  · obtain ⟨n₀, hn₀⟩ := h
    exact ⟨n₀, Or.inl fun n hn =>
      hn₀.trans_le (add_le_add le_rfl (nsmul_le_nsmul_left hc.le hn))⟩
  · push Not at h
    refine ⟨0, Or.inr fun n _ => ?_⟩
    calc a + n • c < a + n • c + c := lt_add_of_pos_right _ hc
      _ = a + (n + 1) • c := by rw [succ_nsmul, add_assoc]
      _ ≤ 0 := h (n + 1)

/-- An affine function `n ↦ a + n • c` with nonzero slope has eventually constant strict
sign. No Archimedean property of `Γ` is used. -/
theorem exists_eventually_sign_affine (a c : Γ) (hc : c ≠ 0) :
    ∃ N : ℕ, (∀ n, N ≤ n → 0 < a + n • c) ∨ (∀ n, N ≤ n → a + n • c < 0) := by
  rcases hc.lt_or_gt with hneg | hpos
  · obtain ⟨N, hN⟩ := exists_eventually_sign_of_pos (-a) (-c) (neg_pos.mpr hneg)
    have e : ∀ n : ℕ, -a + n • -c = -(a + n • c) := fun n => by rw [smul_neg, neg_add]
    refine ⟨N, hN.symm.imp (fun h n hn => ?_) (fun h n hn => ?_)⟩
    · have := h n hn
      rw [e] at this
      exact neg_lt_zero.mp this
    · have := h n hn
      rw [e] at this
      exact neg_pos.mp this
  · exact exists_eventually_sign_of_pos a c hpos

/-- Two distinct affine functions `n ↦ α k + (k n) λ` with `λ ≠ 0` are eventually strictly
ordered, in a fixed direction. -/
theorem exists_eventually_lt_or_gt_affine (α : ℕ → Γ) {lam : Γ} (hlam : lam ≠ 0) {k l : ℕ}
    (hkl : k ≠ l) : ∃ N : ℕ,
      (∀ n, N ≤ n → α k + (k * n) • lam < α l + (l * n) • lam) ∨
      (∀ n, N ≤ n → α l + (l * n) • lam < α k + (k * n) • lam) := by
  wlog hlt : k < l generalizing k l
  · obtain ⟨N, hN⟩ := this hkl.symm (lt_of_le_of_ne (not_lt.mp hlt) hkl.symm)
    exact ⟨N, hN.symm⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  have hc : (m + 1) • lam ≠ 0 := by
    rcases hlam.lt_or_gt with h | h
    · exact (nsmul_neg h (Nat.succ_ne_zero m)).ne
    · exact (nsmul_pos h (Nat.succ_ne_zero m)).ne'
  obtain ⟨N, hN⟩ := exists_eventually_sign_affine (α (k + m + 1) - α k) ((m + 1) • lam) hc
  have e : ∀ n : ℕ, α (k + m + 1) + ((k + m + 1) * n) • lam =
      α k + (k * n) • lam + ((α (k + m + 1) - α k) + n • ((m + 1) • lam)) := fun n => by
    rw [smul_smul, show (k + m + 1) * n = k * n + n * (m + 1) by ring, add_nsmul]
    abel
  refine ⟨N, hN.imp (fun h n hn => ?_) (fun h n hn => ?_)⟩
  · rw [e n]
    exact lt_add_of_pos_right _ (h n hn)
  · rw [e n]
    exact add_lt_of_neg_right _ (h n hn)

/-- Finitely many affine functions `n ↦ α k + (k n) λ`, `k ∈ S`, with `λ ≠ 0` have a unique
eventual minimizer. The minimizing index need not be the least one (`hol:rem:shortcut`); only
the eventual ordering of finitely many affine functions is used. -/
theorem exists_eventually_unique_min_affine (S : Finset ℕ) (hS : S.Nonempty) (α : ℕ → Γ)
    {lam : Γ} (hlam : lam ≠ 0) : ∃ k ∈ S, ∃ N : ℕ, ∀ n, N ≤ n → ∀ l ∈ S, l ≠ k →
      α k + (k * n) • lam < α l + (l * n) • lam := by
  have hpair : ∀ k l : ℕ, ∃ N : ℕ, k = l ∨
      (∀ n, N ≤ n → α k + (k * n) • lam < α l + (l * n) • lam) ∨
      (∀ n, N ≤ n → α l + (l * n) • lam < α k + (k * n) • lam) := by
    intro k l
    by_cases hkl : k = l
    · exact ⟨0, Or.inl hkl⟩
    · obtain ⟨N, hN⟩ := exists_eventually_lt_or_gt_affine α hlam hkl
      exact ⟨N, Or.inr hN⟩
  choose M hM using hpair
  obtain ⟨k, hk, hmin⟩ := S.exists_min_image
    (fun k => α k + (k * (S ×ˢ S).sup fun p => M p.1 p.2) • lam) hS
  refine ⟨k, hk, (S ×ˢ S).sup fun p => M p.1 p.2, fun n hn l hl hlk => ?_⟩
  have hMle : M k l ≤ (S ×ˢ S).sup fun p => M p.1 p.2 :=
    Finset.le_sup (f := fun p : ℕ × ℕ => M p.1 p.2)
      (show (k, l) ∈ S ×ˢ S from Finset.mem_product.mpr ⟨hk, hl⟩)
  rcases hM k l with h | h | h
  · exact absurd h.symm hlk
  · exact h n (hMle.trans hn)
  · exact absurd (hmin l hl) (not_le.mpr (h _ hMle))

end AffineComparison

section HahnSums

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- A finite sum whose term `k` has strictly smallest valuation has the valuation of that
term: the leading term cannot cancel against terms of strictly larger valuation. -/
theorem orderTop_sum_eq_of_forall_lt {ι : Type*} (S : Finset ι) (t : ι → K⟦Γ⟧) {k : ι}
    (hk : k ∈ S) (hk0 : t k ≠ 0) (hlt : ∀ l ∈ S, l ≠ k → (t k).orderTop < (t l).orderTop) :
    (∑ l ∈ S, t l).orderTop = (t k).orderTop := by
  classical
  rw [← Finset.add_sum_erase S t hk]
  apply orderTop_add_eq_left
  have h := (addVal Γ K).map_lt_sum (s := S.erase k) (f := t) (orderTop_ne_top.mpr hk0)
    fun l hl => by
      rw [addVal_apply]
      exact hlt l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
  rwa [addVal_apply] at h

omit [IsOrderedAddMonoid Γ] in
/-- A finite valuation value pins down nonvanishing and the order. -/
theorem ne_zero_and_order_eq_of_orderTop_eq {x : K⟦Γ⟧} {g : Γ} (h : x.orderTop = g) :
    x ≠ 0 ∧ x.order = g := by
  have hx : x ≠ 0 := fun hx => by
    rw [hx, orderTop_zero] at h
    exact WithTop.top_ne_coe h
  exact ⟨hx, WithTop.coe_inj.mp ((order_eq_orderTop_of_ne_zero hx).trans h)⟩

/-- The pairwise-order argument of `hol:lem:affine` for an arbitrary finite family of
eventually nonzero terms `t k n` with affine valuations `α k + (k n) λ`, `λ ≠ 0`: the sum is
eventually nonzero with the valuation of a unique eventual minimizer. -/
theorem exists_eventually_order_sum_affine (S : Finset ℕ) (hS : S.Nonempty)
    (t : ℕ → ℕ → K⟦Γ⟧) (α : ℕ → Γ) {lam : Γ} (hlam : lam ≠ 0) (N₀ : ℕ)
    (ht : ∀ k ∈ S, ∀ n, N₀ ≤ n → t k n ≠ 0 ∧ (t k n).order = α k + (k * n) • lam) :
    ∃ k ∈ S, ∃ N : ℕ, ∀ n, N ≤ n →
      (∑ l ∈ S, t l n) ≠ 0 ∧ (∑ l ∈ S, t l n).order = α k + (k * n) • lam := by
  obtain ⟨k, hk, N, hN⟩ := exists_eventually_unique_min_affine S hS α hlam
  refine ⟨k, hk, max N N₀, fun n hn => ?_⟩
  have htop : ∀ l ∈ S, (t l n).orderTop = (α l + (l * n) • lam : Γ) := fun l hl => by
    obtain ⟨h0, hord⟩ := ht l hl n (le_of_max_le_right hn)
    rw [← order_eq_orderTop_of_ne_zero h0, hord]
  apply ne_zero_and_order_eq_of_orderTop_eq
  rw [orderTop_sum_eq_of_forall_lt S (fun l => t l n) hk (ht k hk n (le_of_max_le_right hn)).1
    fun l hl hlk => by
      rw [htop k hk, htop l hl, WithTop.coe_lt_coe]
      exact hN n (le_of_max_le_left hn) l hl hlk]
  exact htop k hk

/-- `hol:lem:affine`: let `q ≠ 0` have valuation `λ = v(q) ≠ 0` and let `P ≠ 0`. There are an
index `k_P` with `p_{k_P} ≠ 0` and a threshold `N_P` such that for all `n ≥ N_P`,
`P(q^n) ≠ 0` and `v(P(q^n)) = v(p_{k_P}) + k_P n λ` (`hol:eq:affine`). The exponent group is
arbitrary and the coefficient field is any field. -/
theorem exists_eventually_order_eval_pow (q : K⟦Γ⟧) (hq : q ≠ 0) (hlam : q.order ≠ 0)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) : ∃ k ∈ P.support, ∃ N : ℕ, ∀ n, N ≤ n →
      P.eval (q ^ n) ≠ 0 ∧ (P.eval (q ^ n)).order = (P.coeff k).order + (k * n) • q.order := by
  have heval : ∀ n : ℕ, P.eval (q ^ n) = ∑ l ∈ P.support, P.coeff l * (q ^ n) ^ l := fun n => by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [heval]
  refine exists_eventually_order_sum_affine P.support (Polynomial.support_nonempty.mpr hP)
    (fun l n => P.coeff l * (q ^ n) ^ l) (fun l => (P.coeff l).order) hlam 0
    fun l hl n _ => ?_
  have hl0 : P.coeff l ≠ 0 := Polynomial.mem_support_iff.mp hl
  have hpow : (q ^ n) ^ l ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hq)
  refine ⟨mul_ne_zero hl0 hpow, ?_⟩
  rw [order_mul hl0 hpow, ← pow_mul, order_pow, mul_comm n l]

end HahnSums

section InitialEvaluation

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- The coefficient of a product at `a + b`, when the factors have valuations at least `a`
and `b`, is the product of the coefficients at `a` and `b`. -/
theorem coeff_mul_add_of_le (x z : K⟦Γ⟧) {a b : Γ} (hx : (a : WithTop Γ) ≤ x.orderTop)
    (hz : (b : WithTop Γ) ≤ z.orderTop) : (x * z).coeff (a + b) = x.coeff a * z.coeff b := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hz0 : z = 0
  · simp [hz0]
  rw [← order_eq_orderTop_of_ne_zero hx0, WithTop.coe_le_coe] at hx
  rw [← order_eq_orderTop_of_ne_zero hz0, WithTop.coe_le_coe] at hz
  rcases hx.lt_or_eq with hxa | rfl
  · rw [coeff_eq_zero_of_lt_order hxa, zero_mul]
    apply coeff_eq_zero_of_lt_order
    rw [order_mul hx0 hz0]
    exact add_lt_add_of_lt_of_le hxa hz
  rcases hz.lt_or_eq with hzb | rfl
  · rw [coeff_eq_zero_of_lt_order hzb, mul_zero]
    apply coeff_eq_zero_of_lt_order
    rw [order_mul hx0 hz0]
    exact add_lt_add_of_le_of_lt le_rfl hzb
  · rw [coeff_mul_order_add_order, leadingCoeff_eq, leadingCoeff_eq]

/-- If `v(y) ≥ ρ`, then `v(y^k) ≥ kρ` and the coefficient of `y^k` at `kρ` is the `k`th power
of the coefficient of `y` at `ρ`. -/
theorem le_orderTop_pow_and_coeff (y : K⟦Γ⟧) {ρ : Γ} (hy : (ρ : WithTop Γ) ≤ y.orderTop)
    (k : ℕ) :
    ((k • ρ : Γ) : WithTop Γ) ≤ (y ^ k).orderTop ∧ (y ^ k).coeff (k • ρ) = y.coeff ρ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · rw [pow_succ, orderTop_mul, succ_nsmul, WithTop.coe_add]
      exact add_le_add ih.1 hy
    · rw [pow_succ, succ_nsmul, coeff_mul_add_of_le _ _ ih.1 hy, ih.2, pow_succ]

/-- Subtracting a finite exponent from a lower bound. -/
private theorem coe_sub_le_of_le_add {g c : Γ} {o : WithTop Γ} (h : (g : WithTop Γ) ≤ o + c) :
    ((g - c : Γ) : WithTop Γ) ≤ o := by
  induction o using WithTop.recTopCoe with
  | top => exact le_top
  | coe o =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    exact WithTop.coe_le_coe.mpr (sub_le_iff_le_add.mpr h)

/-- The ultrametric lower bound: if `v(y) ≥ ρ`, then `v(P(y))` is at least the weighted
coefficient minimum `min_k (v(p_k) + kρ)`. -/
theorem le_orderTop_eval (P : K⟦Γ⟧[X]) (y : K⟦Γ⟧) {ρ : Γ}
    (hy : (ρ : WithTop Γ) ≤ y.orderTop) :
    (P.support.inf fun k => (P.coeff k).orderTop + (k • ρ : Γ)) ≤ (P.eval y).orderTop := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply (addVal Γ K).map_le_sum
  intro k hk
  rw [addVal_apply, orderTop_mul]
  exact (Finset.inf_le hk).trans (add_le_add le_rfl (le_orderTop_pow_and_coeff y hy k).1)

/-- If `v(y) ≥ ρ`, then at every exponent `g` not exceeding the weighted coefficient minimum,
only the pairs `(g - kρ, kρ)` contribute to the coefficient of `P(y)`. -/
theorem coeff_eval_of_le (P : K⟦Γ⟧[X]) (y : K⟦Γ⟧) {ρ : Γ}
    (hy : (ρ : WithTop Γ) ≤ y.orderTop) {g : Γ}
    (hg : ∀ k ∈ P.support, (g : WithTop Γ) ≤ (P.coeff k).orderTop + (k • ρ : Γ)) :
    (P.eval y).coeff g = ∑ k ∈ P.support, (P.coeff k).coeff (g - k • ρ) * y.coeff ρ ^ k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, coeff_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h2 := le_orderTop_pow_and_coeff y hy k
  rw [← h2.2, ← coeff_mul_add_of_le _ _ (coe_sub_le_of_le_add (hg k hk)) h2.1, sub_add_cancel]

/-- The weighted coefficient minimum of a nonzero polynomial is finite. -/
theorem inf_orderTop_add_nsmul_ne_top {P : K⟦Γ⟧[X]} (hP : P ≠ 0) (ρ : Γ) :
    (P.support.inf fun k => (P.coeff k).orderTop + (k • ρ : Γ)) ≠ ⊤ := by
  have h := (Surreal.HahnSeries.weightedGaussVal_eq_top_iff 0 ρ P).not.mpr hP
  rwa [Surreal.HahnSeries.weightedGaussVal_eq_inf, Polynomial.taylor_zero] at h

/-- Initial-form evaluation. If `v(y) ≥ ρ` and the initial polynomial of `P` for the weight
`ρ` (`Surreal.HahnSeries.gaussInitial 0 ρ P`, the polynomial `∑_{k active} lc(p_k) T^k` over
the indices attaining the weighted minimum) does not vanish at the coefficient of `y` at `ρ`,
then `v(P(y))` equals the weighted minimum `min_k (v(p_k) + kρ)`: the coefficient of `P(y)`
at that exponent is exactly this value of the initial polynomial. -/
theorem orderTop_eval_eq_of_gaussInitial_eval_ne_zero (P : K⟦Γ⟧[X]) (y : K⟦Γ⟧) {ρ : Γ}
    (hy : (ρ : WithTop Γ) ≤ y.orderTop)
    (h : (Surreal.HahnSeries.gaussInitial 0 ρ P).eval (y.coeff ρ) ≠ 0) :
    (P.eval y).orderTop = P.support.inf fun k => (P.coeff k).orderTop + (k • ρ : Γ) := by
  have hP : P ≠ 0 := by
    rintro rfl
    apply h
    simp [Surreal.HahnSeries.gaussInitial]
  have hE : Surreal.HahnSeries.centeredGaussExpansion (0 : K⟦Γ⟧) ρ P ≠ 0 :=
    (map_eq_zero_iff _ (Surreal.HahnSeries.centeredGaussExpansion_injective 0 ρ)).not.mpr hP
  have hw : ((Surreal.HahnSeries.centeredGaussExpansion (0 : K⟦Γ⟧) ρ P).order : WithTop Γ) =
      P.support.inf fun k => (P.coeff k).orderTop + (k • ρ : Γ) := by
    rw [order_eq_orderTop_of_ne_zero hE, ← Surreal.HahnSeries.weightedGaussVal_apply,
      Surreal.HahnSeries.weightedGaussVal_eq_inf, Polynomial.taylor_zero]
  have hsub : (Surreal.HahnSeries.gaussInitial 0 ρ P).support ⊆ P.support := by
    intro k hk
    rw [Polynomial.mem_support_iff] at hk ⊢
    intro hPk
    apply hk
    rw [Surreal.HahnSeries.coeff_gaussInitial, Polynomial.taylor_zero, hPk, coeff_zero]
  have hcoeff : (P.eval y).coeff (Surreal.HahnSeries.centeredGaussExpansion (0 : K⟦Γ⟧) ρ P).order =
      (Surreal.HahnSeries.gaussInitial 0 ρ P).eval (y.coeff ρ) := by
    rw [coeff_eval_of_le P y hy (fun k hk => by rw [hw]; exact Finset.inf_le hk),
      Polynomial.eval_eq_sum,
      Polynomial.sum_eq_of_subset (fun e a => a * y.coeff ρ ^ e) (fun _ => zero_mul _) hsub]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Surreal.HahnSeries.coeff_gaussInitial, Polynomial.taylor_zero]
  rw [← hw]
  refine le_antisymm (orderTop_le_of_coeff_ne_zero (hcoeff ▸ h)) ?_
  rw [hw]
  exact le_orderTop_eval P y hy

/-- The case `ρ = 0` of the initial-form evaluation: if `v(y) ≥ 0` and the residue polynomial
`P̄ = gaussInitial 0 0 P` does not vanish at `res(y)`, then `v(P(y)) = min_k v(p_k)`. -/
theorem orderTop_eval_eq_inf_of_not_isRoot (P : K⟦Γ⟧[X]) (y : K⟦Γ⟧) (hy : 0 ≤ y.orderTop)
    (h : ¬ (Surreal.HahnSeries.gaussInitial 0 0 P).IsRoot (y.coeff 0)) :
    (P.eval y).orderTop = P.support.inf fun k => (P.coeff k).orderTop := by
  have := orderTop_eval_eq_of_gaussInitial_eval_ne_zero P y (ρ := 0)
    (by rwa [WithTop.coe_zero]) h
  simpa only [smul_zero, WithTop.coe_zero, add_zero] using this

/-- `β(P) = min_{p_k ≠ 0} v(p_k)`, as an element of the exponent group, agrees with the
valuation minimum over the coefficient support. -/
theorem coe_inf'_order (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ((P.support.inf' (Polynomial.support_nonempty.mpr hP) fun k => (P.coeff k).order : Γ) :
      WithTop Γ) = P.support.inf fun k => (P.coeff k).orderTop := by
  rw [Finset.coe_inf']
  refine Finset.inf_congr rfl fun k hk => ?_
  exact order_eq_orderTop_of_ne_zero (Polynomial.mem_support_iff.mp hk)

end InitialEvaluation

/-- On `ℕ`, "for all but finitely many `n`" gives "for all `n ≥ N`". -/
theorem exists_forall_ge_of_eventually_cofinite {p : ℕ → Prop}
    (h : ∀ᶠ n in Filter.cofinite, p n) : ∃ N : ℕ, ∀ n, N ≤ n → p n := by
  rw [Nat.cofinite_eq_atTop] at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  exact ⟨N, hN⟩

section IntegerOrbit

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- An ordinary natural number is the constant Hahn series with that coefficient. -/
theorem natCast_eq_single_zero (n : ℕ) : (n : K⟦Γ⟧) = single 0 (n : K) := by
  rw [← C_apply, map_natCast]

/-- The proof of `hol:lem:integer`: every exceptional natural number is a root of the residue
polynomial `P̄ = gaussInitial 0 0 P = ∑_{v(p_k) = β(P)} lc(p_k) X^k`. -/
theorem isRoot_gaussInitial_of_orderTop_eval_natCast_ne (P : K⟦Γ⟧[X]) {n : ℕ}
    (hn : (P.eval (n : K⟦Γ⟧)).orderTop ≠ P.support.inf fun k => (P.coeff k).orderTop) :
    (Surreal.HahnSeries.gaussInitial 0 0 P).IsRoot (n : K) := by
  by_contra hroot
  apply hn
  apply orderTop_eval_eq_inf_of_not_isRoot
  · rw [natCast_eq_single_zero]
    exact orderTop_single_le
  · rwa [natCast_eq_single_zero, coeff_single_same]

/-- `hol:lem:integer`: for `0 ≠ P = ∑ p_k X^k` with `β(P) = min_{p_k ≠ 0} v(p_k)`, for all but
finitely many natural numbers `n`, `P(n) ≠ 0` and `v(P(n)) = β(P)`
(`hol:eq:integerstable`). The coefficient field is any field of characteristic zero. -/
theorem eventually_cofinite_eval_natCast [CharZero K] (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∀ᶠ n : ℕ in Filter.cofinite, P.eval (n : K⟦Γ⟧) ≠ 0 ∧ (P.eval (n : K⟦Γ⟧)).order =
      P.support.inf' (Polynomial.support_nonempty.mpr hP) fun k => (P.coeff k).order := by
  have hG := Surreal.HahnSeries.gaussInitial_ne_zero 0 (0 : Γ) P hP
  refine Filter.eventually_cofinite.mpr (((Polynomial.finite_setOf_isRoot hG).preimage
    (Nat.cast_injective (R := K)).injOn).subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  by_contra hroot
  apply hn
  refine ne_zero_and_order_eq_of_orderTop_eq ((?_ : _ = _).trans (coe_inf'_order P hP).symm)
  by_contra hne
  exact hroot (isRoot_gaussInitial_of_orderTop_eval_natCast_ne P hne)

/-- `hol:lem:integer`, threshold form: `P(n) ≠ 0` and `v(P(n)) = β(P)` for all large `n`. -/
theorem exists_forall_ge_eval_natCast [CharZero K] (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → P.eval (n : K⟦Γ⟧) ≠ 0 ∧ (P.eval (n : K⟦Γ⟧)).order =
      P.support.inf' (Polynomial.support_nonempty.mpr hP) fun k => (P.coeff k).order :=
  exists_forall_ge_of_eventually_cofinite (eventually_cofinite_eval_natCast P hP)

end IntegerOrbit

section UnitOrbit

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

omit [IsOrderedAddMonoid Γ] in
/-- A valuation-zero Hahn series has nonzero residue `res(q) = q.coeff 0`. -/
theorem coeff_zero_ne_zero_of_orderTop_eq_zero {q : K⟦Γ⟧} (hq : q.orderTop = 0) :
    q.coeff 0 ≠ 0 :=
  coeff_orderTop_ne (hq.trans WithTop.coe_zero.symm)

/-- If `ζ ≠ 0` is not a root of unity, the powers `ζ^n` are pairwise distinct. -/
theorem pow_injective_of_not_isOfFinOrder {ζ : K} (hζ0 : ζ ≠ 0) (hζ : ¬ IsOfFinOrder ζ) :
    Function.Injective fun n : ℕ => ζ ^ n := by
  intro n m hnm
  simp only at hnm
  wlog hle : n ≤ m generalizing n m
  · exact (this hnm.symm (le_of_not_ge hle)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rcases d with _ | d
  · rfl
  · exfalso
    apply hζ
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨d + 1, Nat.succ_pos d, ?_⟩
    rw [pow_add] at hnm
    exact mul_left_cancel₀ (pow_ne_zero n hζ0) (hnm.symm.trans (mul_one _).symm)

/-- The proof of `hol:thm:unitorbit` (a): if `v(q) = 0` and `v(P(q^n))` differs from the
minimum valuation of the coefficients of `P`, then `ζ^n` is a root of the residue polynomial
`P̄ = gaussInitial 0 0 P = ∑_{v(p_k) = β(P)} lc(p_k) X^k`, where `ζ = res(q)`. -/
theorem isRoot_gaussInitial_of_orderTop_eval_pow_ne {q : K⟦Γ⟧} (hq : q.orderTop = 0)
    (P : K⟦Γ⟧[X]) {n : ℕ}
    (hn : (P.eval (q ^ n)).orderTop ≠ P.support.inf fun k => (P.coeff k).orderTop) :
    (Surreal.HahnSeries.gaussInitial 0 0 P).IsRoot (q.coeff 0 ^ n) := by
  by_contra hroot
  apply hn
  have hpow := le_orderTop_pow_and_coeff q (ρ := 0) (le_of_eq (by rw [hq, WithTop.coe_zero])) n
  simp only [smul_zero, WithTop.coe_zero] at hpow
  exact orderTop_eval_eq_inf_of_not_isRoot P _ hpow.1 (by rwa [hpow.2])

/-- `hol:thm:unitorbit` (a): let `v(q) = 0` and let `ζ = res(q)` not be a root of unity. For
`P ≠ 0`, for all but finitely many `n`, `P(q^n) ≠ 0` and `v(P(q^n))` is the minimum valuation
`β(P)` of the coefficients of `P`. The proof shows that every exception `n` satisfies
`P̄(ζ^n) = 0` (`isRoot_gaussInitial_of_orderTop_eval_pow_ne`). No characteristic hypothesis is
needed, and infinite order of `q` follows from that of `ζ`. -/
theorem eventually_cofinite_eval_pow_of_not_isOfFinOrder {q : K⟦Γ⟧} (hq : q.orderTop = 0)
    (hζ : ¬ IsOfFinOrder (q.coeff 0)) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∀ᶠ n : ℕ in Filter.cofinite, P.eval (q ^ n) ≠ 0 ∧ (P.eval (q ^ n)).order =
      P.support.inf' (Polynomial.support_nonempty.mpr hP) fun k => (P.coeff k).order := by
  have hG := Surreal.HahnSeries.gaussInitial_ne_zero 0 (0 : Γ) P hP
  refine Filter.eventually_cofinite.mpr (((Polynomial.finite_setOf_isRoot hG).preimage
    (pow_injective_of_not_isOfFinOrder (coeff_zero_ne_zero_of_orderTop_eq_zero hq)
      hζ).injOn).subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  by_contra hroot
  apply hn
  refine ne_zero_and_order_eq_of_orderTop_eq ((?_ : _ = _).trans (coe_inf'_order P hP).symm)
  by_contra hne
  exact hroot (isRoot_gaussInitial_of_orderTop_eval_pow_ne hq P hne)

/-- `hol:thm:unitorbit` (a), threshold form: `v(P(q^n))` is eventually constant, equal to the
minimum valuation of the coefficients of `P`. -/
theorem exists_forall_ge_eval_pow_of_not_isOfFinOrder {q : K⟦Γ⟧} (hq : q.orderTop = 0)
    (hζ : ¬ IsOfFinOrder (q.coeff 0)) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → P.eval (q ^ n) ≠ 0 ∧ (P.eval (q ^ n)).order =
      P.support.inf' (Polynomial.support_nonempty.mpr hP) fun k => (P.coeff k).order :=
  exists_forall_ge_of_eventually_cofinite
    (eventually_cofinite_eval_pow_of_not_isOfFinOrder hq hζ P hP)

/-- The normalized dilation `u = q/ζ - 1` of the proof of `hol:thm:unitorbit` (b), where
`ζ = res(q)`, so that `q = ζ (1 + u)`. -/
def unitShift (q : K⟦Γ⟧) : K⟦Γ⟧ :=
  single 0 (q.coeff 0)⁻¹ * q - 1

/-- `q = ζ (1 + u)` with `ζ = res(q) ≠ 0`. -/
theorem eq_single_mul_one_add_unitShift {q : K⟦Γ⟧} (hζ : q.coeff 0 ≠ 0) :
    q = single 0 (q.coeff 0) * (1 + unitShift q) := by
  rw [unitShift, add_sub_cancel, ← mul_assoc, single_mul_single, add_zero,
    mul_inv_cancel₀ hζ, single_zero_one, one_mul]

/-- `v(u) > 0`: `q/ζ` has valuation zero and residue `1`. -/
theorem orderTop_unitShift_pos {q : K⟦Γ⟧} (hq : q.orderTop = 0) :
    0 < (unitShift q).orderTop := by
  have hζ := coeff_zero_ne_zero_of_orderTop_eq_zero hq
  have h1 : (single 0 (q.coeff 0)⁻¹ * q).orderTop = 0 := by
    rw [orderTop_mul, orderTop_single (inv_ne_zero hζ), hq, WithTop.coe_zero, add_zero]
  apply (Surreal.HahnSeries.coeff_zero_eq_zero_iff_orderTop_pos _ ?_).mp
  · rw [unitShift, coeff_sub, coeff_single_zero_mul, inv_mul_cancel₀ hζ, coeff_one, if_pos rfl,
      sub_self]
  · exact (le_min h1.ge orderTop_one.ge).trans min_orderTop_le_orderTop_sub

/-- `u ≠ 0`: otherwise `q = ζ` would have finite order. Only `ζ^h = 1` for some `h > 0`
is used. -/
theorem unitShift_ne_zero {q : K⟦Γ⟧} (hqt : ¬ IsOfFinOrder q) {h : ℕ} (hh : 0 < h)
    (hζh : q.coeff 0 ^ h = 1) : unitShift q ≠ 0 := by
  intro hu
  apply hqt
  have hζ : q.coeff 0 ≠ 0 := by
    rintro h0
    rw [h0, zero_pow hh.ne'] at hζh
    exact zero_ne_one hζh
  have hq' := eq_single_mul_one_add_unitShift hζ
  rw [hu, add_zero, mul_one] at hq'
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨h, hh, ?_⟩
  rw [hq', single_pow, smul_zero, hζh, single_zero_one]

/-- The finite binomial expansion `hol:eq:yn`: if `v(u) ≥ η > 0`, then
`y_n = (1 + u)^n - 1` has `v(y_n) ≥ η` and coefficient `n · u_η` at `η`. -/
theorem le_orderTop_and_coeff_one_add_pow_sub_one (u : K⟦Γ⟧) {η : Γ} (hη : 0 < η)
    (hu : (η : WithTop Γ) ≤ u.orderTop) (n : ℕ) :
    (η : WithTop Γ) ≤ ((1 + u) ^ n - 1).orderTop ∧ ((1 + u) ^ n - 1).coeff η = n * u.coeff η := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hrec : (1 + u) ^ (n + 1) - 1 = ((1 + u) ^ n - 1) + u + ((1 + u) ^ n - 1) * u := by
      ring
    have hyu : ((η + η : Γ) : WithTop Γ) ≤ (((1 + u) ^ n - 1) * u).orderTop := by
      rw [orderTop_mul, WithTop.coe_add]
      exact add_le_add ih1 hu
    have hlt : (η : WithTop Γ) < ((η + η : Γ) : WithTop Γ) :=
      WithTop.coe_lt_coe.mpr (lt_add_of_pos_right η hη)
    rw [hrec]
    refine ⟨?_, ?_⟩
    · exact (le_min ((le_min ih1 hu).trans min_orderTop_le_orderTop_add)
        (hlt.le.trans hyu)).trans min_orderTop_le_orderTop_add
    · rw [coeff_add, coeff_add, ih2, coeff_eq_zero_of_lt_orderTop (hlt.trans_le hyu)]
      push_cast
      ring

/-- `hol:eq:yn`: in characteristic zero, for `u ≠ 0` with `η = v(u) > 0` and every positive
integer `n`, `y_n = (1 + u)^n - 1` has `v(y_n) = η` and `lc(y_n) = n lc(u)`. -/
theorem orderTop_and_leadingCoeff_one_add_pow_sub_one [CharZero K] {u : K⟦Γ⟧} (hu0 : u ≠ 0)
    (hu : 0 < u.orderTop) {n : ℕ} (hn : 0 < n) :
    ((1 + u) ^ n - 1).orderTop = u.orderTop ∧
      ((1 + u) ^ n - 1).leadingCoeff = n * u.leadingCoeff := by
  have huη : (u.order : WithTop Γ) = u.orderTop := order_eq_orderTop_of_ne_zero hu0
  have hη : 0 < u.order := by
    have h0 : (0 : WithTop Γ) < u.order := by
      rw [huη]
      exact hu
    exact WithTop.coe_pos.mp h0
  obtain ⟨h1, h2⟩ := le_orderTop_and_coeff_one_add_pow_sub_one u hη huη.le n
  have hc : ((1 + u) ^ n - 1).coeff u.order ≠ 0 := by
    rw [h2]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (coeff_order_eq_zero.not.mpr hu0)
  have htop : ((1 + u) ^ n - 1).orderTop = u.order :=
    le_antisymm (orderTop_le_of_coeff_ne_zero hc) h1
  refine ⟨htop.trans huη, ?_⟩
  rw [leadingCoeff_eq, (ne_zero_and_order_eq_of_orderTop_eq htop).2, h2, leadingCoeff_eq]

/-- The expanded polynomial `P(ζ^r (1 + Y))` of `hol:eq:unitexpand`, with `ζ = res(q)`. -/
def unitClassPoly (q : K⟦Γ⟧) (P : K⟦Γ⟧[X]) (r : ℕ) : K⟦Γ⟧[X] :=
  P.comp (Polynomial.C (single 0 (q.coeff 0 ^ r)) * (1 + Polynomial.X))

/-- The class valuation `β_r = min_{b_{r,k} ≠ 0} (v(b_{r,k}) + kη)` of `hol:eq:betar`, where
`b_{r,k}` are the coefficients of `P(ζ^r (1 + Y))` and `η = v(u)`. -/
def unitClassValue (q : K⟦Γ⟧) (P : K⟦Γ⟧[X]) (r : ℕ) : WithTop Γ :=
  (unitClassPoly q P r).support.inf fun k =>
    ((unitClassPoly q P r).coeff k).orderTop + (k • (unitShift q).order : Γ)

/-- `P(ζ^r (1 + Y))` is nonzero for `P ≠ 0` and `ζ ≠ 0`. -/
theorem unitClassPoly_ne_zero {q : K⟦Γ⟧} (hζ : q.coeff 0 ≠ 0) {P : K⟦Γ⟧[X]} (hP : P ≠ 0)
    (r : ℕ) : unitClassPoly q P r ≠ 0 := by
  rw [unitClassPoly, Ne, Polynomial.comp_eq_zero_iff]
  rintro (h | ⟨-, h⟩)
  · exact hP h
  · have h1 := congrArg (fun p : K⟦Γ⟧[X] => p.coeff 1) h
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_X_one, Polynomial.coeff_C, one_ne_zero, ↓reduceIte, zero_add,
      mul_one] at h1
    exact single_ne_zero (pow_ne_zero r hζ) h1

/-- For `n ≡ r (mod h)`, `P(q^n) = P(ζ^r (1 + y_n))` with `y_n = (1 + u)^n - 1`. -/
theorem eval_pow_eq_eval_unitClassPoly {q : K⟦Γ⟧} (hζ : q.coeff 0 ≠ 0) {h : ℕ}
    (hζh : q.coeff 0 ^ h = 1) (P : K⟦Γ⟧[X]) (n : ℕ) :
    P.eval (q ^ n) = (unitClassPoly q P (n % h)).eval ((1 + unitShift q) ^ n - 1) := by
  rw [unitClassPoly, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, add_sub_cancel,
    ← pow_eq_pow_mod n hζh]
  conv_lhs => rw [eq_single_mul_one_add_unitShift hζ]
  rw [mul_pow, single_pow, smul_zero]

/-- The proof of `hol:thm:unitorbit` (b): let `v(q) = 0`, `q` of infinite multiplicative order,
and `ζ = res(q)` with `ζ^h = 1` for some `h > 0`. If `v(P(q^n)) ≠ β_r` for `r = n mod h`, then
`n · lc(u)` is a root of the initial polynomial `gaussInitial 0 η (unitClassPoly q P r)` for the
weight `η = v(u)`; that value is `R_r(n)` for the residue polynomial `R_r` of
`hol:eq:residuepoly`. -/
theorem isRoot_gaussInitial_unitClassPoly_of_orderTop_eval_pow_ne {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) {h : ℕ} (hh : 0 < h)
    (hζh : q.coeff 0 ^ h = 1) (P : K⟦Γ⟧[X]) {n : ℕ}
    (hn : (P.eval (q ^ n)).orderTop ≠ unitClassValue q P (n % h)) :
    (Surreal.HahnSeries.gaussInitial 0 (unitShift q).order (unitClassPoly q P (n % h))).IsRoot
      ((n : K) * (unitShift q).coeff (unitShift q).order) := by
  have hζ := coeff_zero_ne_zero_of_orderTop_eq_zero hq
  have hu0 : unitShift q ≠ 0 := unitShift_ne_zero hqt hh hζh
  have huη : ((unitShift q).order : WithTop Γ) = (unitShift q).orderTop :=
    order_eq_orderTop_of_ne_zero hu0
  have hη : 0 < (unitShift q).order := by
    have h0 : (0 : WithTop Γ) < (unitShift q).order := by
      rw [huη]
      exact orderTop_unitShift_pos hq
    exact WithTop.coe_pos.mp h0
  by_contra hroot
  apply hn
  obtain ⟨hy1, hy2⟩ := le_orderTop_and_coeff_one_add_pow_sub_one (unitShift q) hη huη.le n
  rw [eval_pow_eq_eval_unitClassPoly hζ hζh P n]
  exact orderTop_eval_eq_of_gaussInitial_eval_ne_zero _ _ hy1 (by rwa [hy2])

/-- `hol:thm:unitorbit` (b), explicit form: let `v(q) = 0`, `q` of infinite multiplicative
order, and `ζ = res(q)` with `ζ^h = 1` for some `h > 0` (for instance `h` the exact order of
`ζ`). For `P ≠ 0`, eventually `v(P(q^n)) = β_{n mod h}`, the class valuation of
`hol:eq:betar`. The proof excludes the natural numbers `n` for which `n · lc(u)` is a root of
the initial polynomial `gaussInitial 0 η (unitClassPoly q P (n mod h))`, that is `R_r(n) = 0`
for the residue polynomial `R_r` of `hol:eq:residuepoly` with `r = n mod h`
(`isRoot_gaussInitial_unitClassPoly_of_orderTop_eval_pow_ne`). -/
theorem exists_forall_ge_orderTop_eval_pow_eq_unitClassValue [CharZero K] {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) {h : ℕ} (hh : 0 < h)
    (hζh : q.coeff 0 ^ h = 1) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∃ N : ℕ, ∀ n, N ≤ n → (P.eval (q ^ n)).orderTop = unitClassValue q P (n % h) := by
  have hζ := coeff_zero_ne_zero_of_orderTop_eq_zero hq
  have hu0 : unitShift q ≠ 0 := unitShift_ne_zero hqt hh hζh
  have hd : (unitShift q).coeff (unitShift q).order ≠ 0 := coeff_order_eq_zero.not.mpr hu0
  have hG : ∀ r, Surreal.HahnSeries.gaussInitial 0 (unitShift q).order (unitClassPoly q P r) ≠ 0 :=
    fun r => Surreal.HahnSeries.gaussInitial_ne_zero 0 _ _ (unitClassPoly_ne_zero hζ hP r)
  have hfin : (⋃ r : Fin h, {n : ℕ | (Surreal.HahnSeries.gaussInitial 0 (unitShift q).order
      (unitClassPoly q P r)).IsRoot ((n : K) * (unitShift q).coeff (unitShift q).order)}).Finite :=
    Set.finite_iUnion fun r => (Polynomial.finite_setOf_isRoot (hG r)).preimage
      ((mul_left_injective₀ hd).comp (Nat.cast_injective (R := K))).injOn
  obtain ⟨M, hM⟩ := hfin.bddAbove
  refine ⟨M + 1, fun n hn => ?_⟩
  by_contra hne
  have := hM (Set.mem_iUnion.mpr ⟨⟨n % h, Nat.mod_lt n hh⟩,
    isRoot_gaussInitial_unitClassPoly_of_orderTop_eval_pow_ne hq hqt hh hζh P hne⟩)
  omega

/-- `hol:thm:unitorbit` (b): under the hypotheses of the explicit form, `P(q^n)` is eventually
nonzero and its valuation is eventually constant on each residue class modulo `h`. -/
theorem exists_forall_ge_order_eval_pow_residueClass [CharZero K] {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) {h : ℕ} (hh : 0 < h)
    (hζh : q.coeff 0 ^ h = 1) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∃ β : ℕ → Γ, ∃ N : ℕ, ∀ n, N ≤ n →
      P.eval (q ^ n) ≠ 0 ∧ (P.eval (q ^ n)).order = β (n % h) := by
  have hζ := coeff_zero_ne_zero_of_orderTop_eq_zero hq
  have hfin : ∀ r, ∃ b : Γ, (b : WithTop Γ) = unitClassValue q P r := fun r =>
    WithTop.ne_top_iff_exists.mp (inf_orderTop_add_nsmul_ne_top (unitClassPoly_ne_zero hζ hP r) _)
  choose β hβ using hfin
  obtain ⟨N, hN⟩ := exists_forall_ge_orderTop_eval_pow_eq_unitClassValue hq hqt hh hζh P hP
  exact ⟨β, N, fun n hn => ne_zero_and_order_eq_of_orderTop_eq ((hN n hn).trans (hβ _).symm)⟩

end UnitOrbit

section EventualPeriod

variable {α : Type*}

/-- A sequence is eventually periodic with period `p` if `f (n + p) = f n` for all large `n`.
The period `0` is allowed and is trivial. -/
def EventuallyPeriodic (f : ℕ → α) (p : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → f (n + p) = f n

/-- Multiples of an eventual period are eventual periods. -/
theorem EventuallyPeriodic.mul_left {f : ℕ → α} {p : ℕ} (hp : EventuallyPeriodic f p)
    (m : ℕ) : EventuallyPeriodic f (m * p) := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨N, fun n hn => ?_⟩
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, ← add_assoc, hN _ (le_add_right hn), ih]

/-- Differences of eventual periods are eventual periods. -/
theorem EventuallyPeriodic.sub {f : ℕ → α} {p p' : ℕ} (hp : EventuallyPeriodic f p)
    (hp' : EventuallyPeriodic f p') (hle : p ≤ p') : EventuallyPeriodic f (p' - p) := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hp'
  refine ⟨max N M, fun n hn => ?_⟩
  calc f (n + (p' - p)) = f (n + (p' - p) + p) := (hN _ (by omega)).symm
    _ = f (n + p') := by congr 1; omega
    _ = f n := hM n (by omega)

/-- Remainders of eventual periods are eventual periods. -/
theorem EventuallyPeriodic.mod {f : ℕ → α} {m n : ℕ} (hm : EventuallyPeriodic f m)
    (hn : EventuallyPeriodic f n) : EventuallyPeriodic f (n % m) := by
  obtain ⟨c, hc⟩ : ∃ c, c = m * (n / m) := ⟨_, rfl⟩
  have hdiv : c + n % m = n := by rw [hc]; exact Nat.div_add_mod n m
  have hmul : EventuallyPeriodic f c := by
    rw [hc, mul_comm]
    exact hm.mul_left _
  have h := hmul.sub hn (by omega)
  rwa [show n - c = n % m by omega] at h

/-- Eventual periods are closed under `gcd`. -/
theorem EventuallyPeriodic.gcd {f : ℕ → α} {m n : ℕ} (hm : EventuallyPeriodic f m)
    (hn : EventuallyPeriodic f n) : EventuallyPeriodic f (Nat.gcd m n) := by
  revert hm hn
  refine Nat.gcd.induction m n (fun n _ hn => ?_) fun m n _ ih hm hn => ?_
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact ih (hm.mod hn) hm

/-- An eventually periodic sequence has a least positive eventual period, and it divides
every positive eventual period. -/
theorem exists_eventualPeriod_dvd {f : ℕ → α} {p : ℕ} (hp : 0 < p)
    (hper : EventuallyPeriodic f p) : ∃ p₀, 0 < p₀ ∧ EventuallyPeriodic f p₀ ∧
      ∀ p', 0 < p' → EventuallyPeriodic f p' → p₀ ∣ p' := by
  classical
  have hex : ∃ p, 0 < p ∧ EventuallyPeriodic f p := ⟨p, hp, hper⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun p' _ hper' => ?_⟩
  have hpos := (Nat.find_spec hex).1
  have hle := Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left p' hpos,
    (Nat.find_spec hex).2.gcd hper'⟩
  have hge := Nat.gcd_le_left p' hpos
  rw [← le_antisymm hge hle]
  exact Nat.gcd_dvd_right _ _

end EventualPeriod

section UnitOrbitPeriod

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- `hol:thm:unitorbit` (b), period clause: if `ζ^h = 1` with `h > 0`, then `v(P(q^n))` is
eventually `h`-periodic, and its least eventual period divides `h` (and every other eventual
period). The sequence is stated through the `Γ`-valued `HahnSeries.order`, which has the junk
value `0` at zero; it equals `v(P(q^n))` once `P(q^n) ≠ 0`, which holds for all large `n` by
`exists_forall_ge_order_eval_pow_residueClass`, so the two sequences have the same eventual
periods. -/
theorem eventualPeriod_order_eval_pow_dvd [CharZero K] {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) {h : ℕ} (hh : 0 < h)
    (hζh : q.coeff 0 ^ h = 1) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    EventuallyPeriodic (fun n => (P.eval (q ^ n)).order) h ∧
      ∃ p₀, 0 < p₀ ∧ p₀ ∣ h ∧ EventuallyPeriodic (fun n => (P.eval (q ^ n)).order) p₀ ∧
        ∀ p, 0 < p → EventuallyPeriodic (fun n => (P.eval (q ^ n)).order) p → p₀ ∣ p := by
  obtain ⟨β, N, hN⟩ := exists_forall_ge_order_eval_pow_residueClass hq hqt hh hζh P hP
  have hper : EventuallyPeriodic (fun n => (P.eval (q ^ n)).order) h :=
    ⟨N, fun n hn => by
      simp only
      rw [(hN (n + h) (by omega)).2, (hN n hn).2, Nat.add_mod_right]⟩
  obtain ⟨p₀, hp₀, hper₀, hmin⟩ := exists_eventualPeriod_dvd hh hper
  exact ⟨hper, p₀, hp₀, hmin h hh hper, hper₀, hmin⟩

/-- `hol:thm:unitorbit`, first sentence: for `v(q) = 0` with `q` of infinite multiplicative
order and `P ≠ 0`, `v(P(q^n))` is eventually finite and periodic. The statement gives a period
`h > 0` that is `1` when `ζ = res(q)` is not a root of unity (part (a)) and the exact order
`orderOf ζ` otherwise (part (b)), eventual nonvanishing of `P(q^n)`, and eventual
`h`-periodicity of the `Γ`-valued `HahnSeries.order` of `P(q^n)`, which equals `v(P(q^n))`
wherever `P(q^n) ≠ 0`. -/
theorem exists_eventually_periodic_order_eval_pow [CharZero K] {q : K⟦Γ⟧}
    (hq : q.orderTop = 0) (hqt : ¬ IsOfFinOrder q) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∃ h, 0 < h ∧ (IsOfFinOrder (q.coeff 0) → h = orderOf (q.coeff 0)) ∧
      (¬ IsOfFinOrder (q.coeff 0) → h = 1) ∧ (∃ N : ℕ, ∀ n, N ≤ n → P.eval (q ^ n) ≠ 0) ∧
      EventuallyPeriodic (fun n => (P.eval (q ^ n)).order) h := by
  by_cases hζ : IsOfFinOrder (q.coeff 0)
  · have hh := hζ.orderOf_pos
    obtain ⟨β, N, hN⟩ := exists_forall_ge_order_eval_pow_residueClass hq hqt hh
      (pow_orderOf_eq_one _) P hP
    exact ⟨orderOf (q.coeff 0), hh, fun _ => rfl, fun h' => absurd hζ h',
      ⟨N, fun n hn => (hN n hn).1⟩,
      (eventualPeriod_order_eval_pow_dvd hq hqt hh (pow_orderOf_eq_one _) P hP).1⟩
  · obtain ⟨N, hN⟩ := exists_forall_ge_eval_pow_of_not_isOfFinOrder hq hζ P hP
    refine ⟨1, Nat.one_pos, fun h' => absurd h' hζ, fun _ => rfl, ⟨N, fun n hn => (hN n hn).1⟩,
      N, fun n hn => ?_⟩
    simp only
    rw [(hN (n + 1) (by omega)).2, (hN n hn).2]

end UnitOrbitPeriod

section Bivariate

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- `P(x, y) = ∑_k C_k(x) y^k` for `P(U, X) = ∑_k C_k(U) X^k`. -/
theorem evalEval_eq_sum (P : K⟦Γ⟧[X][X]) (x y : K⟦Γ⟧) :
    P.evalEval x y = ∑ k ∈ P.support, (P.coeff k).eval x * y ^ k := by
  have h : Polynomial.eval (Polynomial.C y) P =
      ∑ k ∈ P.support, P.coeff k * Polynomial.C y ^ k := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Polynomial.eval x (Polynomial.eval (Polynomial.C y) P) = _
  rw [h, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]

/-- `hol:lem:bivariate`: let `q ≠ 0` with `λ = v(q) ≠ 0` and `0 ≠ P(U, X) = ∑_k C_k(U) X^k`.
There are `β ∈ Γ` and `k, N ∈ ℕ` with `P(n, q^n) ≠ 0` and `v(P(n, q^n)) = β + k n λ` for all
`n ≥ N`. The proof gives `C_k ≠ 0` and `β = β(C_k)`. The coefficient field has characteristic
zero, as `hol:lem:integer` requires. -/
theorem exists_eventually_order_evalEval [CharZero K] (q : K⟦Γ⟧) (hq : q ≠ 0)
    (hlam : q.order ≠ 0) (P : K⟦Γ⟧[X][X]) (hP : P ≠ 0) :
    ∃ (β : Γ) (k N : ℕ), ∀ n, N ≤ n → P.evalEval (n : K⟦Γ⟧) (q ^ n) ≠ 0 ∧
      (P.evalEval (n : K⟦Γ⟧) (q ^ n)).order = β + (k * n) • q.order := by
  have hint : ∀ k : ℕ, ∃ b : Γ, ∃ N : ℕ, k ∈ P.support → ∀ n, N ≤ n →
      (P.coeff k).eval (n : K⟦Γ⟧) ≠ 0 ∧ ((P.coeff k).eval (n : K⟦Γ⟧)).order = b := by
    intro k
    by_cases hk : k ∈ P.support
    · obtain ⟨N, hN⟩ := exists_forall_ge_eval_natCast (P.coeff k)
        (Polynomial.mem_support_iff.mp hk)
      exact ⟨_, N, fun _ => hN⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose b N' hN' using hint
  have ht : ∀ k ∈ P.support, ∀ n, P.support.sup N' ≤ n →
      (P.coeff k).eval (n : K⟦Γ⟧) * (q ^ n) ^ k ≠ 0 ∧
        ((P.coeff k).eval (n : K⟦Γ⟧) * (q ^ n) ^ k).order = b k + (k * n) • q.order := by
    intro k hk n hn
    obtain ⟨h0, hord⟩ := hN' k hk n ((Finset.le_sup hk).trans hn)
    have hpow : (q ^ n) ^ k ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hq)
    refine ⟨mul_ne_zero h0 hpow, ?_⟩
    rw [order_mul h0 hpow, hord, ← pow_mul, order_pow, mul_comm n k]
  obtain ⟨k, -, N, hN⟩ := exists_eventually_order_sum_affine P.support
    (Polynomial.support_nonempty.mpr hP) (fun k n => (P.coeff k).eval (n : K⟦Γ⟧) * (q ^ n) ^ k)
    b hlam _ ht
  refine ⟨b k, k, N, fun n hn => ?_⟩
  rw [evalEval_eq_sum]
  exact hN n hn

end Bivariate

end

end Surreal.HolonomicOrbit
