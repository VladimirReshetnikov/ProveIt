import New.Endgame.PrimeError
import Lib.Analytic.QuadraticTwist.ZeroFreeTwist

/-! A good second scale in every long window. If E and E' are O(e^v) and their transforms
∫E(v)e^((1−s)v)dv continue with no pole in Re s ≥ 1, then for large t and any X in [0, e^t] some u
in [t, t²] has E(u) − X E'(u) ≤ e^(−t), which replaces a pointwise prime number theorem in
progressions when the second scale of (⋆) is chosen. Localised one-sided bounds and sign changes for
prime-sum errors are known. Related work: Pintz, On the sign changes of π(x) − li(x), 1976–78;
Kaczorowski, On sign-changes in the remainder-term of the prime-number formula, 1984.

One-sided bound for non-split primes gives a zero-free half-plane. If β > 1/2 and, for every prime d
of a unit class mod M forcing d ≡ 7 mod 8, the normalised error at x in the weighted count of
primes ≡ 1 mod M not split in Q(√−d) is eventually ≤ x^(β−1), then L(s,χ) has no zero in Re s > β
for χ mod M, and this takes (⋆) to GRH. It is known that a one-sided bound for a weighted sum over
primes 1 mod q gives a zero-free half-plane if there are no real zeros. Related work: M. Suzuki, On
variants of Chebyshev's conjecture, arXiv 2411.07436, 2024; Montgomery–Vaughan, Multiplicative
Number Theory I, §15.1–15.2, 2007; Landau, Über einen Satz von Tschebyschef, 1905.

This file: One-sided bound gives a zero-free half-plane; small value in every long window. -/

open Complex Filter Nat Real Set MeasureTheory Topology

/-- One-sided criterion: let β > 1/2 and a be a unit mod M such that every prime d ≡ a is ≡ 7 mod 8,
prime to M, with R_M(x) ≤ x^{β−1} for large x (`primeError`). Then `entireL` χ has no zero in Re
s > β for any χ mod M.

One-sided bound for non-split primes gives a zero-free half-plane. -/
lemma entireL_ne_zero_of_primeError_le {M} [NeZero M] {a : ZMod M} {β} (hβ : 1 / 2 < β)
  (ha : IsUnit a) (h : ∀ d : Primes, d = a → (d.1 % 8 = 7 ∧ M.Coprime d) ∧ ∀ᶠ x in atTop, primeError
  d M x ≤ x ^ (β - 1)) ρ (hρ : β < ρ.re) (χ : DirichletCharacter ℂ M) : entireL χ ρ ≠ 0 := by
  let ⟨d, e, hZ⟩ := exists_entireL_quadTwist_ne_zero |ρ.im| hβ ha (by grind)
  use by_cases (entireL_ne_zero χ) (flip ?_ (((h d e).1.elim isPolar_primeError).landau (by bound)
    (le_total · 1 |>.rec ?_ ?_) (.mono (tendsto_exp_atTop (h d e).2) (by simp [exp_mul, mul_comm]))
    hρ)) <;> simp +contextual (maxDischargeDepth := 3) [le_of_lt, div_re,
    (tendsto_sub_mul_logDeriv_entireL _).1.2, *, normSq, entireL_ne_zero, (hβ.trans hρ).trans',
    ← cast_sum, tendsto_sub_mul_logDeriv_entireL, ne_of_apply_ne re, ne_of_gt]; bound

/-- For polar E, all R > 3 close to 3 and then all large t: |E(v)| ≤ t e^v for v ≥ 0, and for
every k the function v^k e^{−3v} E(v) is integrable on (0, ∞) with integral of modulus ≤ k!
t / R^k. -/
lemma IsPolar.eventually_moment_le {E r} (h : IsPolar E r) : ∀ᶠ R in 𝓝[>] 3, ∀ᶠ t in atTop,
    (∀ v ≥ 0, |E v| ≤ t * v.exp) ∧ ∀ k, let F v := v ^ k * (-3 * v).exp * E v
  IntegrableOn F (Ioi 0) ∧ |∫ v in Ioi 0, F v| ≤ k ! * t / R ^ k := h.elim fun m ⟨C, Φ, _, hC, e,
      A, _⟩ ↦ ((isCompact_closedBall (1 + 3) 3).exists_thickening_subset_open (isOpen_analyticAt ..)
      (A · <| by simpa using (re_le_norm _).trans ·)).elim fun ε ⟨o, D⟩ ↦ by
  filter_upwards [Ioo_mem_nhdsGT (by bound : 3 < ε + 3)] with R ⟨a, b⟩
  simp [o] at D
  -- differentiation under the integral sign
  have J k : ∀ s, 2 < re s → let F v := (-v) ^ k * E v * ((1 - s) * v).exp
    IntegrableOn F (Ioi 0) ∧ iteratedDeriv k Φ s = ∫ v in Ioi 0, F v := by
    induction' k with k ih <;> intro s hs; simp [integrableOn_laplace_of_abs_le m hC, *]
    obtain ⟨⟨ε, o, q⟩, n⟩ := exists_pos_mul_lt (sub_pos.2 hs) 2, (isOpen_re_gt _).mem_nhds hs
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le ((isOpen_re_gt _).mem_nhds
      (lt_tsub_iff_right.1 q)) (.mono n (ih · · |>.1.1)) (ih s hs).1 (by fun_prop) (.mono
      (self_mem_ae_restrict (by simp)) fun v u z j ↦ ?_) ((ih (ε + 2) (by simpa)).1.norm.div_const
      ε) (.of_forall fun v z _ ↦ ((hasDerivAt_mul_const _).cexp.const_mul _).comp_const_sub ..)
    · simpa [iteratedDeriv_succ, pow_succ, ← mul_assoc, mul_right_comm] using! this.imp id
        (·.congr_of_eventuallyEq (.mono n (ih · · |>.2)) |>.deriv)
    simp [abs_of_pos, le_div_iff₀, mul_assoc, *]
    grw [← j.out, lt_add_one (v * ε), add_one_le_exp, ← Real.exp_add]; bound
  filter_upwards [mem_atTop C, mem_atTop (tsum _)] with t c d
  use (by grw [hC · ·, c]), fun k ↦ (J k 4 (by norm_num)).rec fun i j ↦ (?_ : _ ∧ _)
  grw [← d,
    ← (summable_taylor_of_removable (1 + 3 + R) D (by simp; grind)).norm.le_tsum k (by bound)]
  norm_num [j, neg_pow (ofReal _), mul_assoc, integrable_const_mul_iff, IntegrableOn,
    mul_comm (ofReal _)] at i ⊢
  use mod_cast i.re, mod_cast by simp [field]; bound

/-- If E and E' are polar (`IsPolar`), then for all large t and every X in [0, e^t] there is u in
[t, t²] with E(u) − X E'(u) ≤ e^{−t}.

A good second scale in every long window. -/
lemma IsPolar.exists_window_sub_mul_le {E r E' r'} (h : IsPolar E r) (h' :
  IsPolar E' r') : ∀ᶠ t in atTop, ∀ X ∈ Icc 0
  t.exp, ∃ u ∈ Icc t (t ^ 2), E u - X * E' u ≤ (-t).exp := (h.eventually_moment_le.and
  (h'.eventually_moment_le.and (Ioo_mem_nhdsGT (lt_add_one _)))).exists.elim fun R ⟨c, d, p, q⟩ ↦ by
  simp_rw [IntegrableOn, abs_le, forall_and] at *
  filter_upwards [c, d, mem_atTop (99 / (R.log - .log 3)), mem_atTop 9]
    with t ⟨c, _, a⟩ ⟨d, _, b⟩ u _ X ⟨_, _⟩
  let k := ⌈t ^ 2 / 9⌉₊
  obtain ⟨w, I, K : t + t * X + 1 ≤ t.exp * t.exp⟩ := three_pos.trans p,
    mod_cast fun R : ℝ ↦ (@laplace_pow R · k), by nlinarith [t.add_one_le_exp]
  have J R o := Integrable.of_integral_ne_zero ((I R o).trans_ne (by simp; grind))
  by_contra! N
  -- `E - X E' - e^{-t}` plus two exponentials, which dominate outside the window, is `≥ 0`
  have : 0 ≤ ∫ v in Ioi 0, v ^ k * ((-R * v).exp * (7 * t).exp + (-1 * v).exp *
    (2 * t - t ^ 2).exp + (-3 * v).exp * (E v - _ * X - (-t).exp)) := setIntegral_nonneg
    (by simp) fun v (l : 0 < v) ↦ mul_nonneg (by bound) (by_cases (by bound [N v ·]) fun x ↦ ?_)
  -- but in the mean with `k ≈ t²/9` three terms are each at most a third of the negative one
  · simp (disch := first | fun_prop (disch := simp [w]) | simp [*]) [mul_add, mul_sub, ← mul_assoc,
      integral_add, integral_sub, I, -neg_mul] at this
    grw [a.2, ← b.1, (by ring : _ - _ * X = k ! * (t + t * X) / R ^ k), lt_add_one (t + _), K,
      add_sub, sub_pos] at this
    apply this.not_ge ((add_le_add_three ..).trans_eq (add_thirds _)) <;>
    simp (disch := positivity) [← log_le_log_iff] <;> nlinarith [log_three_lt_d9,
      abs_le.1 (abs_sub_ceil_le (by bound : 0 ≤ t ^ 2 / 9)), (div_le_iff₀ (by bound)).1 u]
  grw [← neg_le_iff_add_nonneg, ← c.1, d.2, (by grind : -t ≤ v), (by ring : -_ = (-3 * v).exp *
    v.exp * (t + t * X + 1)), K, ← max_le_add_of_nonneg] <;> simp [← Real.exp_add, exp_nonneg, l.le]
  contrapose! x; use ?_ <;> nlinarith
