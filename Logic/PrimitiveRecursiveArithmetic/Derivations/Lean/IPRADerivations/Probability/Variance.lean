import IPRADerivations.Probability.TailSum

/-!
# Variance, squared error and the sample mean

Packet: `probability/expected_value_ipra_2026-11-16`, Sections 5 and 8 (`thm:variance-identity`,
`thm:mean-minimizes`, `thm:sample-mean`), for a weight body `w(i, x)` on outcomes `i < N` and a
natural-valued observable `X(i, x)`. With `W = ∑ w_i`, `S = ∑ w_i X_i` and `Q = ∑ w_i X_i²`, the
deviation `X − S/W` is cleared to the natural number `|W X_i − S|`, where
`|a − b| = (a ∸ b) + (b ∸ a)`.

* `ad_sq`: `|a − b|² + 2ab = a² + b²`;
* `dev_sum`: for arbitrary `A`, `B`,
  `∑ w_i |A X_i − B|² + 2AB · S = A² · Q + B² · W`, by induction on `N`;
* `variance_identity` (`thm:variance-identity`): `∑ w_i |W X_i − S|² + W S² = W² Q`, i.e.
  `W² Var(X) = W Q − S²`;
* `mean_square_decomp`, `mean_minimizes` (`thm:mean-minimizes`): for a rational `a = p/q`,
  `W² ∑ w_i |q X_i − p|² = q² ∑ w_i |W X_i − S|² + W |q S − p W|²`, so the mean minimizes the
  squared error;
* `second_moment_add` (`thm:variance-identity`): `Ew((X+Y)²) = Ew(X²) + 2 Ew(XY) + Ew(Y²)`;
* `sum_one`, `sum_const_of`: `∑_{j<N} 1 = N` and `∑_{j<N} m = N m`;
* `sample_mean` (`thm:sample-mean`): if every column `∑_{i<M} a(i, j)` of a double sum is `m`,
  the double sum over `j < r` is `r m`; with `a(i, j) = w_i X_j(i)` this is `r E[X̄] = r μ`,
  with no independence assumption.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Variance

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add' mul_one' exp_add)
open LeanProofs.IPRA.Probability.Independence (sum_scale dsum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The absolute difference -/

/-- `|a − b| = (a ∸ b) + (b ∸ a)`. -/
abbrev ad (a b : PTm n) : PTm n := monus a b + monus b a

theorem ad_sq_of_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] ad a b * ad a b + (a * b + a * b) ≐ a * a + b * b := by
  ipra_lc (Groth.ι (IPRA.Q.mk Γ (monus a b)) + 2 * Groth.ι (IPRA.Q.mk Γ (monus b a))) * natEq h -
    (Groth.ι (IPRA.Q.mk Γ (monus b a)) + Groth.ι (IPRA.Q.mk Γ b) - Groth.ι (IPRA.Q.mk Γ a)) * natEq (eq_add_of_le h)

/-- `|a − b|² + 2ab = a² + b²`. -/
theorem ad_sq (a b : PTm n) : Γ ⊢[PRAAx] ad a b * ad a b + (a * b + a * b) ≐ a * a + b * b := by
  refine .orE (le_total a b) (ad_sq_of_le Prf.hyp0) ?_
  ipra_lc natEq (ad_sq_of_le (a := b) (b := a) (Γ := le b a :: Γ) Prf.hyp0)

/-! ## The squared-deviation sum -/

section Dev

variable (w X : PTm 2)

/-- `w(i, x) · |A X(i, x) − B|²`, with the parameter `⟨A, ⟨B, x⟩⟩`. -/
def dvB : PTm 2 :=
  Syn.subst ![var 0, sndT (sndT (var 1))] w *
    ((monus (fstT (var 1) * Syn.subst ![var 0, sndT (sndT (var 1))] X) (fstT (sndT (var 1))) +
        monus (fstT (sndT (var 1))) (fstT (var 1) * Syn.subst ![var 0, sndT (sndT (var 1))] X)) *
      (monus (fstT (var 1) * Syn.subst ![var 0, sndT (sndT (var 1))] X) (fstT (sndT (var 1))) +
        monus (fstT (sndT (var 1))) (fstT (var 1) * Syn.subst ![var 0, sndT (sndT (var 1))] X)))

theorem inst2_dvB (i y : PTm n) :
    inst2 (dvB w X) i y = inst2 w i (sndT (sndT y)) *
      (ad (fstT y * inst2 X i (sndT (sndT y))) (fstT (sndT y)) *
        ad (fstT y * inst2 X i (sndT (sndT y))) (fstT (sndT y))) := by
  have e : ∀ f : PTm 2, Syn.subst ![i, y] (Syn.subst ![var 0, sndT (sndT (var 1))] f) =
      Syn.subst ![i, sndT (sndT y)] f := fun f => by
    rw [Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, dvB, ad, PTm.subst_mul, PTm.subst_add, PTm.subst_monus, subst_fstT, subst_sndT, e]
  simp

theorem dv_pt (i A B x : PTm n) :
    Γ ⊢[PRAAx] inst2 (dvB w X) i (pairT A (pairT B x)) ≐
      inst2 w i x * (ad (A * inst2 X i x) B * ad (A * inst2 X i x) B) := by
  rw [inst2_dvB]
  have hA : Γ ⊢[PRAAx] fstT (pairT A (pairT B x)) ≐ A := fst_pair _ _
  have hB : Γ ⊢[PRAAx] fstT (sndT (pairT A (pairT B x))) ≐ B := (snd_pair _ _).fstE
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT A (pairT B x))) ≐ x := (snd_pair _ _).sndE
  have ht := congrMul hA (congrInst2 X (.eqRefl i) hx)
  have hD := congrAdd (congrMonus ht hB) (congrMonus hB ht)
  exact congrMul (congrInst2 w (.eqRefl i) hx) (congrMul hD hD)

/-- `D(N) = ∑_{i<N} w_i |A X_i − B|²`. -/
abbrev dS (N A B x : PTm n) : PTm n := ap2 (sumF (dvB w X)) N (pairT A (pairT B x))

theorem dv_base (A B x : PTm n) :
    Γ ⊢[PRAAx] dS w X zero A B x + (A * B + A * B) * ap2 (sumF (w * X)) zero x ≐
      A * A * ap2 (sumF (w * (X * X))) zero x + B * B * ap2 (sumF w) zero x :=
  (congrAdd (sum_zero _ _) ((congrMul (.eqRefl _) (sum_zero _ _)).eqTrans (mul_zero _))).eqTrans
    ((add_zero _).eqTrans (.eqSymm ((congrAdd ((congrMul (.eqRefl _) (sum_zero _ _)).eqTrans (mul_zero _))
      ((congrMul (.eqRefl _) (sum_zero _ _)).eqTrans (mul_zero _))).eqTrans (add_zero _))))

theorem dv_step {N A B x : PTm n}
    (ih : Γ ⊢[PRAAx] dS w X N A B x + (A * B + A * B) * ap2 (sumF (w * X)) N x ≐
      A * A * ap2 (sumF (w * (X * X))) N x + B * B * ap2 (sumF w) N x) :
    Γ ⊢[PRAAx] dS w X (succ N) A B x + (A * B + A * B) * ap2 (sumF (w * X)) (succ N) x ≐
      A * A * ap2 (sumF (w * (X * X))) (succ N) x + B * B * ap2 (sumF w) (succ N) x := by
  have s0 := natEq ((sum_succ' (Γ := Γ) (dvB w X) N (pairT A (pairT B x))).eqTrans
    (congrAdd (.eqRefl _) (dv_pt w X N A B x)))
  have e1 := sum_succ' (Γ := Γ) (w * X) N x
  rw [inst2_mul'] at e1
  have e2 := sum_succ' (Γ := Γ) (w * (X * X)) N x
  rw [inst2_mul', inst2_mul'] at e2
  ipra_lc natEq ih + s0 +
    (Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ B) + Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ B)) * natEq e1 -
    Groth.ι (IPRA.Q.mk Γ A) * Groth.ι (IPRA.Q.mk Γ A) * natEq e2 -
    Groth.ι (IPRA.Q.mk Γ B) * Groth.ι (IPRA.Q.mk Γ B) * natEq (sum_succ' (Γ := Γ) w N x) +
    Groth.ι (IPRA.Q.mk Γ (inst2 w N x)) * natEq (ad_sq (Γ := Γ) (A * inst2 X N x) B)

/-- Variables: `0 = N`, `1 = A`, `2 = B`, `3 = x`. -/
private abbrev dvF : Fm PTm 4 :=
  dS w X (var 0) (var 1) (var 2) (var 3) + (var 1 * var 2 + var 1 * var 2) * ap2 (sumF (w * X)) (var 0) (var 3) ≐
    var 1 * var 1 * ap2 (sumF (w * (X * X))) (var 0) (var 3) + var 2 * var 2 * ap2 (sumF w) (var 0) (var 3)

private theorem dv₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] dvF w X := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact dv_base w X _ _ _
  · exact dv_step w X Prf.hyp0

/-- `∑_{i<N} w_i |A X_i − B|² + 2AB · Ew(X) = A² · Ew(X²) + B² · W`. -/
theorem dev_sum (N A B x : PTm n) :
    Γ ⊢[PRAAx] dS w X N A B x + (A * B + A * B) * Ew w X N x ≐
      A * A * Ew w (X * X) N x + B * B * Wt w N x := by
  have h := inst (Γ := Γ) (dv₀ w X) (![N, A, B, x] : Fin 4 → PTm n)
  simpa using h

/-! ## Variance and squared error -/

/-- `W² Var(X)`, as `∑_{i<N} w_i |W X_i − S|²`. -/
abbrev Vr (N x : PTm n) : PTm n := dS w X N (Wt w N x) (Ew w X N x) x

/-- `thm:variance-identity`: `∑ w_i |W X_i − S|² + W S² = W² Q`. -/
theorem variance_identity (N x : PTm n) :
    Γ ⊢[PRAAx] Vr w X N x + Wt w N x * (Ew w X N x * Ew w X N x) ≐
      Wt w N x * Wt w N x * Ew w (X * X) N x := by
  ipra_lc natEq (dev_sum (Γ := Γ) w X N (Wt w N x) (Ew w X N x) x)

/-- `thm:mean-minimizes`: for `a = p / q`,
`W² ∑ w_i |q X_i − p|² = q² ∑ w_i |W X_i − S|² + W |q S − p W|²`. -/
theorem mean_square_decomp (N p q x : PTm n) :
    Γ ⊢[PRAAx] Wt w N x * Wt w N x * dS w X N q p x ≐
      q * q * Vr w X N x +
        Wt w N x * (ad (q * Ew w X N x) (p * Wt w N x) * ad (q * Ew w X N x) (p * Wt w N x)) := by
  ipra_lc Groth.ι (IPRA.Q.mk Γ (ap2 (sumF w) N x)) * Groth.ι (IPRA.Q.mk Γ (ap2 (sumF w) N x)) * natEq (dev_sum (Γ := Γ) w X N q p x) -
    Groth.ι (IPRA.Q.mk Γ q) * Groth.ι (IPRA.Q.mk Γ q) * natEq (variance_identity (Γ := Γ) w X N x) -
    Groth.ι (IPRA.Q.mk Γ (ap2 (sumF w) N x)) * natEq (ad_sq (Γ := Γ) (q * Ew w X N x) (p * Wt w N x))

/-- The mean minimizes the squared error: `q² · W² Var(X) ≤ W² · ∑ w_i |q X_i − p|²`. -/
theorem mean_minimizes (N p q x : PTm n) :
    Γ ⊢[PRAAx] le (q * q * Vr w X N x) (Wt w N x * Wt w N x * dS w X N q p x) :=
  le_of_eq_add (mean_square_decomp w X N p q x)

end Dev

/-- `Ew((X + Y)²) = Ew(X²) + 2 Ew(X Y) + Ew(Y²)`. -/
theorem second_moment_add (w X Y : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] Ew w ((X + Y) * (X + Y)) N x ≐
      Ew w (X * X) N x + (Ew w (X * Y) N x + Ew w (X * Y) N x) + Ew w (Y * Y) N x := by
  refine (sum_congr_bounded (w * ((X + Y) * (X + Y))) (w * (X * X + (X * Y + X * Y) + Y * Y)) x x N
    (.allI (.impI ?_))).eqTrans ((exp_add w (X * X + (X * Y + X * Y)) (Y * Y) N x).eqTrans
      (congrAdd ((exp_add w (X * X) (X * Y + X * Y) N x).eqTrans
        (congrAdd (.eqRefl _) (exp_add w (X * Y) (X * Y) N x))) (.eqRefl _)))
  ipra_lc [inst2_mul', inst2_add']

/-! ## Constant sums and the sample mean -/

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev oneF : Fm PTm 2 := ap2 (sumF (one : PTm 2)) (var 0) (var 1) ≐ var 0

private theorem sum_one₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] oneF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (succ_eq_add_one _).eqSymm)
    have e : inst2 (one : PTm 2) (var 0 : PTm 2) (var 1) = one := by simp [inst2]
    rw [e]
    exact .eqRefl _

/-- `∑_{j<N} 1 = N`. -/
theorem sum_one (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (one : PTm 2)) N x ≐ N := by
  have h := inst (Γ := Γ) sum_one₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

/-- If `h(j, y) = m` for `j < N`, then `∑_{j<N} h(j, y) = N · m`. -/
theorem sum_const_of (h : PTm 2) (N m y : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 h (var 0) (Syn.shift y) ≐ Syn.shift m))) :
    Γ ⊢[PRAAx] ap2 (sumF h) N y ≐ N * m := by
  exact (sum_congr_bounded h (var 1 : PTm 2) y m N (by simpa [inst2] using hp)).eqTrans (sum_const_param N m)

/-- `thm:sample-mean`: if each column `∑_{i<M} a(i, j, x)` with `j < r` equals `m`, then
`∑_{i<M} ∑_{j<r} a(i, j, x) = r · m`. For `a(i, j) = w_i X_j(i)` with every `Ew(X_j) = m`, this is
the unbiased sample mean in the cross-multiplied form `r E[X̄] = r μ`. -/
theorem sample_mean (a : PTm 3) {M r m x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift r) ⟶
      (ap2 (sumF (colB a)) (Syn.shift M) (pairT (var 0) (Syn.shift x)) ≐ Syn.shift m))) :
    Γ ⊢[PRAAx] dsum a M r x ≐ r * m := by
  refine (fubini a M r x).eqTrans (sum_const_of (pB a) r m (pairT M x) (.allI (.impI ?_)))
  rw [shift_pairT, inst2_pB]
  exact (congrAp2 (sumF (colB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
    (Prf.impE h.allOpen.wk Prf.hyp0)

end LeanProofs.IPRA.Probability.Variance
