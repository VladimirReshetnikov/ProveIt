import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.DiophantineNumberTheory.Hurwitz

/-!
# The finite kernel of expectation

Packet: `probability/expected_value_ipra_2026-11-16` (Sections 3, 5 and 6: the exact finite kernel).
A finite weighted law is a weight body `w(i, x) ≥ 0` on outcomes `i < N` (with a parameter `x`);
an observable is a body `X(i, x)` with natural values. The expectation is `E[X] = Ew / W` with

  `W = ∑_{i<N} w_i`,   `Ew(X) = ∑_{i<N} w_i X_i`,

and every statement is cross-multiplied by `W`, so no division occurs:

* `exp_add` (linearity): `Ew(X + Y) = Ew(X) + Ew(Y)`; scaling by a constant is `sum_mul_param`;
* `exp_mono` (monotonicity): `X ≤ Y` on outcomes gives `Ew(X) ≤ Ew(Y)`;
* `exp_lower`, `exp_upper` (`thm:convex-hull`): `c ≤ X_i` gives `c W ≤ Ew(X)`, and dually;
* `prob_le` (`thm:normalization`): an indicator `A ≤ 1` has `∑ w_i A_i ≤ W`;
* `markov` (`thm:markov`): `c · ∑ w_i [X_i ≥ c] ≤ Ew(X)`;
* `chebyshev` (`thm:chebyshev`, power-Markov form): `c² · ∑ w_i [D_i ≥ c] ≤ Ew(D²)`;
* `cauchy_schwarz`: `Ew(XY)² ≤ Ew(X²) · Ew(Y²)`;
* `second_moment`: `Ew(X)² ≤ Ew(X²) · W`, i.e. the variance `W·Q − S²` is nonnegative.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Expectation

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le mulParam inst2_mulParam sum_mul_param)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem inst2_mul' (f g : PTm 2) (i x : PTm n) : inst2 (f * g) i x = inst2 f i x * inst2 g i x := by
  simp [inst2]

theorem inst2_add' (f g : PTm 2) (i x : PTm n) : inst2 (f + g) i x = inst2 f i x + inst2 g i x := by
  simp [inst2]

/-- `Ew(X) = ∑_{i<N} w_i X_i`. -/
abbrev Ew (w X : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF (w * X)) N x

/-- `W = ∑_{i<N} w_i`. -/
abbrev Wt (w : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF w) N x

/-! ## Linearity and monotonicity -/

/-- `Ew(X + Y) = Ew(X) + Ew(Y)`. -/
theorem exp_add (w X Y : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] Ew w (X + Y) N x ≐ Ew w X N x + Ew w Y N x := by
  refine (sum_congr_bounded (w * (X + Y)) (addBody (w * X) (w * Y)) x x N (.allI (.impI ?_))).eqTrans
    (sum_add (w * X) (w * Y) N x)
  rw [inst2_addBody, inst2_mul', inst2_mul', inst2_mul', inst2_add']
  ipra_ring

/-- `X ≤ Y` pointwise gives `Ew(X) ≤ Ew(Y)`. -/
theorem exp_mono (w X Y : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 X (var 0) (Syn.shift x)) (inst2 Y (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (Ew w X N x) (Ew w Y N x) := by
  refine sum_le (w * X) (w * Y) x N (.allI (.impI ?_))
  rw [inst2_mul', inst2_mul']
  exact le_mul_mono (le_refl _) (Prf.impE h.allOpen.wk Prf.hyp0)

/-- `c ≤ X_i` on the outcomes gives `c · W ≤ Ew(X)` (`c` is read from the parameter). -/
theorem exp_lower (c : PTm 1) (w X : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.subst ![Syn.shift x] c) (inst2 X (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (Syn.subst ![x] c * Wt w N x) (Ew w X N x) := by
  refine le_congr (sum_mul_param c w N x) (.eqRefl _) (sum_le (mulParam c w) (w * X) x N (.allI (.impI ?_)))
  rw [inst2_mulParam, inst2_mul']
  exact le_congr (mul_comm _ _) (.eqRefl _) (le_mul_mono (le_refl _) (Prf.impE h.allOpen.wk Prf.hyp0))

/-- `X_i ≤ c` on the outcomes gives `Ew(X) ≤ c · W`. -/
theorem exp_upper (c : PTm 1) (w X : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 X (var 0) (Syn.shift x)) (Syn.subst ![Syn.shift x] c))) :
    Γ ⊢[PRAAx] le (Ew w X N x) (Syn.subst ![x] c * Wt w N x) := by
  refine le_congr (.eqRefl _) (sum_mul_param c w N x) (sum_le (w * X) (mulParam c w) x N (.allI (.impI ?_)))
  rw [inst2_mulParam, inst2_mul']
  exact le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl _) (Prf.impE h.allOpen.wk Prf.hyp0))

alias mul_one' := Common.mul_one_right

/-- `A_i ≤ 1` gives `∑ w_i A_i ≤ W`: probabilities are at most one. -/
theorem prob_le (w A : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 A (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] le (Ew w A N x) (Wt w N x) := by
  refine sum_le (w * A) w x N (.allI (.impI ?_))
  rw [inst2_mul']
  exact le_congr (.eqRefl _) (mul_one' _) (le_mul_mono (le_refl _) (Prf.impE h.allOpen.wk Prf.hyp0))

/-! ## Markov and Chebyshev -/

/-- The indicator `[X ≥ a]`. -/
abbrev geI (a X : PTm n) : PTm n := monus one (monus a X)

theorem geI_true {a X : PTm n} (h : Γ ⊢[PRAAx] le a X) : Γ ⊢[PRAAx] geI a X ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem geI_false {a X : PTm n} (h : Γ ⊢[PRAAx] lt X a) : Γ ⊢[PRAAx] geI a X ≐ zero := by
  have e : Γ ⊢[PRAAx] a ≐ X + succ (monus a (succ X)) := (eq_add_of_le h).eqTrans (by ipra_ring)
  exact (congrMonus (.eqRefl _) ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans
    ((succ_monus_succ _ _).eqTrans (zero_monus _))

alias le_zero_of := Common.le_of_eq_zero

/-- `a · w [X ≥ a] ≤ w X`. -/
theorem markov_pt (a w X : PTm n) : Γ ⊢[PRAAx] le (a * (w * geI a X)) (w * X) :=
  .orE (lt_or_le X a)
    (le_zero_of ((congrMul (.eqRefl _) ((congrMul (.eqRefl _) (geI_false Prf.hyp0)).eqTrans (mul_zero _))).eqTrans
      (mul_zero _)))
    (le_congr ((congrMul (.eqRefl a) ((congrMul (.eqRefl w) (geI_true Prf.hyp0)).eqTrans (mul_one' _))).eqTrans
        (mul_comm _ _)).eqSymm (.eqRefl _)
      (le_mul_mono (le_refl w) Prf.hyp0))

/-- `a² · w [D ≥ a] ≤ w D²`. -/
theorem chebyshev_pt (a w D : PTm n) : Γ ⊢[PRAAx] le (a * a * (w * geI a D)) (w * (D * D)) :=
  .orE (lt_or_le D a)
    (le_zero_of ((congrMul (.eqRefl _) ((congrMul (.eqRefl _) (geI_false Prf.hyp0)).eqTrans (mul_zero _))).eqTrans
      (mul_zero _)))
    (le_congr ((congrMul (.eqRefl (a * a)) ((congrMul (.eqRefl w) (geI_true Prf.hyp0)).eqTrans (mul_one' _))).eqTrans
        (mul_comm _ _)).eqSymm (.eqRefl _)
      (le_mul_mono (le_refl w) (sq_le_sq Prf.hyp0)))

/-- The indicator body `[X_i ≥ c]`, with the threshold `c` read from the parameter. -/
abbrev geB (c : PTm 1) (X : PTm 2) : PTm 2 := monus one (monus (Syn.subst ![var 1] c) X)

theorem inst2_geB (c : PTm 1) (X : PTm 2) (i x : PTm n) :
    inst2 (geB c X) i x = geI (Syn.subst ![x] c) (inst2 X i x) := by
  have e := inst2_mulParam c X i x
  simp only [inst2, mulParam, PTm.subst_mul] at e
  simp only [inst2, geB, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  have e' : Syn.subst ![i, x] (Syn.subst ![var 1] c) = Syn.subst ![x] c := by
    rw [Syn.subst_subst]; congr 1; funext j; fin_cases j; rfl
  rw [e']

/-- `thm:markov`: `c · ∑ w_i [X_i ≥ c] ≤ ∑ w_i X_i`. -/
theorem markov (c : PTm 1) (w X : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] le (Syn.subst ![x] c * Ew w (geB c X) N x) (Ew w X N x) := by
  refine le_congr (sum_mul_param c (w * geB c X) N x) (.eqRefl _)
    (sum_le (mulParam c (w * geB c X)) (w * X) x N (.allI (.impI ?_)))
  rw [inst2_mulParam, inst2_mul', inst2_mul', inst2_geB]
  exact markov_pt _ _ _

/-- `thm:chebyshev` in power-Markov form: `c² · ∑ w_i [D_i ≥ c] ≤ ∑ w_i D_i²`. -/
theorem chebyshev (c : PTm 1) (w D : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] le (Syn.subst ![x] (c * c) * Ew w (geB c D) N x) (Ew w (D * D) N x) := by
  refine le_congr (sum_mul_param (c * c) (w * geB c D) N x) (.eqRefl _)
    (sum_le (mulParam (c * c) (w * geB c D)) (w * (D * D)) x N (.allI (.impI ?_)))
  rw [inst2_mulParam, inst2_mul', inst2_mul', inst2_mul', inst2_geB]
  have e : Syn.subst ![Syn.shift x] (c * c) = Syn.subst ![Syn.shift x] c * Syn.subst ![Syn.shift x] c := by simp
  rw [e]
  exact chebyshev_pt _ _ _

/-! ## Cauchy–Schwarz -/

theorem four_mul_le_of {u v e : PTm n} (h : Γ ⊢[PRAAx] v ≐ u + e) :
    Γ ⊢[PRAAx] le (two * two * (u * v)) ((u + v) * (u + v)) := by
  refine le_of_eq_add (d := e * e) ?_
  ipra_lc (Groth.ι (IPRA.Q.mk Γ v) - Groth.ι (IPRA.Q.mk Γ u) + Groth.ι (IPRA.Q.mk Γ e)) * natEq h

/-- `4uv ≤ (u + v)²`. -/
theorem four_mul_le (u v : PTm n) : Γ ⊢[PRAAx] le (two * two * (u * v)) ((u + v) * (u + v)) :=
  .orE (lt_or_le v u)
    (le_congr (congrMul (.eqRefl _) (mul_comm _ _)) (congrMul (add_comm _ _) (add_comm _ _))
      (four_mul_le_of (eq_add_of_le (le_of_lt Prf.hyp0))))
    (four_mul_le_of (eq_add_of_le Prf.hyp0))

/-- `P² ≤ uv → 2P ≤ u + v`. -/
theorem two_mul_le {P u v : PTm n} (h : Γ ⊢[PRAAx] le (P * P) (u * v)) : Γ ⊢[PRAAx] le (two * P) (u + v) := by
  refine le_of_sq_le (le_trans (le_congr ?_ (.eqRefl _) (le_mul_mono (le_refl (two * two)) h)) (four_mul_le u v))
  ipra_ring

/-- The step: adding one outcome of weight `w` and values `a`, `b`. -/
theorem cs_step {Sxy Sxx Syy w a b : PTm n} (ih : Γ ⊢[PRAAx] le (Sxy * Sxy) (Sxx * Syy)) :
    Γ ⊢[PRAAx] le ((Sxy + w * (a * b)) * (Sxy + w * (a * b))) ((Sxx + w * (a * a)) * (Syy + w * (b * b))) := by
  have hP : Γ ⊢[PRAAx] le ((Sxy * (a * b)) * (Sxy * (a * b))) ((Sxx * (b * b)) * (Syy * (a * a))) := by
    refine le_congr ?_ ?_ (le_mul_mono ih (le_refl ((a * b) * (a * b))))
    · ipra_ring
    · ipra_ring
  have h2 := two_mul_le hP
  refine le_of_eq_add (d := monus (Sxx * Syy) (Sxy * Sxy) +
    w * monus (Sxx * (b * b) + Syy * (a * a)) (two * (Sxy * (a * b)))) ?_
  ipra_lc natEq (eq_add_of_le ih) + Groth.ι (IPRA.Q.mk Γ w) * natEq (eq_add_of_le h2)

theorem cs_sum_step (w X Y : PTm 2) {N x : PTm n}
    (ih : Γ ⊢[PRAAx] le (Ew w (X * Y) N x * Ew w (X * Y) N x) (Ew w (X * X) N x * Ew w (Y * Y) N x)) :
    Γ ⊢[PRAAx] le (Ew w (X * Y) (succ N) x * Ew w (X * Y) (succ N) x)
      (Ew w (X * X) (succ N) x * Ew w (Y * Y) (succ N) x) := by
  have e₁ := sum_succ' (Γ := Γ) (w * (X * Y)) N x
  have e₂ := sum_succ' (Γ := Γ) (w * (X * X)) N x
  have e₃ := sum_succ' (Γ := Γ) (w * (Y * Y)) N x
  rw [inst2_mul', inst2_mul'] at e₁ e₂ e₃
  exact le_congr (congrMul e₁ e₁).eqSymm (congrMul e₂ e₃).eqSymm (cs_step ih)

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev csF (w X Y : PTm 2) : Fm PTm 2 :=
  le (Ew w (X * Y) (var 0) (var 1) * Ew w (X * Y) (var 0) (var 1))
    (Ew w (X * X) (var 0) (var 1) * Ew w (Y * Y) (var 0) (var 1))

private theorem cs₀ (w X Y : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] csF w X Y := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (congrMul (sum_zero _ _) (sum_zero _ _)).eqSymm (congrMul (sum_zero _ _) (sum_zero _ _)).eqSymm
      (le_refl _)
  · exact cs_sum_step w X Y Prf.hyp0

/-- Cauchy–Schwarz: `Ew(XY)² ≤ Ew(X²) · Ew(Y²)`. -/
theorem cauchy_schwarz (w X Y : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] le (Ew w (X * Y) N x * Ew w (X * Y) N x) (Ew w (X * X) N x * Ew w (Y * Y) N x) := by
  have h := inst (Γ := Γ) (cs₀ w X Y) (![N, x] : Fin 2 → PTm n)
  simpa using h

/-- `Ew(X)² ≤ Ew(X²) · W`: the variance `W · Ew(X²) − Ew(X)²` is nonnegative. -/
theorem second_moment (w X : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] le (Ew w X N x * Ew w X N x) (Ew w (X * X) N x * Wt w N x) := by
  have c := cauchy_schwarz (Γ := Γ) w X (one : PTm 2) N x
  have e₁ : Γ ⊢[PRAAx] Ew w (X * one) N x ≐ Ew w X N x := by
    refine sum_congr_bounded (w * (X * one)) (w * X) x x N (.allI (.impI ?_))
    rw [inst2_mul', inst2_mul', inst2_mul']
    have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift x) = one := by simp [inst2]
    rw [e]
    exact congrMul (.eqRefl _) (mul_one' _)
  have e₂ : Γ ⊢[PRAAx] Ew w ((one : PTm 2) * one) N x ≐ Wt w N x := by
    refine sum_congr_bounded (w * ((one : PTm 2) * one)) w x x N (.allI (.impI ?_))
    rw [inst2_mul', inst2_mul']
    have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift x) = one := by simp [inst2]
    rw [e]
    ipra_ring
  exact le_congr (congrMul e₁ e₁) (congrMul (.eqRefl _) e₂) c

end LeanProofs.IPRA.Probability.Expectation
