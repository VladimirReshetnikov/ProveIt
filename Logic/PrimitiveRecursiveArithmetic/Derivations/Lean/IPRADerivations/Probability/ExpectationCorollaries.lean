import IPRADerivations.Probability.Variance
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Core.LinearCombination

/-!
# Corollaries of the finite expectation kernel

Packet: `probability/expected_value_ipra_2026-11-16`, Sections 3, 5 and 6, in the cross-multiplied
setting of `Probability/Expectation` (weights `w_i ≥ 0` on outcomes `i < N`, natural observables,
`W = ∑ w_i`, `Ew(X) = ∑ w_i X_i = W · E[X]`):

* `exp_const` (`cor:constant`): `Ew(c) = c W`, i.e. `E[c] = c`;
* `exp_scale` (`thm:linearity`, homogeneity; with `exp_add` additivity): `Ew(c X) = c Ew(X)`;
* `equiprobable` (`cor:equiprobable`): for unit weights `W = N` and `Ew(X) = ∑ X_i`;
* `ae_congr` (`thm:ae-congruence`): `w_i X_i = w_i Y_i` for all `i` gives `Ew(X) = Ew(Y)`;
* `zero_abs` (`thm:zero-abs`): `Ew(|X − Y|) = 0` gives `w_i X_i = w_i Y_i`, i.e. `X = Y` almost surely;
* `var_zero` (`thm:variance-zero`): if `W Q = S²` (variance zero) then `W X_i = S` at every outcome of
  positive weight; nonnegativity is `Expectation.second_moment`;
* `power_markov` (`cor:power-markov`): `c^r · ∑ w_i [X_i ≥ c] ≤ ∑ w_i X_i^r`;
* `three_quarters` (`cor:three-quarters`, denominator-free form): if `Ew(D²) = s² W` with `s ≥ 1`,
  then `4 · ∑ w_i [D_i ≥ 2s] ≤ W`, i.e. `P(|X − μ| ≥ 2σ) ≤ 1/4`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ExpectationCorollaries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add' geB inst2_geB geI geI_true geI_false
  le_zero_of chebyshev)
open LeanProofs.IPRA.Probability.Variance (ad Vr dvB dv_pt variance_identity sum_one)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le mulParam inst2_mulParam sum_mul_param)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A constant observable `c(x)`. -/
abbrev cst (c : PTm 1) : PTm 2 := Syn.subst ![var 1] c

theorem inst2_cst (c : PTm 1) (i x : PTm n) : inst2 (cst c) i x = Syn.subst ![x] c := by
  simp only [inst2, cst, Syn.subst_subst]; congr 1; funext j; fin_cases j; rfl

/-- `cor:constant`: `Ew(c) = c W`. -/
theorem exp_const (c : PTm 1) (w : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] Ew w (cst c) N x ≐ Syn.subst ![x] c * Wt w N x := by
  refine (sum_congr_bounded (w * cst c) (mulParam c w) x x N (.allI (.impI ?_))).eqTrans (sum_mul_param c w N x)
  rw [inst2_mul', inst2_mulParam, inst2_cst]
  exact mul_comm _ _

/-- `thm:linearity`, homogeneity: `Ew(c X) = c Ew(X)`. -/
theorem exp_scale (c : PTm 1) (w X : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] Ew w (cst c * X) N x ≐ Syn.subst ![x] c * Ew w X N x := by
  refine (sum_congr_bounded (w * (cst c * X)) (mulParam c (w * X)) x x N (.allI (.impI ?_))).eqTrans
    (sum_mul_param c (w * X) N x)
  rw [inst2_mul', inst2_mul', inst2_mulParam, inst2_mul', inst2_cst]
  ipra_ring

theorem inst2_one' (i x : PTm n) : inst2 (one : PTm 2) i x = one := by simp [inst2]

theorem zml {a : PTm n} (h : Γ ⊢[PRAAx] a ≐ zero) (X : PTm n) : Γ ⊢[PRAAx] a * X ≐ zero :=
  (congrMul h (.eqRefl X)).eqTrans (zero_mul X)

/-- `cor:equiprobable`: for unit weights, `W = N` and `Ew(X) = ∑_{i<N} X_i`. -/
theorem equiprobable (X : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] (Wt (one : PTm 2) N x ≐ N) ⋏ (Ew (one : PTm 2) X N x ≐ ap2 (sumF X) N x) := by
  refine .andI (sum_one N x) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  rw [inst2_mul', inst2_one']
  exact one_mul _

/-- `thm:ae-congruence`: observables that agree on every outcome of positive weight have equal
expectations. -/
theorem ae_congr (w X Y : PTm 2) {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 w (var 0) (Syn.shift x) * inst2 X (var 0) (Syn.shift x) ≐
        inst2 w (var 0) (Syn.shift x) * inst2 Y (var 0) (Syn.shift x))) :
    Γ ⊢[PRAAx] Ew w X N x ≐ Ew w Y N x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_mul', inst2_mul']
  exact Prf.impE h.allOpen.wk Prf.hyp0

/-! ## Zero absolute expectation and zero variance -/

theorem ad_zero {a b : PTm n} (h : Γ ⊢[PRAAx] ad a b ≐ zero) : Γ ⊢[PRAAx] a ≐ b := by
  have l1 : Γ ⊢[PRAAx] le (monus a b) zero := le_congr (.eqRefl _) h (le_add_right _ _)
  have l2 : Γ ⊢[PRAAx] le (monus b a) zero := le_congr (.eqRefl _) h (le_add_left _ _)
  exact le_antisymm (le_antisymm l1 (zero_le _)) (le_antisymm l2 (zero_le _))

theorem w_cancel {w a b : PTm n} (h : Γ ⊢[PRAAx] w * ad a b ≐ zero) : Γ ⊢[PRAAx] w * a ≐ w * b := by
  refine .orE (zero_or_zero_of_mul h) ?_ ?_
  · exact (zml Prf.hyp0 _).eqTrans (zml Prf.hyp0 _).eqSymm
  · exact congrMul (.eqRefl _) (ad_zero Prf.hyp0)

/-- `|X − Y|` as an observable. -/
abbrev adB (X Y : PTm 2) : PTm 2 := monus X Y + monus Y X

theorem inst2_adB (X Y : PTm 2) (i x : PTm n) : inst2 (adB X Y) i x = ad (inst2 X i x) (inst2 Y i x) := by
  simp [inst2, ad]

/-- `thm:zero-abs`: `Ew(|X − Y|) = 0` forces `w_i X_i = w_i Y_i` at every outcome. -/
theorem zero_abs (w X Y : PTm 2) {N x i : PTm n} (h : Γ ⊢[PRAAx] Ew w (adB X Y) N x ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 w i x * inst2 X i x ≐ inst2 w i x * inst2 Y i x := by
  have z := sum_zero_elim (w * adB X Y) h hi
  rw [inst2_mul', inst2_adB] at z
  exact w_cancel z

/-- `thm:variance-zero`: if `W Q = S²` (zero variance), then `W X_i = S` at every outcome of positive
weight, i.e. `X = E[X]` almost surely. -/
theorem var_zero (w X : PTm 2) {N x i : PTm n}
    (hv : Γ ⊢[PRAAx] Wt w N x * Ew w (X * X) N x ≐ Ew w X N x * Ew w X N x) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 w i x * (Wt w N x * inst2 X i x) ≐ inst2 w i x * Ew w X N x := by
  have hv' := natEq hv
  have v0 : Γ ⊢[PRAAx] Vr w X N x ≐ zero := by
    ipra_lc natEq (variance_identity (Γ := Γ) w X N x) + Groth.ι (IPRA.Q.mk Γ (Wt w N x)) * hv'
  have z := (dv_pt w X i _ _ x).eqSymm.eqTrans (sum_zero_elim (dvB w X) v0 hi)
  refine .orE (zero_or_zero_of_mul z) ?_ ?_
  · exact (zml Prf.hyp0 _).eqTrans (zml Prf.hyp0 _).eqSymm
  · refine .orE (zero_or_zero_of_mul Prf.hyp0) ?_ ?_ <;> exact congrMul (.eqRefl _) (ad_zero Prf.hyp0)

/-! ## Power Markov and the three-quarters bound -/

theorem pw_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) (r : PTm n) : Γ ⊢[PRAAx] le (pw a r) (pw b r) := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
    have e := h.shift
    simp only [Fm.shift, subst_le] at e
    simpa [Syn.shift] using e
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw (Syn.shift a) (var 0)) (pw (Syn.shift b) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact le_congr (pw_zero _).eqSymm (pw_zero _).eqSymm (le_refl _)
    · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      exact le_congr (pw_succ _ _).eqSymm (pw_succ _ _).eqSymm (le_mul_mono Prf.hyp0 h'.wk)
  have i := Prf.allE r hall
  simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at i
  exact i

theorem power_pt (a X w r : PTm n) : Γ ⊢[PRAAx] le (pw a r * (w * geI a X)) (w * pw X r) := by
  refine .orE (lt_or_le X a) ?_ ?_
  · exact le_zero_of ((congrMul (.eqRefl _) ((congrMul (.eqRefl _) (geI_false Prf.hyp0)).eqTrans (mul_zero _))).eqTrans
      (mul_zero _))
  · refine le_congr ?_ (.eqRefl _) (le_mul_mono (le_refl w) (pw_mono Prf.hyp0 r))
    refine .eqTrans ?_ (congrMul (.eqRefl _) (congrMul (.eqRefl _) (geI_true Prf.hyp0))).eqSymm
    ipra_ring

theorem inst2_pwR (X : PTm 2) (r : PTm 1) (i x : PTm n) :
    inst2 (pw X (cst r)) i x = pw (inst2 X i x) (Syn.subst ![x] r) := by
  have e := inst2_cst (n := n) r i x
  simp only [inst2] at e ⊢
  simp only [subst_ap2, e]

/-- `cor:power-markov`: `c^r · ∑ w_i [X_i ≥ c] ≤ ∑ w_i X_i^r`. -/
theorem power_markov (c r : PTm 1) (w X : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] le (Syn.subst ![x] (pw c r) * Ew w (geB c X) N x) (Ew w (pw X (cst r)) N x) := by
  refine le_congr (sum_mul_param (pw c r) (w * geB c X) N x) (.eqRefl _)
    (sum_le (mulParam (pw c r) (w * geB c X)) (w * pw X (cst r)) x N (.allI (.impI ?_)))
  rw [inst2_mulParam, inst2_mul', inst2_mul', inst2_geB, inst2_pwR]
  have e : Syn.subst ![Syn.shift x] (pw c r) = pw (Syn.subst ![Syn.shift x] c) (Syn.subst ![Syn.shift x] r) := by
    simp
  rw [e]
  exact power_pt _ _ _ _

/-- `cor:three-quarters`, denominator-free: if `Ew(D²) = s² W` with `s ≥ 1`, then
`4 ∑ w_i [D_i ≥ 2s] ≤ W`. -/
theorem three_quarters (s : PTm 1) (w D : PTm 2) {N x : PTm n}
    (hs : Γ ⊢[PRAAx] Syn.subst ![x] s ≐ succ (pred (Syn.subst ![x] s)))
    (hv : Γ ⊢[PRAAx] Ew w (D * D) N x ≐ (Syn.subst ![x] s * Syn.subst ![x] s) * Wt w N x) :
    Γ ⊢[PRAAx] le (two * two * Ew w (geB (two * s) D) N x) (Wt w N x) := by
  have ch := chebyshev (Γ := Γ) (two * s) w D N x
  have e : Syn.subst ![x] (two * s * (two * s)) = two * Syn.subst ![x] s * (two * Syn.subst ![x] s) := by simp
  rw [e] at ch
  refine le_cancel_pos (Combinatorics.Binomial.pos_mul hs hs) (le_congr ?_ hv (le_congr (.eqRefl _) (.eqRefl _) ch))
  ipra_ring

end LeanProofs.IPRA.Probability.ExpectationCorollaries
