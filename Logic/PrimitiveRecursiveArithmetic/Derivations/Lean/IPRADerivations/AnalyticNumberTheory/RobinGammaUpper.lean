import IPRADerivations.AnalyticNumberTheory.RobinGammaInterval

/-!
# The Euler-constant enclosure and its consistency (`robin_ipra_research_2026-11-19`, `lem:gamma`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, Lemma `lem:gamma`
(`a_m ≤ γ ≤ a_m + 1/(12m²)`) and §"Euler's constant without an unspecified convergence rate": "The case `m = 1` gives
`1/2 ≤ γ ≤ 7/12`, useful for every subsequent domain check. … Intersecting with `[1/2, 7/12]` is legitimate".

With the lower name `γ_lo(t, K) = 1/2 + An/Ad` of `RobinGammaInterval` (upper logarithm names) and the upper name

  `γ_hi(t, K') = 1/2 + P_t/Q_t + 1/(12M²)`,  `M = 1 + t`,

built from `RobinGamma`'s partial sums `P_t/Q_t = Σ_{i<t} δ_{K'}(1 + i)` of the increments with the *lower* logarithm names:

* `term_cmp`: `δU_K(m) ≤ δ_{K'}(m)` for all `K, K'` — because `S_{K'}(1/s) ≤ U_K(1/s)` (`low_le_up`, from the nested
  names `RobinLogName.log_name`);
* `acc_cmp`: `An_t/Ad_t ≤ P_t/Q_t`, by induction on `t`;
* `gamma_consistent`: `γ_lo(t, K) ≤ γ_hi(t, K')` for all `t, K, K'`;
* `gamma_hi_le` (`K' ≥ 2`): `γ_hi(t, K') ≤ 7/12`, from `RobinGamma.gamma_tail` at `m₀ = 1`; and `gamma_lo_ge`:
  `γ_lo ≥ 1/2`. So every enclosure lies in `[1/2, 7/12]`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaUpper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma
  (Lf Lv Pv sv Wv Nv nn dd n_eq Pt Qt Pf dB nB P_succ' P_zero' Q_succ dB_at nB_at gamma_tail)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName
  (Nz Dz Un Ud Lz log_name low_up L_eq N_bridge frac_trans Dz_pos Ud_pos Nz_congr Dz_congr Un_congr Ud_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval
  (nU dU Xm nU_eq s_sq sv_pos Wv_pos An Ad An_zero An_succ Ad_zero Ad_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Termwise comparison -/

/-- `S_{K'}(1/s) ≤ U_K(1/s)` for all `K, K'`. -/
theorem low_le_up {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (K K' : PTm n) :
    Γ ⊢[PRAAx] le (Nz K' one (sv m) * Ud K one (sv m) (Wv m)) (Un K one (sv m) (Wv m) * Dz K' one (sv m)) := by
  refine .orE (le_total K K') ?_ ?_
  · let C : List (Fm PTm n) := le K K' :: Γ
    have eK : C ⊢[PRAAx] K + monus K' K ≐ K' := (eq_add_of_le Prf.hyp0).eqSymm
    have u := Prf.andE₂ (Prf.andE₁ (log_name (Γ := C) (p := one) (sv_pos m) (Wv_pos hm.wk) (s_sq m) K (monus K' K)))
    have u' := le_congr (congrMul (Un_congr _ _ _ eK) (.eqRefl _)) (congrMul (.eqRefl _) (Ud_congr _ _ _ eK)) u
    exact frac_trans (Ud_pos (sv_pos m) (Wv_pos hm.wk) K' one) (low_up K' one (sv m) (Wv m)) u'
  · let C : List (Fm PTm n) := le K' K :: Γ
    have eK : C ⊢[PRAAx] K' + monus K K' ≐ K := (eq_add_of_le Prf.hyp0).eqSymm
    have l := Prf.andE₁ (Prf.andE₁ (log_name (Γ := C) (p := one) (sv_pos m) (Wv_pos hm.wk) (s_sq m) K' (monus K K')))
    have l' := le_congr (congrMul (.eqRefl _) (Dz_congr _ _ eK)) (congrMul (Nz_congr _ _ eK) (.eqRefl _)) l
    exact frac_trans (Dz_pos (sv_pos m) K one) l' (low_up K one (sv m) (Wv m))

/-- `δU_K(m) ≤ δ_{K'}(m)`: `nU·dd ≤ nn·dU`. -/
theorem term_cmp {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (K K' : PTm n) :
    Γ ⊢[PRAAx] le (nU m K * dd m K') (nn m K' * dU m K) := by
  have c := low_le_up hm K K'
  have e1 := natEq (n_eq (Γ := Γ) m K')
  have e2 := natEq (nU_eq (Γ := Γ) m K)
  have e3 := natEq (N_bridge (Γ := Γ) K' (sv m))
  have e4 := natEq (L_eq (Γ := Γ) K' (sv m) zero)
  ipra_le 𝔞 (Wv m) * sl c with
    -(𝔞 (Lv K zero) * 𝔞 (Pv K (sv m)) * (4 * 𝔞 m * (𝔞 m + 1)) * (2 * 𝔞 K + 1)) * e1 +
      𝔞 (Lv K' (sv m)) * 𝔞 (Pv K' (sv m)) * (4 * 𝔞 m * (𝔞 m + 1)) * e2 -
      𝔞 (Lv K zero) * 𝔞 (Pv K (sv m)) * (4 * 𝔞 m * (𝔞 m + 1)) ^ 2 * (2 * 𝔞 K + 1) * e3 +
      𝔞 (Pv K' (sv m)) * (𝔞 (Nz K one (sv m)) * (2 * 𝔞 K + 1) * (4 * 𝔞 m * (𝔞 m + 1)) +
        2 * 𝔞 (Pv K one) * (2 * 𝔞 m + 1) ^ 2 * 𝔞 (Lv K zero)) * (4 * 𝔞 m * (𝔞 m + 1)) * e4

/-! ## Accumulated comparison -/

theorem sv_congr {m m' : PTm n} (e : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] sv m ≐ sv m' := congrSucc (congrMul (.eqRefl _) e)
theorem Wv_congr {m m' : PTm n} (e : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Wv m ≐ Wv m' :=
  congrMul (congrMul (.eqRefl _) e) (congrSucc e)
theorem dd_congr {m m' : PTm n} (e : Γ ⊢[PRAAx] m ≐ m') (K : PTm n) : Γ ⊢[PRAAx] dd m K ≐ dd m' K :=
  congrMul (Wv_congr e) (congrMul (congrAp2 _ (.eqRefl _) (sv_congr e)) (congrAp2 powF (.eqRefl _) (sv_congr e)))
theorem nn_congr {m m' : PTm n} (e : Γ ⊢[PRAAx] m ≐ m') (K : PTm n) : Γ ⊢[PRAAx] nn m K ≐ nn m' K :=
  congrMonus (congrMul (congrMul (.eqRefl _) (sv_congr e))
      (congrMul (congrAp2 _ (.eqRefl _) (sv_congr e)) (congrAp2 powF (.eqRefl _) (sv_congr e))))
    (congrMul (congrAp2 _ (.eqRefl _) (sv_congr e)) (Wv_congr e))

/-- `An_t/Ad_t ≤ P_t/Q_t`. -/
abbrev CF (t K K' : PTm n) : Fm PTm n := le (An t K * Qt t (pairT one K')) (Pt t (pairT one K') * Ad t K)

theorem cf_step (t K K' : PTm n) (ih : Γ ⊢[PRAAx] CF t K K') : Γ ⊢[PRAAx] CF (succ t) K K' := by
  have e : Γ ⊢[PRAAx] one + t ≐ succ t := by ipra_ring
  have hm : Γ ⊢[PRAAx] le one (succ t) := by ipra_le 𝔞 t
  have tc := term_cmp hm K K'
  have eQ : Γ ⊢[PRAAx] Qt (succ t) (pairT one K') ≐ Qt t (pairT one K') * dd (succ t) K' :=
    (Q_succ t _).eqTrans (congrMul (.eqRefl _) ((dB_at t one K').eqTrans (dd_congr e K')))
  have eP : Γ ⊢[PRAAx] Pt (succ t) (pairT one K') ≐
      Pt t (pairT one K') * dd (succ t) K' + nn (succ t) K' * Qt t (pairT one K') :=
    (P_succ' t _).eqTrans (congrAdd (congrMul (.eqRefl _) ((dB_at t one K').eqTrans (dd_congr e K')))
      (congrMul ((nB_at t one K').eqTrans (nn_congr e K')) (.eqRefl _)))
  refine le_congr (congrMul (An_succ t K) eQ).eqSymm (congrMul eP (Ad_succ t K)).eqSymm ?_
  ipra_le 𝔞 (dU (succ t) K * dd (succ t) K') * sl ih + 𝔞 (Ad t K * Qt t (pairT one K')) * sl tc

theorem acc_cmp (t K K' : PTm n) : Γ ⊢[PRAAx] CF t K K' := by
  have hall : Γ ⊢[PRAAx] Fm.all (CF (var 0) (Syn.shift K) (Syn.shift K')) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (An_zero (Γ := Γ) K)
      ipra_le 𝔞 (Pt zero (pairT one K') * Ad zero K) with -(𝔞 (Qt zero (pairT one K'))) * a
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact cf_step _ _ _ Prf.hyp0
  have r := Prf.allE t hall
  simpa [Syn.subst_inst_shift] using r

/-! ## The enclosure -/

/-- `γ_lo(t, K) = (Ad + 2An)/(2Ad)`. -/
abbrev gloN (t K : PTm n) : PTm n := Ad t K + two * An t K
abbrev gloD (t K : PTm n) : PTm n := two * Ad t K
/-- `γ_hi(t, K') = (6M²Q + 12M²P + Q)/(12M²Q)`, `M = 1 + t`. -/
abbrev ghiN (t K' : PTm n) : PTm n :=
  two * succ two * ((one + t) * (one + t)) * Qt t (pairT one K') +
    two * two * succ two * ((one + t) * (one + t)) * Pt t (pairT one K') + Qt t (pairT one K')
abbrev ghiD (t K' : PTm n) : PTm n := two * two * succ two * ((one + t) * (one + t)) * Qt t (pairT one K')

/-- Consistency: `γ_lo(t, K) ≤ γ_hi(t, K')` for all `t, K, K'`. -/
theorem gamma_consistent (t K K' : PTm n) :
    Γ ⊢[PRAAx] le (gloN t K * ghiD t K') (ghiN t K' * gloD t K) := by
  have c := acc_cmp (Γ := Γ) t K K'
  ipra_le 24 * 𝔞 ((one + t) * (one + t)) * sl c + 2 * 𝔞 (Qt t (pairT one K') * Ad t K)

/-- `γ_hi(t, K') ≤ 7/12` for `K' ≥ 2`. -/
theorem gamma_hi_le (t j : PTm n) :
    Γ ⊢[PRAAx] le (num 12 * ghiN t (succ (succ j))) (num 7 * ghiD t (succ (succ j))) := by
  have g := gamma_tail (Γ := Γ) (m := one) (le_refl _) j t
  ipra_le 12 * sl g

/-- `γ_lo(t, K) ≥ 1/2`. -/
theorem gamma_lo_ge (t K : PTm n) : Γ ⊢[PRAAx] le (gloD t K) (two * gloN t K) := by
  ipra_le 4 * 𝔞 (An t K)

end LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaUpper
