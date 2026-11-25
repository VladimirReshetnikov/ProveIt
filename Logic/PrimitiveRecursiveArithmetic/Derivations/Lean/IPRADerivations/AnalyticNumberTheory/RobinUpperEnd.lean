import IPRADerivations.AnalyticNumberTheory.RobinThreePos
import IPRADerivations.AnalyticNumberTheory.RobinGammaUpper

/-!
# The upper end `U(n, k)`, `Neg`, and the incompatibility of `Pos` and `Neg` (`robin_ipra_research_2026-11-19`, `eq:neg`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, §"Composing the double logarithm":
"The resulting rational interval `[L(n, k), U(n, k)]` contains `B(n)` … `Neg(n, k) :⟺ n ≥ 2 ∧ nU(n, k) < σ(n)` (`eq:neg`; `NegR` here).
… They are mutually incompatible, even when different precisions are used."

The upper end `U(n, k) = (Up − Um)/Ud` is the upper corner of the same program as `RobinThreePos.L`: the upper end
`C₁/D₁ = hi(n, K₁)` of `log n`; if `C₁ ≥ D₁` the double logarithm is at most `hi(C₁/D₁)` and `U = T_{K_e}(γ_hi) · hi(C₁/D₁)`
(`T` the upper exponential name of `RobinExpName`, `γ_hi` of `RobinGammaUpper`); otherwise it is at most `−lo(D₁/C₁) < 0` and
`U = −E_{K_e}(γ_lo) · lo(D₁/C₁)`.

* `gamma_any`: `γ_lo(t, K) ≤ γ_hi(t', K')` for all `t, t', K` and `K' ≥ 2`: the lower names increase in `t` (`lo_t_mono`),
  the upper names decrease (`ghi_step`, by `RobinGamma.step_upper`, and `ghi_mono`);
* `exp_any`: `E_K(x) ≤ T_{K'}(x)` for all `K, K'` and `0 ≤ x ≤ 1`; `e_le_three`: `E_K(x) ≤ 1 + 2x ≤ 3`;
* `lo_pos`, `hi_pos`: for `n ≥ 2` the numerators of `log n`'s ends are at least `1`;
* `lu`: `L(n, k) ≤ U(n, k')` for every `n ≥ 2` and all precisions `k, k'` — all three sign cases of the double logarithm;
* `pos_neg`: `Pos(n, k)` and `Neg(n, k')` are contradictory.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinUpperEnd

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv Pv sv Wv nn dd Pt Qt P_succ' Q_succ dB_at nB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Nz_succ frac_trans L_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval
  (eb eb_spec exp_le loN loD hiN hiD Kp lo_mono lo_le_hi_any loD_pos hiD_pos dt st Wt c3 c8 st_pos Wt_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval (An Ad Ad_pos An_succ Ad_succ sv_pos Wv_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaUpper
  (gloN gloD ghiN ghiD gamma_consistent gamma_hi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName
  (Ev Ed Fv Tn Td E_zero F_succ F_zero exp_name e_up e_mono Ed_pos Td_pos Ed_congr Ev_congr Tn_congr Td_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos
  (one_le_of_pos branch rr K1 A1 B1 K2 LLn LLd K2' LHn LHd tg Kg gN gD Ke EN ED cnd Lp Lm Ld Pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult (sig)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower (pos_pw)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Signum (sg sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Euler's constant across `t` -/

/-- `An_t/Ad_t ≤ An_{t+j}/Ad_{t+j}`. -/
abbrev GF (t j K : PTm n) : Fm PTm n := le (An t K * Ad (t + j) K) (An (t + j) K * Ad t K)

theorem gf_step {t j K : PTm n} (ih : Γ ⊢[PRAAx] GF t j K) : Γ ⊢[PRAAx] GF t (succ j) K := by
  have e : Γ ⊢[PRAAx] t + succ j ≐ succ (t + j) := add_succ _ _
  have eA' : Γ ⊢[PRAAx] An (t + succ j) K ≐
      An (t + j) K * RobinGammaInterval.dU (succ (t + j)) K + RobinGammaInterval.nU (succ (t + j)) K * Ad (t + j) K :=
    (congrAp2 _ e (.eqRefl _)).eqTrans (An_succ _ _)
  have eD' : Γ ⊢[PRAAx] Ad (t + succ j) K ≐ Ad (t + j) K * RobinGammaInterval.dU (succ (t + j)) K :=
    (congrAp2 _ e (.eqRefl _)).eqTrans (Ad_succ _ _)
  refine le_congr (congrMul (.eqRefl _) eD').eqSymm (congrMul eA' (.eqRefl _)).eqSymm ?_
  ipra_le 𝔞 (RobinGammaInterval.dU (succ (t + j)) K) * sl ih +
    𝔞 (RobinGammaInterval.nU (succ (t + j)) K * Ad (t + j) K * Ad t K)

theorem lo_t_mono (t j K : PTm n) : Γ ⊢[PRAAx] GF t j K := by
  have hall : Γ ⊢[PRAAx] Fm.all (GF (Syn.shift t) (var 0) (Syn.shift K)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have e : Γ ⊢[PRAAx] t + zero ≐ t := add_zero _
      exact le_congr (congrMul (.eqRefl _) (congrAp2 _ e (.eqRefl _)).eqSymm)
        (congrMul (congrAp2 _ e (.eqRefl _)).eqSymm (.eqRefl _)) (le_refl _)
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact gf_step Prf.hyp0
  have r := Prf.allE j hall
  simpa [Syn.subst_inst_shift] using r

theorem dd_pos {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (K : PTm n) : Γ ⊢[PRAAx] dd m K ≐ succ (pred (dd m K)) :=
  pos_mul (Wv_pos hm) (pos_mul (L_pos _ _) (pos_pw (sv_pos m) _))

theorem Qt_pos (t K : PTm n) : Γ ⊢[PRAAx] Qt t (pairT one K) ≐ succ (pred (Qt t (pairT one K))) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Qt (var 0) (pairT one (Syn.shift K)) ≐ succ (pred (Qt (var 0) (pairT one (Syn.shift K))))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        LeanProofs.IPRA.PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have z := prod_zero (Γ := Γ) RobinGamma.dB (pairT one K)
      exact z.eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred z.eqSymm)))
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        LeanProofs.IPRA.PTm.subst_pred, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := (Qt (var 0) (pairT one (Syn.shift K)) ≐
        succ (pred (Qt (var 0) (pairT one (Syn.shift K))))) :: Γ.map Fm.shift
      have h0 : Δ ⊢[PRAAx] Qt (succ (var 0)) (pairT one (Syn.shift K)) ≐
          Qt (var 0) (pairT one (Syn.shift K)) * dd (one + var 0) (Syn.shift K) :=
        (Q_succ _ _).eqTrans (congrMul (.eqRefl _) (dB_at _ _ _))
      have hm : Δ ⊢[PRAAx] le one (one + var 0) := by ipra_le 𝔞 (var 0)
      have p := pos_mul (Γ := Δ) Prf.hyp0 (dd_pos hm (Syn.shift K))
      exact h0.eqTrans (p.eqTrans (congrSucc (congrPred h0.eqSymm)))
  have r := Prf.allE t hall
  simpa [Syn.subst_inst_shift] using r

theorem ghiD_pos (t K : PTm n) : Γ ⊢[PRAAx] ghiD t K ≐ succ (pred (ghiD t K)) := by
  have hM : Γ ⊢[PRAAx] one + t ≐ succ (pred (one + t)) := pos_of_one_le (by ipra_le 𝔞 t)
  have h12 : Γ ⊢[PRAAx] (two * two * succ two : PTm n) ≐ succ (pred (two * two * succ two)) :=
    pos_of_one_le (by ipra_le 11)
  exact pos_mul (pos_mul h12 (pos_mul hM hM)) (Qt_pos t K)

theorem gloD_pos (t K : PTm n) : Γ ⊢[PRAAx] gloD t K ≐ succ (pred (gloD t K)) := pos_mul two_pos' (Ad_pos _ _)

/-- `γ_hi(t + 1, K') ≤ γ_hi(t, K')` for `K' ≥ 2`. -/
theorem ghi_step (t j : PTm n) :
    Γ ⊢[PRAAx] le (ghiN (succ t) (succ (succ j)) * ghiD t (succ (succ j)))
      (ghiN t (succ (succ j)) * ghiD (succ t) (succ (succ j))) := by
  have eQ := natEq ((Q_succ (Γ := Γ) t (pairT one (succ (succ j)))).eqTrans (congrMul (.eqRefl _) (dB_at t one _)))
  have eP := natEq ((P_succ' (Γ := Γ) t (pairT one (succ (succ j)))).eqTrans
    (congrAdd (congrMul (.eqRefl _) (dB_at t one _)) (congrMul (nB_at t one _) (.eqRefl _))))
  have h := RobinGamma.step_upper (Γ := Γ) (one + t) j
  ipra_le 12 * 𝔞 (Qt t (pairT one (succ (succ j))) * Qt t (pairT one (succ (succ j)))) * sl h with
    -(144 * (1 + 𝔞 t) ^ 2 * (2 + 𝔞 t) ^ 2 * 𝔞 (Qt t (pairT one (succ (succ j))))) * eP +
      (12 * (2 + 𝔞 t) ^ 2 * (6 * (1 + 𝔞 t) ^ 2 * 𝔞 (Qt t (pairT one (succ (succ j)))) +
          12 * (1 + 𝔞 t) ^ 2 * 𝔞 (Pt t (pairT one (succ (succ j)))) + 𝔞 (Qt t (pairT one (succ (succ j))))) -
        (6 * (2 + 𝔞 t) ^ 2 + 1) * 12 * (1 + 𝔞 t) ^ 2 * 𝔞 (Qt t (pairT one (succ (succ j))))) * eQ

theorem ghiN_congr {t t' : PTm n} (K : PTm n) (e : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx] ghiN t K ≐ ghiN t' K := by
  have eM : Γ ⊢[PRAAx] (one + t) * (one + t) ≐ (one + t') * (one + t') :=
    congrMul (congrAdd (.eqRefl _) e) (congrAdd (.eqRefl _) e)
  have eQ : Γ ⊢[PRAAx] Qt t (pairT one K) ≐ Qt t' (pairT one K) := congrAp2 _ e (.eqRefl _)
  have eP : Γ ⊢[PRAAx] Pt t (pairT one K) ≐ Pt t' (pairT one K) := congrAp2 _ e (.eqRefl _)
  exact congrAdd (congrAdd (congrMul (congrMul (.eqRefl _) eM) eQ) (congrMul (congrMul (.eqRefl _) eM) eP)) eQ

theorem ghiD_congr {t t' : PTm n} (K : PTm n) (e : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx] ghiD t K ≐ ghiD t' K :=
  congrMul (congrMul (.eqRefl _) (congrMul (congrAdd (.eqRefl _) e) (congrAdd (.eqRefl _) e))) (congrAp2 _ e (.eqRefl _))

abbrev HF (t i K : PTm n) : Fm PTm n := le (ghiN (t + i) K * ghiD t K) (ghiN t K * ghiD (t + i) K)

/-- `γ_hi(t + i, K') ≤ γ_hi(t, K')` for `K' ≥ 2`. -/
theorem ghi_mono (t i j : PTm n) : Γ ⊢[PRAAx] HF t i (succ (succ j)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (HF (Syn.shift t) (var 0) (succ (succ (Syn.shift j)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have e : Γ ⊢[PRAAx] t + zero ≐ t := add_zero _
      exact le_congr (congrMul (ghiN_congr _ e).eqSymm (.eqRefl _)) (congrMul (.eqRefl _) (ghiD_congr _ e).eqSymm)
        (le_refl _)
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := HF (Syn.shift t) (var 0) (succ (succ (Syn.shift j))) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] HF (Syn.shift t) (var 0) (succ (succ (Syn.shift j))) := Prf.hyp0
      have st' := ghi_step (Γ := Δ) (Syn.shift t + var 0) (Syn.shift j)
      have u := frac_trans (ghiD_pos _ _) st' ih
      have e : Δ ⊢[PRAAx] succ (Syn.shift t + var 0) ≐ Syn.shift t + succ (var 0) := (add_succ _ _).eqSymm
      exact le_congr (congrMul (ghiN_congr _ e) (.eqRefl _)) (congrMul (.eqRefl _) (ghiD_congr _ e)) u
  have r := Prf.allE i hall
  simpa [Syn.subst_inst_shift] using r

/-- `γ_lo(t, K) ≤ γ_hi(t', K')` for all `t, t', K` and `K' ≥ 2`. -/
theorem gamma_any (t t' K j : PTm n) :
    Γ ⊢[PRAAx] le (gloN t K * ghiD t' (succ (succ j))) (ghiN t' (succ (succ j)) * gloD t K) := by
  refine .orE (le_total t t') ?_ ?_
  · let C : List (Fm PTm n) := le t t' :: Γ
    have et : C ⊢[PRAAx] t + monus t' t ≐ t' := (eq_add_of_le Prf.hyp0).eqSymm
    have g := lo_t_mono (Γ := C) t (monus t' t) K
    have g' : C ⊢[PRAAx] le (An t K * Ad t' K) (An t' K * Ad t K) :=
      le_congr (congrMul (.eqRefl _) (congrAp2 _ et (.eqRefl _))) (congrMul (congrAp2 _ et (.eqRefl _)) (.eqRefl _)) g
    have g2 : C ⊢[PRAAx] le (gloN t K * gloD t' K) (gloN t' K * gloD t K) := by ipra_le 4 * sl g'
    exact frac_trans (gloD_pos t' K) g2 (gamma_consistent t' K _)
  · let C : List (Fm PTm n) := le t' t :: Γ
    have et : C ⊢[PRAAx] t' + monus t t' ≐ t := (eq_add_of_le Prf.hyp0).eqSymm
    have h := ghi_mono (Γ := C) t' (monus t t') j
    have h' := le_congr (congrMul (ghiN_congr _ et) (.eqRefl _)) (congrMul (.eqRefl _) (ghiD_congr _ et)) h
    exact frac_trans (ghiD_pos t _) (gamma_consistent t K _) h'

/-- `γ_lo ≤ 1`, from `γ_lo ≤ γ_hi ≤ 7/12`. -/
theorem glo_le_one (t K j : PTm n) : Γ ⊢[PRAAx] le (gloN t K) (gloD t K) := by
  have c := gamma_any (Γ := Γ) t t K j
  have h := gamma_hi_le (Γ := Γ) t j
  have m1 := le_mul_mono c (le_refl (num 12 : PTm n))
  have m2 := le_mul_mono h (le_refl (gloD t K))
  have l : Γ ⊢[PRAAx] le (ghiD t (succ (succ j)) * (num 12 * gloN t K)) (ghiD t (succ (succ j)) * (num 12 * gloD t K)) := by
    ipra_le sl m1 + sl m2 + 5 * 𝔞 (ghiD t (succ (succ j)) * gloD t K)
  have l' := mul_le_cancel (le_congr (congrMul (ghiD_pos _ _) (.eqRefl _)) (congrMul (ghiD_pos _ _) (.eqRefl _)) l)
  exact mul_le_cancel (d' := num 11) l'

/-- `γ_hi ≤ 1`. -/
theorem ghi_le_one (t j : PTm n) : Γ ⊢[PRAAx] le (ghiN t (succ (succ j))) (ghiD t (succ (succ j))) := by
  have h := gamma_hi_le (Γ := Γ) t j
  exact mul_le_cancel (d' := num 11) (by ipra_le sl h + 5 * 𝔞 (ghiD t (succ (succ j))))

/-! ## The exponential across precisions -/

/-- `E_K(x) ≤ T_{K'}(x)` for all `K, K'`, `0 ≤ x = p/q ≤ 1`. -/
theorem exp_any {p q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hpq : Γ ⊢[PRAAx] le p q) (K K' : PTm n) :
    Γ ⊢[PRAAx] le (Ev K p q * Td K' q) (Tn K' p q * Ed K q) := by
  refine .orE (le_total K K') ?_ ?_
  · let C : List (Fm PTm n) := le K K' :: Γ
    have eK : C ⊢[PRAAx] K + monus K' K ≐ K' := (eq_add_of_le Prf.hyp0).eqSymm
    have nst := Prf.andE₁ (Prf.andE₁ (exp_name (Γ := C) hq.wk hpq.wk K (monus K' K)))
    have nst' := le_congr (congrMul (.eqRefl _) (Ed_congr _ eK)) (congrMul (Ev_congr _ _ eK) (.eqRefl _)) nst
    exact frac_trans (Ed_pos hq.wk K') nst' (e_up K' p q)
  · let C : List (Fm PTm n) := le K' K :: Γ
    have eK : C ⊢[PRAAx] K' + monus K K' ≐ K := (eq_add_of_le Prf.hyp0).eqSymm
    have nst := Prf.andE₂ (Prf.andE₁ (exp_name (Γ := C) hq.wk hpq.wk K' (monus K K')))
    have nst' := le_congr (congrMul (Tn_congr _ _ eK) (.eqRefl _)) (congrMul (.eqRefl _) (Td_congr _ eK)) nst
    exact frac_trans (Td_pos hq.wk K) (e_up K p q) nst'

/-- `E_K(x) ≤ T_0(x) = 1 + 2x ≤ 3` for `0 ≤ x ≤ 1`. -/
theorem e_le_three {p q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hpq : Γ ⊢[PRAAx] le p q) (K : PTm n) :
    Γ ⊢[PRAAx] le (Ev K p q) (num 3 * Ed K q) := by
  have h := exp_any hq hpq K zero
  have E0 := natEq (E_zero (Γ := Γ) p q)
  have P1 := natEq (pw_one (Γ := Γ) p)
  have Q1 := natEq (pw_one (Γ := Γ) q)
  have F1 := natEq ((F_succ (Γ := Γ) zero).eqTrans ((congrMul (.eqRefl _) F_zero).eqTrans
    (by ipra_ring : Γ ⊢[PRAAx] succ zero * one ≐ one)))
  have c : Γ ⊢[PRAAx] le (q * Ev K p q) (q * (num 3 * Ed K q)) := by
    ipra_le sl h + 2 * 𝔞 (Ed K q) * sl hpq with
      -(𝔞 q * 𝔞 (Fv K) * 𝔞 (pw q K)) * E0 - 2 * 𝔞 (Fv K) * 𝔞 (pw q K) * P1 +
        𝔞 (Ev K p q) * 𝔞 (pw q (succ zero)) * F1 + 𝔞 (Ev K p q) * Q1
  exact mul_le_cancel (le_congr (congrMul hq (.eqRefl _)) (congrMul hq (.eqRefl _)) c)

/-! ## Positivity of the logarithm numerators -/

theorem eb_ge_one {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] le one (eb N one) := by
  have hN1 : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 1
  have p1 := natEq (pw_one (Γ := Γ) (two : PTm n))
  have h1 : Γ ⊢[PRAAx] le (one * pw two one) N := by ipra_le sl hN with -p1
  exact exp_le (le_refl _) h1 (Prf.andE₂ (eb_spec (le_refl _) hN1)) (le_refl _)

theorem nz3_pos (K : PTm n) : Γ ⊢[PRAAx] le one (Nz (succ K) one c3) := by
  have l := one_le_of_pos (L_pos (Γ := Γ) K (zero : PTm n))
  have e1 := natEq (AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) (succ (two * K)))
  have en := natEq (Nz_succ (Γ := Γ) K one c3)
  ipra_le 𝔞 (Nz K one c3 * succ (two * K) * (c3 * c3)) + 18 * sl l + 17 with en + 18 * 𝔞 (Lv K zero) * e1

theorem un3_pos (K : PTm n) : Γ ⊢[PRAAx] le one (RobinLogName.Un K one c3 c8) := by
  have l := one_le_of_pos (L_pos (Γ := Γ) K (zero : PTm n))
  have e1 := natEq (AnalyticNumberTheory.Order.pw_one_base (Γ := Γ) (succ (two * K)))
  ipra_le 𝔞 (Nz K one c3 * succ (two * K) * c8) + 18 * sl l + 17 with 18 * 𝔞 (Lv K zero) * e1

/-- `log n ≥ lo ≥ 1/D` for `n ≥ 2`: the lower numerator is positive. -/
theorem lo_pos {N K : PTm n} (hN : Γ ⊢[PRAAx] le two N) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le one (loN N one K) := by
  have hN1 : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 1
  have he := eb_ge_one hN
  have eK := pos_of_one_le hK
  have hz : Γ ⊢[PRAAx] le one (Nz K one c3) :=
    le_congr (.eqRefl _) (RobinLogName.Nz_congr _ _ eK).eqSymm (nz3_pos (pred K))
  have hd := one_le_of_pos (RobinLogName.Dz_pos (Γ := Γ) (st_pos (le_refl _) hN1) K (dt N one))
  have m := le_mul_mono (le_mul_mono he hz) hd
  ipra_le sl m + 𝔞 (Nz K (dt N one) (st N one) * RobinLogName.Dz K one c3)

theorem hi_pos {N K : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] le one (hiN N one K) := by
  have hN1 : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 1
  have he := eb_ge_one hN
  have hu := un3_pos (Γ := Γ) K
  have hd := one_le_of_pos (RobinLogName.Ud_pos (Γ := Γ) (st_pos (le_refl _) hN1) (Wt_pos (le_refl _) hN1) K (dt N one))
  have m := le_mul_mono (le_mul_mono he hu) hd
  ipra_le sl m + 𝔞 (RobinLogName.Un K (dt N one) (st N one) (Wt N one) * RobinLogName.Ud K one c3 c8)

/-! ## The upper end and `Neg` -/

/-- `log n ≤ C₁/D₁`. -/
abbrev C1 (N k : PTm n) : PTm n := hiN N one (K1 N k)
abbrev D1 (N k : PTm n) : PTm n := hiD N one (K1 N k)
abbrev K3 (N k : PTm n) : PTm n := Kp (C1 N k) (D1 N k) (rr N k)
/-- `log log n ≤ UHn/UHd` when `C₁ ≥ D₁`. -/
abbrev UHn (N k : PTm n) : PTm n := hiN (C1 N k) (D1 N k) (K3 N k)
abbrev UHd (N k : PTm n) : PTm n := hiD (C1 N k) (D1 N k) (K3 N k)
abbrev K3' (N k : PTm n) : PTm n := Kp (D1 N k) (C1 N k) (rr N k)
/-- `log log n ≤ −ULn/ULd` when `C₁ < D₁`. -/
abbrev ULn (N k : PTm n) : PTm n := loN (D1 N k) (C1 N k) (K3' N k)
abbrev ULd (N k : PTm n) : PTm n := loD (D1 N k) (C1 N k) (K3' N k)
/-- `γ ≤ gHn/gHd` and `e^γ ≤ EhN/EhD = T_{K_e}(gHn/gHd)`. -/
abbrev gHn (N k : PTm n) : PTm n := ghiN (tg N k) (Kg N k)
abbrev gHd (N k : PTm n) : PTm n := ghiD (tg N k) (Kg N k)
abbrev EhN (N k : PTm n) : PTm n := Tn (Ke N k) (gHn N k) (gHd N k)
abbrev EhD (N k : PTm n) : PTm n := Td (Ke N k) (gHd N k)
/-- The case test: `1` iff `C₁ < D₁`. -/
abbrev cndU (N k : PTm n) : PTm n := sg (monus (D1 N k) (C1 N k))
/-- `U(n, k) = (Uup − Uum)/Uud`. -/
abbrev Uup (N k : PTm n) : PTm n := monus one (cndU N k) * (EhN N k * UHn N k)
abbrev Uum (N k : PTm n) : PTm n := cndU N k * (EN N k * ULn N k)
abbrev Uud (N k : PTm n) : PTm n := monus one (cndU N k) * (EhD N k * UHd N k) + cndU N k * (ED N k * ULd N k)

/-- `eq:neg`: `Neg(n, k) :⟺ n ≥ 2 ∧ n U(n, k) < σ(n)`, cleared: `n·Uup < σ(n)·Uud + n·Uum`. -/
def NegR (N k : PTm n) : Fm PTm n := le two N ⋏ lt (N * Uup N k) (sig N * Uud N k + N * Uum N k)

/-! ## `L ≤ U` -/

theorem one_le_monus {x y : PTm n} (h : Γ ⊢[PRAAx] lt y x) : Γ ⊢[PRAAx] le one (monus x y) := by
  have e := natEq (eq_add_of_le (le_of_lt h))
  ipra_le sl h with -e

/-- With `c ≥ 1`, the case split selects the second branch. -/
theorem branch1 {c : PTm n} (hc : Γ ⊢[PRAAx] le one c) (X Y Z W : PTm n) :
    Γ ⊢[PRAAx] monus one (sg c) * X ≐ zero ⋏ (sg c * Y ≐ Y ⋏ monus one (sg c) * Z + sg c * W ≐ W) := by
  have s1 : Γ ⊢[PRAAx] sg c ≐ one :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (pos_of_one_le hc))).eqTrans (sg_succ _)
  have m0 : Γ ⊢[PRAAx] monus one (sg c) ≐ zero := (congrMonus (.eqRefl _) s1).eqTrans (monus_self _)
  have e0 := natEq m0
  have e1 := natEq s1
  refine .andI ?_ (.andI ?_ ?_)
  · apply deriveNat; ipra_simps; rw [e0]; ring
  · apply deriveNat; ipra_simps; rw [e1]; ring
  · apply deriveNat; ipra_simps; rw [e0, e1]; ring

theorem cancel_le {x y z w : PTm n} (hz : Γ ⊢[PRAAx] z ≐ succ (pred z)) (h1 : Γ ⊢[PRAAx] le z w)
    (h2 : Γ ⊢[PRAAx] le (w * x) (y * z)) : Γ ⊢[PRAAx] le x y := by
  have m := le_mul_mono h1 (le_refl x)
  have c : Γ ⊢[PRAAx] le (z * x) (z * y) := by ipra_le sl m + sl h2
  exact mul_le_cancel (le_congr (congrMul hz (.eqRefl _)) (congrMul hz (.eqRefl _)) c)

theorem comm2 {a b c d : PTm n} (h : Γ ⊢[PRAAx] le (a * b) (c * d)) : Γ ⊢[PRAAx] le (b * a) (d * c) := by ipra_le sl h

theorem prod_frac {a b c d e f g h : PTm n} (h1 : Γ ⊢[PRAAx] le (a * d) (c * b)) (h2 : Γ ⊢[PRAAx] le (e * h) (g * f)) :
    Γ ⊢[PRAAx] le ((a * e) * (d * h)) ((c * g) * (b * f)) := by
  have m := le_mul_mono h1 h2
  ipra_le sl m

theorem lu_pp {X1 X2 Y1 Y2 : PTm n} (h : Γ ⊢[PRAAx] le (X1 * Y2) (Y1 * X2)) :
    Γ ⊢[PRAAx] le (X1 * Y2 + zero * X2) (Y1 * X2 + zero * Y2) := by ipra_le sl h

theorem lu_triv (a b c d : PTm n) : Γ ⊢[PRAAx] le (zero * a + zero * b) (c + d) := by ipra_le 𝔞 c + 𝔞 d

theorem lu_nn {E D A B C X : PTm n} (he : Γ ⊢[PRAAx] le E (num 3 * D)) (hl : Γ ⊢[PRAAx] le (A * B) (C * X)) :
    Γ ⊢[PRAAx] le (zero * (D * X) + (E * A) * B) (zero * B + (c3 * C) * (D * X)) := by
  ipra_le 𝔞 (A * B) * sl he + 3 * 𝔞 D * sl hl

/-- `L(n, k) ≤ U(n, k')` for `n ≥ 2` and all precisions, cleared:
`Lp·Uud + Uum·Ld ≤ Uup·Ld + Lm·Uud`. -/
theorem lu {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) (k k' : PTm n) :
    Γ ⊢[PRAAx] le (Lp N k * Uud N k' + Uum N k' * Ld N k) (Uup N k' * Ld N k + Lm N k * Uud N k') := by
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have hN1 : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 1
  have hK1 : Γ ⊢[PRAAx] le one (K1 N k) := by ipra_le 𝔞 (rr N k) + 𝔞 (eb N one) + 3
  have hA1 : Γ ⊢[PRAAx] le one (A1 N k) := lo_pos hN hK1
  have hB1 : Γ ⊢[PRAAx] le one (B1 N k) := one_le_of_pos (loD_pos h1 hN1 (K1 N k))
  have hC1 : Γ ⊢[PRAAx] le one (C1 N k') := hi_pos hN
  have hD1 : Γ ⊢[PRAAx] le one (D1 N k') := one_le_of_pos (hiD_pos h1 hN1 (K1 N k'))
  have hAC : Γ ⊢[PRAAx] le (A1 N k * D1 N k') (C1 N k' * B1 N k) := lo_le_hi_any h1 hN1 (K1 N k) (K1 N k')
  -- the γ and exponential factors
  have hgD : Γ ⊢[PRAAx] gD N k ≐ succ (pred (gD N k)) := gloD_pos _ _
  have hgD' : Γ ⊢[PRAAx] gD N k' ≐ succ (pred (gD N k')) := gloD_pos _ _
  have hgH' : Γ ⊢[PRAAx] gHd N k' ≐ succ (pred (gHd N k')) := ghiD_pos _ _
  refine .orE (lt_or_le (A1 N k) (B1 N k)) ?_ ?_
  · -- `log n`'s lower end is below `1`: `L = −3 hi(B₁/A₁)`
    let C : List (Fm PTm n) := lt (A1 N k) (B1 N k) :: Γ
    have hlt : C ⊢[PRAAx] lt (A1 N k) (B1 N k) := Prf.hyp0
    have hAB : C ⊢[PRAAx] le (A1 N k) (B1 N k) := le_of_lt hlt
    have bL := branch1 (one_le_monus hlt) (EN N k * LLn N k) (c3 * LHn N k) (ED N k * LLd N k) (LHd N k)
    refine .orE (lt_or_le (C1 N k') (D1 N k')) ?_ ?_
    · -- both ends negative
      let C' : List (Fm PTm n) := lt (C1 N k') (D1 N k') :: C
      have hlt' : C' ⊢[PRAAx] lt (C1 N k') (D1 N k') := Prf.hyp0
      have hCD : C' ⊢[PRAAx] le (C1 N k') (D1 N k') := le_of_lt hlt'
      have bU := branch1 (one_le_monus hlt') (EhN N k' * UHn N k') (EN N k' * ULn N k') (EhD N k' * UHd N k')
        (ED N k' * ULd N k')
      have hC1' : C' ⊢[PRAAx] le one (C1 N k') := hC1.wk.wk
      have hA1' : C' ⊢[PRAAx] le one (A1 N k) := hA1.wk.wk
      have hAB' : C' ⊢[PRAAx] le (A1 N k) (B1 N k) := hAB.wk
      have hAC' : C' ⊢[PRAAx] le (A1 N k * D1 N k') (C1 N k' * B1 N k) := hAC.wk.wk
      have m1 := lo_mono (a := D1 N k') (b := C1 N k') (a' := B1 N k) (b' := A1 N k) hC1' hCD hA1' hAB'
        (comm2 hAC') (K3' N k')
      have m2 := lo_le_hi_any (a := B1 N k) (b := A1 N k) hA1' hAB' (K3' N k') (K2' N k)
      have ul := frac_trans (loD_pos hA1' hAB' (K3' N k')) m1 m2
      have e3 := e_le_three (Γ := C') hgD'.wk.wk (glo_le_one _ _ (two * rr N k')) (Ke N k')
      have r := lu_nn e3 ul
      refine le_congr ?_ ?_ r
      · exact (congrAdd (congrMul (Prf.andE₁ bL.wk) (Prf.andE₂ (Prf.andE₂ bU)))
          (congrMul (Prf.andE₁ (Prf.andE₂ bU)) (Prf.andE₂ (Prf.andE₂ bL.wk)))).eqSymm
      · exact (congrAdd (congrMul (Prf.andE₁ bU) (Prf.andE₂ (Prf.andE₂ bL.wk)))
          (congrMul (Prf.andE₁ (Prf.andE₂ bL.wk)) (Prf.andE₂ (Prf.andE₂ bU)))).eqSymm
    · -- `L < 0 ≤ U`
      let C' : List (Fm PTm n) := le (D1 N k') (C1 N k') :: C
      have bU := branch (Prf.hyp0 : C' ⊢[PRAAx] le (D1 N k') (C1 N k')) (EhN N k' * UHn N k') (EN N k' * ULn N k')
        (EhD N k' * UHd N k') (ED N k' * ULd N k')
      have r := lu_triv (Γ := C') (Uud N k') (Ld N k) (Uup N k' * Ld N k) (Lm N k * Uud N k')
      refine le_congr ?_ (.eqRefl _) r
      exact (congrAdd (congrMul (Prf.andE₁ bL.wk) (.eqRefl _)) (congrMul (Prf.andE₁ (Prf.andE₂ bU)) (.eqRefl _))).eqSymm
  · -- `log n`'s lower end is at least `1`, so is the upper end
    let C : List (Fm PTm n) := le (B1 N k) (A1 N k) :: Γ
    have hBA : C ⊢[PRAAx] le (B1 N k) (A1 N k) := Prf.hyp0
    have hDC : C ⊢[PRAAx] le (D1 N k') (C1 N k') := cancel_le (loD_pos (Γ := C) h1.wk hN1.wk (K1 N k)) hBA hAC.wk
    have bL := branch hBA (EN N k * LLn N k) (c3 * LHn N k) (ED N k * LLd N k) (LHd N k)
    have bU := branch hDC (EhN N k' * UHn N k') (EN N k' * ULn N k') (EhD N k' * UHd N k') (ED N k' * ULd N k')
    -- the double logarithms
    have m1 := lo_mono (Γ := C) (a := A1 N k) (b := B1 N k) (a' := C1 N k') (b' := D1 N k') hB1.wk hBA hD1.wk hDC hAC.wk (K2 N k)
    have m2 := lo_le_hi_any (Γ := C) (a := C1 N k') (b := D1 N k') hD1.wk hDC (K2 N k) (K3 N k')
    have ll := frac_trans (loD_pos (Γ := C) hD1.wk hDC (K2 N k)) m1 m2
    -- the exponential factors
    have g := gamma_any (Γ := C) (tg N k) (tg N k') (Kg N k) (two * rr N k')
    have em := e_mono (p := gN N k) (q := gD N k) (p' := gHn N k') (q' := gHd N k') g (Ke N k)
    have ex := exp_any (Γ := C) hgH'.wk (ghi_le_one _ _) (Ke N k) (Ke N k')
    have ee := frac_trans (Ed_pos hgH'.wk (Ke N k)) em ex
    have r := lu_pp (prod_frac ee ll)
    refine le_congr ?_ ?_ r
    · exact (congrAdd (congrMul (Prf.andE₁ bL) (Prf.andE₂ (Prf.andE₂ bU)))
        (congrMul (Prf.andE₁ (Prf.andE₂ bU)) (Prf.andE₂ (Prf.andE₂ bL)))).eqSymm
    · exact (congrAdd (congrMul (Prf.andE₁ bU) (Prf.andE₂ (Prf.andE₂ bL)))
        (congrMul (Prf.andE₁ (Prf.andE₂ bL)) (Prf.andE₂ (Prf.andE₂ bU)))).eqSymm

/-- The upper denominator is positive for `n ≥ 2`. -/
theorem uud_pos {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) (k : PTm n) : Γ ⊢[PRAAx] le one (Uud N k) := by
  have h1 : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have hN1 : Γ ⊢[PRAAx] le one N := by ipra_le sl hN + 1
  have hC1 : Γ ⊢[PRAAx] le one (C1 N k) := hi_pos hN
  have hD1 : Γ ⊢[PRAAx] le one (D1 N k) := one_le_of_pos (hiD_pos h1 hN1 (K1 N k))
  refine .orE (lt_or_le (C1 N k) (D1 N k)) ?_ ?_
  · let C : List (Fm PTm n) := lt (C1 N k) (D1 N k) :: Γ
    have hlt : C ⊢[PRAAx] lt (C1 N k) (D1 N k) := Prf.hyp0
    have bU := branch1 (one_le_monus hlt) (EhN N k * UHn N k) (EN N k * ULn N k) (EhD N k * UHd N k) (ED N k * ULd N k)
    have p := one_le_of_pos (pos_mul (Ed_pos (gloD_pos (Γ := C) (tg N k) (Kg N k)) (Ke N k))
      (loD_pos hC1.wk (le_of_lt hlt) (K3' N k)))
    exact le_congr (.eqRefl _) (Prf.andE₂ (Prf.andE₂ bU)).eqSymm p
  · let C : List (Fm PTm n) := le (D1 N k) (C1 N k) :: Γ
    have bU := branch (Prf.hyp0 : C ⊢[PRAAx] le (D1 N k) (C1 N k)) (EhN N k * UHn N k) (EN N k * ULn N k)
      (EhD N k * UHd N k) (ED N k * ULd N k)
    have p := one_le_of_pos (pos_mul (Td_pos (ghiD_pos (Γ := C) (tg N k) (Kg N k)) (Ke N k))
      (hiD_pos hD1.wk Prf.hyp0 (K3 N k)))
    exact le_congr (.eqRefl _) (Prf.andE₂ (Prf.andE₂ bU)).eqSymm p

theorem incomp_gen {s N Lp Lm Ld Up Um Ud : PTm n} (φ : Fm PTm n) (hP : Γ ⊢[PRAAx] lt (s * Ld + N * Lm) (N * Lp))
    (hN : Γ ⊢[PRAAx] lt (N * Up) (s * Ud + N * Um)) (hLU : Γ ⊢[PRAAx] le (Lp * Ud + Um * Ld) (Up * Ld + Lm * Ud))
    (hUd : Γ ⊢[PRAAx] le one Ud) : Γ ⊢[PRAAx] φ := by
  have m1 := le_mul_mono (hP : Γ ⊢[PRAAx] le (succ (s * Ld + N * Lm)) (N * Lp)) (le_refl Ud)
  have m2 := le_mul_mono (hN : Γ ⊢[PRAAx] le (succ (N * Up)) (s * Ud + N * Um)) (le_refl Ld)
  have m3 := le_mul_mono (le_refl N) hLU
  exact lt_irrefl zero _ (by ipra_le sl m1 + sl m2 + sl m3 + sl hUd + 𝔞 Ld)

/-- `Pos(n, k)` and `Neg(n, k')` are incompatible, even at different precisions. -/
theorem pos_neg {N k k' : PTm n} (φ : Fm PTm n) (hP : Γ ⊢[PRAAx] Pos N k) (hN : Γ ⊢[PRAAx] NegR N k') :
    Γ ⊢[PRAAx] φ := by
  have hP' := hP; unfold Pos at hP'
  have hN' := hN; unfold NegR at hN'
  have h2 := Prf.andE₁ hP'
  exact incomp_gen φ (Prf.andE₂ hP') (Prf.andE₂ hN') (lu h2 k k') (uud_pos h2 k')

end LeanProofs.IPRA.AnalyticNumberTheory.RobinUpperEnd
