import IPRADerivations.AnalyticNumberTheory.RobinGammaUpper
import IPRADerivations.AnalyticNumberTheory.RobinLogWidth
import IPRADerivations.Core.Header

/-!
# The width of the Euler-constant enclosure (`robin_ipra_research_2026-11-19`, `lem:gamma`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "For a rational enclosure at
precision `k`, choose `m = 2^{k+4}` … The resulting width is less than `2^{−k}`."

With `γ_lo(t, K) = 1/2 + An/Ad` (upper logarithm names) and `γ_hi(t, K) = 1/2 + P/Q + 1/(12M²)`, `M = 1 + t` (lower
logarithm names) of `RobinGammaUpper`:

* `tw`: each increment pair differs by `δ_K(m) − δU_K(m) = U_K(1/s) − S_K(1/s) ≤ 9/Z_K`, `Z_K = 4(2K+1)3^{2K+1}`
  (`RobinLogWidth.name_tail`, `s = 2m + 1 ≥ 3`);
* `gw_all`: `P_t/Q_t ≤ An_t/Ad_t + 9t/Z_K` for every `t`, by induction;
* `gamma_width`: `γ_hi(t, K) − γ_lo(t, K) ≤ 9t/Z_K + 1/(12(1 + t)²)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaWidth

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma
  (Lf Lv Pv sv Wv Nv nn dd n_eq Pt Qt Pf dB nB P_succ' P_zero' Q_succ dB_at nB_at)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Un Ud Lz L_eq N_bridge)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaInterval
  (nU dU Xm nU_eq s_sq An Ad An_zero An_succ Ad_zero Ad_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaUpper (gloN gloD ghiN ghiD dd_congr nn_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (c3)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Z_K = 4(2K+1)3^{2K+1}`. -/
abbrev Zg (K : PTm n) : PTm n := two * two * succ (two * K) * Pv K c3

/-! ## One increment -/

theorem tw_alg {nn nU X N Un W s A Z : PTm n} (e1 : Γ ⊢[PRAAx] two * s * X ≐ N * W + nn)
    (e2 : Γ ⊢[PRAAx] two * s * A * X ≐ Un + nU)
    (nt : Γ ⊢[PRAAx] le (Z * (Un * X)) (Z * (N * (A * W * X)) + num 9 * (A * W * X * X))) :
    Γ ⊢[PRAAx] le (nn * (A * W * X) * Z) (nU * (W * X) * Z + num 9 * (W * X) * (A * W * X)) := by
  have e1 := natEq e1
  have e2 := natEq e2
  ipra_le 𝔞 W * sl nt with (𝔞 A * 𝔞 W * 𝔞 X * 𝔞 Z) * e1 - (𝔞 W * 𝔞 X * 𝔞 Z) * e2

/-- `δ_K(m) − δU_K(m) ≤ 9/Z_K`: `nn·dU·Z ≤ nU·dd·Z + 9·dd·dU`. -/
theorem tw {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (K : PTm n) :
    Γ ⊢[PRAAx] le (nn m K * dU m K * Zg K) (nU m K * dd m K * Zg K + num 9 * dd m K * dU m K) := by
  have nt := RobinLogWidth.name_tail (K := K) (p := one) (s_sq (Γ := Γ) m)
    (by ipra_le 2 * sl hm : Γ ⊢[PRAAx] le (c3 * one) (sv m))
  have eL : Γ ⊢[PRAAx] Lv K (sv m) * Pv K (sv m) ≐ Dz K one (sv m) := congrMul (L_eq K (sv m) zero) (.eqRefl _)
  have e1 : Γ ⊢[PRAAx] two * sv m * Dz K one (sv m) ≐ Nz K one (sv m) * Wv m + nn m K :=
    ((congrMul (.eqRefl _) eL).eqSymm.eqTrans (n_eq m K)).eqTrans
      (congrAdd (congrMul (N_bridge K (sv m)) (.eqRefl _)) (.eqRefl _))
  have a := tw_alg (Z := Zg K) e1 (nU_eq m K) (by ipra_le sl nt)
  have ed : Γ ⊢[PRAAx] dd m K ≐ Wv m * Dz K one (sv m) := congrMul (.eqRefl _) eL
  exact le_congr (.eqRefl _) (congrAdd (congrMul (congrMul (.eqRefl _) ed.eqSymm) (.eqRefl _))
    (congrMul (congrMul (.eqRefl _) ed.eqSymm) (.eqRefl _))) a

/-! ## The accumulated difference -/

/-- `P_t/Q_t ≤ An_t/Ad_t + 9t/Z_K`, cleared. -/
abbrev WF (t K : PTm n) : Fm PTm n :=
  le (Pt t (pairT one K) * Ad t K * Zg K) (An t K * Qt t (pairT one K) * Zg K + num 9 * t * Qt t (pairT one K) * Ad t K)

theorem gw_step (t K : PTm n) (ih : Γ ⊢[PRAAx] WF t K) : Γ ⊢[PRAAx] WF (succ t) K := by
  have e : Γ ⊢[PRAAx] one + t ≐ succ t := by ipra_ring
  have hm : Γ ⊢[PRAAx] le one (succ t) := by ipra_le 𝔞 t
  have tc := tw hm K
  have eQ : Γ ⊢[PRAAx] Qt (succ t) (pairT one K) ≐ Qt t (pairT one K) * dd (succ t) K :=
    (Q_succ t _).eqTrans (congrMul (.eqRefl _) ((dB_at t one K).eqTrans (dd_congr e K)))
  have eP : Γ ⊢[PRAAx] Pt (succ t) (pairT one K) ≐
      Pt t (pairT one K) * dd (succ t) K + nn (succ t) K * Qt t (pairT one K) :=
    (P_succ' t _).eqTrans (congrAdd (congrMul (.eqRefl _) ((dB_at t one K).eqTrans (dd_congr e K)))
      (congrMul ((nB_at t one K).eqTrans (nn_congr e K)) (.eqRefl _)))
  refine le_congr (congrMul (congrMul eP (Ad_succ t K)) (.eqRefl _)).eqSymm
    (congrAdd (congrMul (congrMul (An_succ t K) eQ) (.eqRefl _))
      (congrMul (congrMul (.eqRefl _) eQ) (Ad_succ t K))).eqSymm ?_
  ipra_le 𝔞 (dd (succ t) K * dU (succ t) K) * sl ih + 𝔞 (Qt t (pairT one K) * Ad t K) * sl tc

theorem gw_all (t K : PTm n) : Γ ⊢[PRAAx] WF t K := by
  have hall : Γ ⊢[PRAAx] Fm.all (WF (var 0) (Syn.shift K)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_num,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (An_zero (Γ := Γ) K)
      have p := natEq (P_zero' (Γ := Γ) (pairT one K) : Γ ⊢[PRAAx] ap2 Pf zero (pairT one K) ≐ zero)
      ipra_le 0 with (4 * (2 * 𝔞 K + 1) * 𝔞 (Pv K c3) * 𝔞 (Qt zero (pairT one K))) * a -
        (4 * (2 * 𝔞 K + 1) * 𝔞 (Pv K c3) * 𝔞 (Ad zero K)) * p
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_num,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact gw_step _ _ Prf.hyp0
  have r := Prf.allE t hall
  simpa [Syn.subst_inst_shift] using r

/-- `γ_hi(t, K) − γ_lo(t, K) ≤ 9t/Z_K + 1/(12(1+t)²)`, cleared over `ghiD · gloD · Z_K`. -/
theorem gamma_width (t K : PTm n) :
    Γ ⊢[PRAAx] le (ghiN t K * gloD t K * Zg K)
      (gloN t K * ghiD t K * Zg K + num 9 * t * ghiD t K * gloD t K + two * Qt t (pairT one K) * Ad t K * Zg K) := by
  have w := gw_all (Γ := Γ) t K
  ipra_le 24 * 𝔞 ((one + t) * (one + t)) * sl w

end LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaWidth
