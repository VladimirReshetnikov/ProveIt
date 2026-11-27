import IPRADerivations.AnalyticNumberTheory.RobinGamma
import IPRADerivations.AnalyticNumberTheory.SigmaPrimePower

/-!
# Nested logarithm names (`robin_ipra_research_2026-11-19`, `eq:logtail`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, §"A logarithm enclosure from a finite
geometric identity": for `0 ≤ z < 1`, `S_K(z) = 2 Σ_{j<K} z^{2j+1}/(2j+1)` and
`0 ≤ log((1+z)/(1−z)) − S_K(z) ≤ 2z^{2K+1}/((2K+1)(1−z²))`; "In a rational-name presentation the same formula is the
consistency bound between finite polynomials … There is no unbounded search."

For a rational `z = p/s` with `s² = W + p²` (`W ≥ 1`), with cleared denominators
(`RobinGamma.Lf`: `L_K = Π_{j<K} (2j+1)`, `Q_K = s^{2K+1}`, `P_K = p^{2K+1}`, `A = 2K + 1`):

* the lower ends `S_K = N_K / D_K`, `D_K = L_K Q_K`, `N_{K+1} = A s² N_K + 2 s² L_K P_K` (`Nz`), increase (`low_step`);
* the upper ends `U_K = S_K + 2z^{2K+1}/((2K+1)(1−z²)) = Un_K / Ud_K`, `Un_K = A W N_K + 2 s² L_K P_K`,
  `Ud_K = A W D_K`, decrease (`up_step`: `U_K − U_{K+1}` is `4 P_K L_K p²` after clearing), and `S_K ≤ U_K` (`low_up`);
* `log_name`: for all `K` and `j`, `S_K ≤ S_{K+j} ≤ U_{K+j} ≤ U_K` — the nested rational intervals naming
  `log((1+z)/(1−z))` with the explicit width `2z^{2K+1}/((2K+1)(1−z²))`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lf Lv L_zero L_succ Pv P_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The numerators -/

/-- `N_{K+1} = (2K+1) s² N_K + 2 s² L_K p^{2K+1}` at the parameter `⟨p, s⟩`. -/
def Nf2 : PR 2 := rec2 zero (var 1 * succ (two * var 0) * (sndT (var 2) * sndT (var 2)) +
  two * ap2 Lf (var 0) zero * pw (fstT (var 2)) (succ (two * var 0)) * (sndT (var 2) * sndT (var 2)))

abbrev Nz (K p s : PTm n) : PTm n := ap2 Nf2 K (pairT p s)
/-- `L_K`, at the canonical parameter `0` (it does not depend on it, `L_eq`). -/
abbrev Lz (K _p _s : PTm n) : PTm n := Lv K zero

theorem Nz_zero (p s : PTm n) : Γ ⊢[PRAAx] Nz zero p s ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (var 1 * succ (two * var 0) * (sndT (var 2) * sndT (var 2)) +
    two * ap2 Lf (var 0) zero * pw (fstT (var 2)) (succ (two * var 0)) * (sndT (var 2) * sndT (var 2))) (pairT p s)
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem Nz_succ (K p s : PTm n) :
    Γ ⊢[PRAAx] Nz (succ K) p s ≐ Nz K p s * succ (two * K) * (s * s) + two * Lz K p s * Pv K p * (s * s) := by
  have h : Γ ⊢[PRAAx] ap2 Nf2 (succ K) (pairT p s) ≐ Syn.subst ![K, ap2 Nf2 K (pairT p s), pairT p s]
      (var 1 * succ (two * var 0) * (sndT (var 2) * sndT (var 2)) +
        two * ap2 Lf (var 0) zero * pw (fstT (var 2)) (succ (two * var 0)) * (sndT (var 2) * sndT (var 2))) :=
    rec2_succ (Γ := Γ) zero _ K (pairT p s)
  have e : Syn.subst ![K, ap2 Nf2 K (pairT p s), pairT p s]
      (var 1 * succ (two * var 0) * (sndT (var 2) * sndT (var 2)) +
        two * ap2 Lf (var 0) zero * pw (fstT (var 2)) (succ (two * var 0)) * (sndT (var 2) * sndT (var 2))) =
      ap2 Nf2 K (pairT p s) * succ (two * K) * (sndT (pairT p s) * sndT (pairT p s)) +
        two * ap2 Lf K zero * pw (fstT (pairT p s)) (succ (two * K)) *
          (sndT (pairT p s) * sndT (pairT p s)) := by simp
  rw [e] at h
  refine h.eqTrans ?_
  have es : Γ ⊢[PRAAx] sndT (pairT p s) * sndT (pairT p s) ≐ s * s := congrMul (snd_pair _ _) (snd_pair _ _)
  exact congrAdd (congrMul (.eqRefl _) es)
    (congrMul (congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (fst_pair _ _))) es)

/-! ## The three one-step comparisons -/

/-- `S_K ≤ S_{K+1}`. -/
theorem low_step (K p s : PTm n) :
    Γ ⊢[PRAAx] le (Nz K p s * (Lz (succ K) p s * Pv (succ K) s)) (Nz (succ K) p s * (Lz K p s * Pv K s)) := by
  have eN := Nz_succ (Γ := Γ) K p s
  have eD : Γ ⊢[PRAAx] Lz (succ K) p s * Pv (succ K) s ≐ succ (two * K) * Lz K p s * (Pv K s * s * s) :=
    congrMul (L_succ _ _) (P_succ _ _)
  refine le_congr (congrMul (.eqRefl _) eD).eqSymm (congrMul eN (.eqRefl _)).eqSymm ?_
  ipra_le 𝔞 (two * Lz K p s * Pv K p * (s * s) * (Lz K p s * Pv K s))

/-- `S_K ≤ U_K`. -/
theorem low_up (K p s W : PTm n) :
    Γ ⊢[PRAAx] le (Nz K p s * (succ (two * K) * W * (Lz K p s * Pv K s)))
      ((Nz K p s * succ (two * K) * W + two * Pv K p * (s * s) * Lz K p s) * (Lz K p s * Pv K s)) := by
  ipra_le 𝔞 (two * Pv K p * (s * s) * Lz K p s * (Lz K p s * Pv K s))

/-- `U_{K+1} ≤ U_K` for `s² = W + p²`. -/
theorem up_step {K p s W : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) :
    Γ ⊢[PRAAx] le ((Nz (succ K) p s * succ (two * succ K) * W + two * Pv (succ K) p * (s * s) * Lz (succ K) p s) *
        (succ (two * K) * W * (Lz K p s * Pv K s)))
      ((Nz K p s * succ (two * K) * W + two * Pv K p * (s * s) * Lz K p s) *
        (succ (two * succ K) * W * (Lz (succ K) p s * Pv (succ K) s))) := by
  have eN := Nz_succ (Γ := Γ) K p s
  have eL := L_succ (Γ := Γ) K (zero : PTm n)
  have eP := P_succ (Γ := Γ) K p
  have eQ := P_succ (Γ := Γ) K s
  have eU : Γ ⊢[PRAAx] Nz (succ K) p s * succ (two * succ K) * W + two * Pv (succ K) p * (s * s) * Lz (succ K) p s ≐
      (Nz K p s * succ (two * K) * (s * s) + two * Lz K p s * Pv K p * (s * s)) * succ (two * succ K) * W +
        two * (Pv K p * p * p) * (s * s) * (succ (two * K) * Lz K p s) :=
    congrAdd (congrMul (congrMul eN (.eqRefl _)) (.eqRefl _)) (congrMul (congrMul (congrMul (.eqRefl _) eP) (.eqRefl _)) eL)
  have eD : Γ ⊢[PRAAx] succ (two * succ K) * W * (Lz (succ K) p s * Pv (succ K) s) ≐
      succ (two * succ K) * W * ((succ (two * K) * Lz K p s) * (Pv K s * s * s)) :=
    congrMul (.eqRefl _) (congrMul eL eQ)
  refine le_congr (congrMul eU (.eqRefl _)).eqSymm (congrMul (.eqRefl _) eD).eqSymm ?_
  have c := natEq (congrMul (.eqRefl (two * Lz K p s * Pv K p * succ (two * succ K) *
    (succ (two * K) * Lz K p s * Pv K s * W * (s * s)))) hW)
  ipra_le 𝔞 (two * two * (succ (two * K) * Lz K p s * Pv K s * W * (s * s)) * (Pv K p * Lz K p s * (p * p))) with c

/-! ## Positivity -/

theorem L_pos (K x : PTm n) : Γ ⊢[PRAAx] Lv K x ≐ succ (pred (Lv K x)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Lv (var 0) (Syn.shift x) ≐ succ (pred (Lv (var 0) (Syn.shift x)))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      exact (L_zero _).eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred (L_zero _).eqSymm)))
    · simp only [Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      have h0 := (L_succ (Γ := (Lv (var 0) (Syn.shift x) ≐ succ (pred (Lv (var 0) (Syn.shift x)))) :: Γ.map Fm.shift)
        (var 0) (Syn.shift x))
      have p := pos_mul (Γ := (Lv (var 0) (Syn.shift x) ≐ succ (pred (Lv (var 0) (Syn.shift x)))) :: Γ.map Fm.shift)
        (a := succ (two * var 0)) (congrSucc (pred_succ _).eqSymm) Prf.hyp0
      exact h0.eqTrans (p.eqTrans (congrSucc (congrPred h0.eqSymm)))
  have r := Prf.allE K hall
  simpa [Syn.subst_inst_shift] using r

/-! ## The nesting -/

/-- From `a/b ≤ c/d` and `c/d ≤ e/f` with `d ≥ 1`: `a/b ≤ e/f` (cross-multiplied). -/
theorem frac_trans {a b c d e f : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h1 : Γ ⊢[PRAAx] le (a * d) (c * b))
    (h2 : Γ ⊢[PRAAx] le (c * f) (e * d)) : Γ ⊢[PRAAx] le (a * f) (e * b) := by
  have m1 := le_mul_mono h1 (le_refl f)
  have m2 := le_mul_mono h2 (le_refl b)
  have l : Γ ⊢[PRAAx] le (succ (pred d) * (a * f)) (succ (pred d) * (e * b)) := by
    refine le_congr (congrMul hd (.eqRefl _)) (congrMul hd (.eqRefl _)) ?_
    ipra_le sl m1 + sl m2
  exact mul_le_cancel l

/-- The denominators and the upper ends. -/
abbrev Dz (K p s : PTm n) : PTm n := Lz K p s * Pv K s
abbrev Un (K p s W : PTm n) : PTm n := Nz K p s * succ (two * K) * W + two * Pv K p * (s * s) * Lz K p s
abbrev Ud (K p s W : PTm n) : PTm n := succ (two * K) * W * Dz K p s

theorem Pv_congr {K K' : PTm n} (s : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Pv K s ≐ Pv K' s :=
  congrAp2 powF (congrSucc (congrMul (.eqRefl _) e)) (.eqRefl _)

theorem Dz_congr {K K' : PTm n} (p s : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Dz K p s ≐ Dz K' p s :=
  congrMul (congrAp2 _ e (.eqRefl _)) (Pv_congr s e)

theorem Nz_congr {K K' : PTm n} (p s : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Nz K p s ≐ Nz K' p s :=
  congrAp2 _ e (.eqRefl _)

theorem Un_congr {K K' : PTm n} (p s W : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Un K p s W ≐ Un K' p s W :=
  congrAdd (congrMul (congrMul (Nz_congr p s e) (congrSucc (congrMul (.eqRefl _) e))) (.eqRefl _))
    (congrMul (congrMul (congrMul (.eqRefl _) (Pv_congr p e)) (.eqRefl _)) (congrAp2 _ e (.eqRefl _)))

theorem Ud_congr {K K' : PTm n} (p s W : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Ud K p s W ≐ Ud K' p s W :=
  congrMul (congrMul (congrSucc (congrMul (.eqRefl _) e)) (.eqRefl _)) (Dz_congr p s e)

theorem Dz_pos {s : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (K p : PTm n) :
    Γ ⊢[PRAAx] Dz K p s ≐ succ (pred (Dz K p s)) :=
  pos_mul (L_pos _ _) (pos_pw hs _)

theorem Ud_pos {s W : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hW : Γ ⊢[PRAAx] W ≐ succ (pred W)) (K p : PTm n) :
    Γ ⊢[PRAAx] Ud K p s W ≐ succ (pred (Ud K p s W)) :=
  pos_mul (pos_mul (congrSucc (pred_succ _).eqSymm) hW) (Dz_pos hs K p)

/-- The nesting formula at `K' = K + j`. -/
abbrev NF (K j p s W : PTm n) : Fm PTm n :=
  le (Nz K p s * Dz (K + j) p s) (Nz (K + j) p s * Dz K p s) ⋏
    le (Un (K + j) p s W * Ud K p s W) (Un K p s W * Ud (K + j) p s W)

theorem nf_step {K j p s W : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hWp : Γ ⊢[PRAAx] W ≐ succ (pred W))
    (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (ih : Γ ⊢[PRAAx] NF K j p s W) : Γ ⊢[PRAAx] NF K (succ j) p s W := by
  have e : Γ ⊢[PRAAx] succ (K + j) ≐ K + succ j := (add_succ _ _).eqSymm
  have ls := low_step (Γ := Γ) (K + j) p s
  have us := up_step (Γ := Γ) (K := K + j) hW
  -- the lower ends
  have l1 := frac_trans (Dz_pos hs (K + j) p) (Prf.andE₁ ih) ls
  -- the upper ends
  have u1 := frac_trans (Ud_pos hs hWp (K + j) p) us (Prf.andE₂ ih)
  refine .andI ?_ ?_
  · exact le_congr (congrMul (.eqRefl _) (Dz_congr p s e)) (congrMul (Nz_congr p s e) (.eqRefl _)) l1
  · exact le_congr (congrMul (Un_congr p s W e) (.eqRefl _)) (congrMul (.eqRefl _) (Ud_congr p s W e)) u1

theorem nf_zero (K p s W : PTm n) : Γ ⊢[PRAAx] NF K zero p s W := by
  have e : Γ ⊢[PRAAx] K + zero ≐ K := add_zero K
  refine .andI ?_ ?_
  · exact le_congr (congrMul (.eqRefl _) (Dz_congr p s e).eqSymm) (congrMul (Nz_congr p s e).eqSymm (.eqRefl _))
      (le_refl _)
  · exact le_congr (congrMul (Un_congr p s W e).eqSymm (.eqRefl _)) (congrMul (.eqRefl _) (Ud_congr p s W e).eqSymm)
      (le_refl _)

/-- `eq:logtail` as a name: `S_K ≤ S_{K+j}`, `S_{K+j} ≤ U_{K+j}` and `U_{K+j} ≤ U_K` for every `K, j`, for
`z = p/s` with `s² = W + p²`, `s, W ≥ 1`. -/
theorem log_name {p s W : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s)) (hWp : Γ ⊢[PRAAx] W ≐ succ (pred W))
    (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (K j : PTm n) :
    Γ ⊢[PRAAx] NF K j p s W ⋏
      le (Nz (K + j) p s * Ud (K + j) p s W) (Un (K + j) p s W * Dz (K + j) p s) := by
  have hall : Γ ⊢[PRAAx] Fm.all (NF (Syn.shift K) (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift W)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact nf_zero K p s W
    · simp only [Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := NF (Syn.shift K) (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift W) ::
        Γ.map Fm.shift
      have hs' : Δ ⊢[PRAAx] Syn.shift s ≐ succ (pred (Syn.shift s)) := by
        have b := hs.shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
        exact b.wk
      have hWp' : Δ ⊢[PRAAx] Syn.shift W ≐ succ (pred (Syn.shift W)) := by
        have b := hWp.shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
        exact b.wk
      have hW' : Δ ⊢[PRAAx] Syn.shift s * Syn.shift s ≐ Syn.shift W + Syn.shift p * Syn.shift p := by
        have b := hW.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      exact nf_step hs' hWp' hW' Prf.hyp0
  have r := Prf.allE j hall
  simp only [Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact .andI r (low_up _ _ _ _)

/-! ## The parameter of `L_K`, and the bridge to `RobinGamma` -/

/-- `L_K` does not depend on its (unused) parameter. -/
theorem L_eq (K x y : PTm n) : Γ ⊢[PRAAx] Lv K x ≐ Lv K y := by
  have hall : Γ ⊢[PRAAx] Fm.all (Lv (var 0) (Syn.shift x) ≐ Lv (var 0) (Syn.shift y)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (L_zero _).eqTrans (L_zero _).eqSymm
    · simp only [Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact (L_succ _ _).eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (L_succ _ _).eqSymm)
  have r := Prf.allE K hall
  simpa [Syn.subst_inst_shift] using r

/-- `RobinGamma`'s numerators are the case `p = 1`: `Nv K s = Nz K 1 s`. -/
theorem N_bridge (K s : PTm n) : Γ ⊢[PRAAx] RobinGamma.Nv K s ≐ Nz K one s := by
  have hall : Γ ⊢[PRAAx] Fm.all (RobinGamma.Nv (var 0) (Syn.shift s) ≐ Nz (var 0) one (Syn.shift s)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (RobinGamma.N_zero _).eqTrans (Nz_zero _ _).eqSymm
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := (RobinGamma.Nv (var 0) (Syn.shift s) ≐ Nz (var 0) one (Syn.shift s)) ::
        Γ.map Fm.shift
      have a := RobinGamma.N_succ (Γ := Δ) (var 0) (Syn.shift s)
      have b := Nz_succ (Γ := Δ) (var 0) one (Syn.shift s)
      have l := L_eq (Γ := Δ) (var 0) (Syn.shift s) zero
      have o := Order.pw_one_base (Γ := Δ) (succ (two * var 0))
      have ih : Δ ⊢[PRAAx] RobinGamma.Nv (var 0) (Syn.shift s) ≐ Nz (var 0) one (Syn.shift s) := Prf.hyp0
      refine a.eqTrans (b.eqTrans ?_).eqSymm
      refine withEq ih fun e0 => withEq l fun e1 => withEq o fun e2 => ?_
      apply deriveNat; ipra_simps; rw [e0, e1, e2]; ring
  have r := Prf.allE K hall
  simpa [Syn.subst_inst_shift] using r

/-! ## Monotonicity in `z` -/

/-- `S_K(p/s) ≤ S_K(p'/s')`, before the common factor `L_K`: `N_K(p,s) s'^{2K+1} ≤ N_K(p',s') s^{2K+1}`. -/
abbrev MF (K p s p' s' : PTm n) : Fm PTm n := le (Nz K p s * Pv K s') (Nz K p' s' * Pv K s)

theorem mono_step {K p s p' s' : PTm n} (hz : Γ ⊢[PRAAx] le (p * s') (p' * s)) (ih : Γ ⊢[PRAAx] MF K p s p' s') :
    Γ ⊢[PRAAx] MF (succ K) p s p' s' := by
  have eN := Nz_succ (Γ := Γ) K p s
  have eN' := Nz_succ (Γ := Γ) K p' s'
  have eP := P_succ (Γ := Γ) K s
  have eP' := P_succ (Γ := Γ) K s'
  have w := pw_le_pw (Γ := Γ) (succ (two * K)) hz
  have w1 := natEq (LocalFactor.pw_mul_base (Γ := Γ) p s' (succ (two * K)))
  have w2 := natEq (LocalFactor.pw_mul_base (Γ := Γ) p' s (succ (two * K)))
  have pw1 : Γ ⊢[PRAAx] le (Pv K p * Pv K s') (Pv K p' * Pv K s) := by ipra_le sl w with w1 - w2
  refine le_congr (congrMul eN eP').eqSymm (congrMul eN' eP).eqSymm ?_
  ipra_le 𝔞 (succ (two * K) * (s * s) * (s' * s')) * sl ih + 𝔞 (two * Lz K p s * (s * s) * (s' * s')) * sl pw1

/-- `S_K(p/s) ≤ S_K(p'/s')` for every `K`, whenever `p/s ≤ p'/s'`. -/
theorem low_mono {p s p' s' : PTm n} (hz : Γ ⊢[PRAAx] le (p * s') (p' * s)) (K : PTm n) :
    Γ ⊢[PRAAx] le (Nz K p s * Dz K p' s') (Nz K p' s' * Dz K p s) := by
  have hall : Γ ⊢[PRAAx] Fm.all (MF (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift p') (Syn.shift s')) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have a := natEq (Nz_zero (Γ := Γ) p s)
      ipra_le 𝔞 (Nz zero p' s' * Pv zero s) with -(𝔞 (Pv zero s')) * a
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hz' : (MF (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift p') (Syn.shift s') :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift p * Syn.shift s') (Syn.shift p' * Syn.shift s) := by
        have b := hz.shift
        simp only [Fm.shift, subst_le, PTm.subst_mul] at b
        exact b.wk
      exact mono_step hz' Prf.hyp0
  have r := Prf.allE K hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  ipra_le 𝔞 (Lz K p s) * sl r

/-! ## The uniform tail -/

/-- `eq:uniform-log-tail`: for `z = p/s ≤ 1/3`, the width `U_K − S_K = 2 z^{2K+1}/((2K+1)(1−z²))` of the name is at most
`r_K = 9/(4(2K+1)3^{2K+1})`; cleared, `8 p^{2K+1} s² 3^{2K+1} ≤ 9 s^{2K+1} W`. -/
theorem uniform_tail {K p s W : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p) (h3 : Γ ⊢[PRAAx] le (succ two * p) s) :
    Γ ⊢[PRAAx] le (two * two * two * (Pv K p * (s * s)) * Pv K (succ two))
      (succ two * succ two * (Pv K s * W)) := by
  have w := pw_le_pw (Γ := Γ) (succ (two * K)) h3
  have w1 := natEq (LocalFactor.pw_mul_base (Γ := Γ) (succ two) p (succ (two * K)))
  have x : Γ ⊢[PRAAx] le (Pv K (succ two) * Pv K p) (Pv K s) := by ipra_le sl w with w1
  have sq := le_mul_mono h3 h3
  have e := natEq hW
  have y : Γ ⊢[PRAAx] le (two * two * two * (s * s)) (succ two * succ two * W) := by ipra_le sl sq with -9 * e
  have m := le_mul_mono y x
  ipra_le sl m

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName

export_ipra AnalyticNumberTheory.RobinLogName (Dz_pos Nz_succ Nz_zero Ud_pos frac_trans)
