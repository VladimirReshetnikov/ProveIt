import IPRADerivations.AnalyticNumberTheory.RobinLogName

/-!
# Nested exponential names (`robin_ipra_research_2026-11-19`, `eq:exptail`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, §"The exponential enclosure": "For
`0 ≤ x ≤ 1` put `E_K(x) = Σ_{j=0}^K x^j/j!`. The ratio of consecutive omitted terms is at most `1/(K+2)`, so
`0 ≤ e^x − E_K(x) ≤ 2/(K+1)!` (`eq:exptail`). This too is a finite tail estimate … If `x ∈ [l, u] ⊆ [0, 1]`, monotonicity
gives `E_K(l) ≤ e^x ≤ E_K(u) + 2/(K+1)!`."

For a rational `x = p/q`, `q ≥ 1`, with cleared denominators (`F_K = K!`, `Fv`):

* the lower ends `E_K = e_K/(K! q^K)`, `e_0 = 1`, `e_{K+1} = (K+1) q e_K + p^{K+1}` (`Ev`), increase (`e_step`);
* the upper ends `T_K = E_K + 2x^{K+1}/(K+1)! = Tn_K/Td_K`, `Tn_K = (K+1) q e_K + 2p^{K+1}`, `Td_K = (K+1)! q^{K+1}`, satisfy
  `E_K ≤ T_K` (`e_up`) and decrease for `x ≤ 1` (`t_step`: after clearing, `T_K − T_{K+1}` is
  `(K+1)! q^{K+1} p^{K+1} ((K+2)q − 2p)`);
* `exp_name`: `E_K ≤ E_{K+j} ≤ T_{K+j} ≤ T_K` for all `K, j` — nested rational intervals for `e^x`, `0 ≤ x ≤ 1`;
* `exp_tail` (`eq:exptail`): `T_K − E_K = 2x^{K+1}/(K+1)! ≤ 2/(K+1)!`;
* `e_mono`: `E_K` is monotone in `x` (the packet's "monotonicity gives `E_K(l) ≤ e^x`").
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Factorials and numerators -/

/-- `F_K = K!` (the parameter is unused). -/
def Ff : PR 2 := rec2 (succ zero) (succ (var 0) * var 1)
abbrev Fv (K : PTm n) : PTm n := ap2 Ff K zero

theorem F_zero : Γ ⊢[PRAAx] Fv (zero : PTm n) ≐ one := by
  have h := rec2_zero (Γ := Γ) (succ zero) (succ (var 0) * var 1) (zero : PTm n)
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem F_succ (K : PTm n) : Γ ⊢[PRAAx] Fv (succ K) ≐ succ K * Fv K := by
  have h : Γ ⊢[PRAAx] ap2 Ff (succ K) zero ≐ Syn.subst ![K, ap2 Ff K zero, zero] (succ (var 0) * var 1) :=
    rec2_succ (Γ := Γ) (succ zero) (succ (var 0) * var 1) K zero
  have e : Syn.subst ![K, ap2 Ff K zero, zero] (succ (var 0) * var 1) = succ K * ap2 Ff K zero := by simp
  rw [e] at h
  exact h

theorem F_pos (K : PTm n) : Γ ⊢[PRAAx] Fv K ≐ succ (pred (Fv K)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Fv (var 0) ≐ succ (pred (Fv (var 0)))) := by
    ipra_qfind (trivial) [subst_ap2]
    · exact F_zero.eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred F_zero.eqSymm)))
    · have h0 := F_succ (Γ := (Fv (var 0) ≐ succ (pred (Fv (var 0)))) :: Γ.map Fm.shift) (var 0)
      have p := pos_mul (Γ := (Fv (var 0) ≐ succ (pred (Fv (var 0)))) :: Γ.map Fm.shift)
        (a := succ (var 0)) (congrSucc (pred_succ _).eqSymm) Prf.hyp0
      exact h0.eqTrans (p.eqTrans (congrSucc (congrPred h0.eqSymm)))
  have r := Prf.allE K hall
  simpa using r

/-- `e_{K+1} = (K+1) q e_K + p^{K+1}` at the parameter `⟨p, q⟩`. -/
def Ef : PR 2 := rec2 (succ zero) (succ (var 0) * sndT (var 2) * var 1 + pw (fstT (var 2)) (succ (var 0)))
abbrev Ev (K p q : PTm n) : PTm n := ap2 Ef K (pairT p q)
/-- The denominator `K! q^K`. -/
abbrev Ed (K q : PTm n) : PTm n := Fv K * pw q K
/-- The upper end `T_K = Tn/Td`. -/
abbrev Tn (K p q : PTm n) : PTm n := succ K * q * Ev K p q + two * pw p (succ K)
abbrev Td (K q : PTm n) : PTm n := Fv (succ K) * pw q (succ K)

theorem E_zero (p q : PTm n) : Γ ⊢[PRAAx] Ev zero p q ≐ one := by
  have h := rec2_zero (Γ := Γ) (succ zero) (succ (var 0) * sndT (var 2) * var 1 + pw (fstT (var 2)) (succ (var 0)))
    (pairT p q)
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem E_succ (K p q : PTm n) : Γ ⊢[PRAAx] Ev (succ K) p q ≐ succ K * q * Ev K p q + pw p (succ K) := by
  have h : Γ ⊢[PRAAx] ap2 Ef (succ K) (pairT p q) ≐ Syn.subst ![K, ap2 Ef K (pairT p q), pairT p q]
      (succ (var 0) * sndT (var 2) * var 1 + pw (fstT (var 2)) (succ (var 0))) :=
    rec2_succ (Γ := Γ) (succ zero) _ K (pairT p q)
  have e : Syn.subst ![K, ap2 Ef K (pairT p q), pairT p q]
      (succ (var 0) * sndT (var 2) * var 1 + pw (fstT (var 2)) (succ (var 0))) =
      succ K * sndT (pairT p q) * ap2 Ef K (pairT p q) + pw (fstT (pairT p q)) (succ K) := by simp
  rw [e] at h
  exact h.eqTrans (congrAdd (congrMul (congrMul (.eqRefl _) (snd_pair _ _)) (.eqRefl _))
    (congrAp2 powF (.eqRefl _) (fst_pair _ _)))

theorem Ev_congr {K K' : PTm n} (p q : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Ev K p q ≐ Ev K' p q :=
  congrAp2 _ e (.eqRefl _)
theorem Ed_congr {K K' : PTm n} (q : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Ed K q ≐ Ed K' q :=
  congrMul (congrAp2 _ e (.eqRefl _)) (congrAp2 powF e (.eqRefl _))
theorem Tn_congr {K K' : PTm n} (p q : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Tn K p q ≐ Tn K' p q :=
  congrAdd (congrMul (congrMul (congrSucc e) (.eqRefl _)) (Ev_congr p q e))
    (congrMul (.eqRefl _) (congrAp2 powF (congrSucc e) (.eqRefl _)))
theorem Td_congr {K K' : PTm n} (q : PTm n) (e : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] Td K q ≐ Td K' q :=
  congrMul (congrAp2 _ (congrSucc e) (.eqRefl _)) (congrAp2 powF (congrSucc e) (.eqRefl _))

theorem Ed_pos {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (K : PTm n) : Γ ⊢[PRAAx] Ed K q ≐ succ (pred (Ed K q)) :=
  pos_mul (F_pos K) (pos_pw hq K)
theorem Td_pos {q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (K : PTm n) : Γ ⊢[PRAAx] Td K q ≐ succ (pred (Td K q)) :=
  pos_mul (F_pos _) (pos_pw hq _)

/-! ## The one-step comparisons -/

/-- `E_K ≤ E_{K+1}`. -/
theorem e_step (K p q : PTm n) : Γ ⊢[PRAAx] le (Ev K p q * Ed (succ K) q) (Ev (succ K) p q * Ed K q) := by
  have eE := natEq (E_succ (Γ := Γ) K p q)
  have eF := natEq (F_succ (Γ := Γ) K)
  have eP := natEq (pw_succ (Γ := Γ) q K)
  ipra_le 𝔞 (pw p (succ K) * Ed K q) with
    𝔞 (Fv K) * 𝔞 (pw q K) * eE - 𝔞 (Ev K p q) * 𝔞 (pw q (succ K)) * eF -
      𝔞 (Ev K p q) * (𝔞 K + 1) * 𝔞 (Fv K) * eP

/-- `E_K ≤ T_K`. -/
theorem e_up (K p q : PTm n) : Γ ⊢[PRAAx] le (Ev K p q * Td K q) (Tn K p q * Ed K q) := by
  have eF := natEq (F_succ (Γ := Γ) K)
  have eP := natEq (pw_succ (Γ := Γ) q K)
  ipra_le 𝔞 (two * pw p (succ K) * Ed K q) with
    -(𝔞 (Ev K p q) * 𝔞 (pw q (succ K))) * eF - 𝔞 (Ev K p q) * (𝔞 K + 1) * 𝔞 (Fv K) * eP

/-- `T_{K+1} ≤ T_K` for `x = p/q ≤ 1`. -/
theorem t_step {K p q : PTm n} (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (Tn (succ K) p q * Td K q) (Tn K p q * Td (succ K) q) := by
  have eE := natEq (E_succ (Γ := Γ) K p q)
  have eF := natEq (F_succ (Γ := Γ) (succ K))
  have eP := natEq (pw_succ (Γ := Γ) q (succ K))
  have eQ := natEq (pw_succ (Γ := Γ) p (succ K))
  ipra_le 𝔞 (Fv (succ K) * pw q (succ K) * pw p (succ K)) * (𝔞 (K * q) + 2 * sl hpq) with
    -((𝔞 K + 2) * 𝔞 q * 𝔞 (Fv (succ K)) * 𝔞 (pw q (succ K))) * eE -
      2 * 𝔞 (Fv (succ K)) * 𝔞 (pw q (succ K)) * eQ +
      ((𝔞 K + 1) * 𝔞 q * 𝔞 (Ev K p q) + 2 * 𝔞 (pw p (succ K))) * 𝔞 (pw q (succ (succ K))) * eF +
      ((𝔞 K + 1) * 𝔞 q * 𝔞 (Ev K p q) + 2 * 𝔞 (pw p (succ K))) * (𝔞 K + 2) * 𝔞 (Fv (succ K)) * eP

/-! ## The nesting -/

abbrev XF (K j p q : PTm n) : Fm PTm n :=
  le (Ev K p q * Ed (K + j) q) (Ev (K + j) p q * Ed K q) ⋏ le (Tn (K + j) p q * Td K q) (Tn K p q * Td (K + j) q)

theorem xf_step {K j p q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hpq : Γ ⊢[PRAAx] le p q)
    (ih : Γ ⊢[PRAAx] XF K j p q) : Γ ⊢[PRAAx] XF K (succ j) p q := by
  have e : Γ ⊢[PRAAx] succ (K + j) ≐ K + succ j := (add_succ _ _).eqSymm
  have l1 := frac_trans (Ed_pos hq (K + j)) (Prf.andE₁ ih) (e_step (K + j) p q)
  have u1 := frac_trans (Td_pos hq (K + j)) (t_step (K := K + j) hpq) (Prf.andE₂ ih)
  refine .andI ?_ ?_
  · exact le_congr (congrMul (.eqRefl _) (Ed_congr q e)) (congrMul (Ev_congr p q e) (.eqRefl _)) l1
  · exact le_congr (congrMul (Tn_congr p q e) (.eqRefl _)) (congrMul (.eqRefl _) (Td_congr q e)) u1

theorem xf_zero (K p q : PTm n) : Γ ⊢[PRAAx] XF K zero p q := by
  have e : Γ ⊢[PRAAx] K + zero ≐ K := add_zero K
  refine .andI ?_ ?_
  · exact le_congr (congrMul (.eqRefl _) (Ed_congr q e).eqSymm) (congrMul (Ev_congr p q e).eqSymm (.eqRefl _))
      (le_refl _)
  · exact le_congr (congrMul (Tn_congr p q e).eqSymm (.eqRefl _)) (congrMul (.eqRefl _) (Td_congr q e).eqSymm)
      (le_refl _)

/-- The nested names of `e^x`, `0 ≤ x = p/q ≤ 1`: `E_K ≤ E_{K+j}`, `T_{K+j} ≤ T_K` and `E_{K+j} ≤ T_{K+j}`. -/
theorem exp_name {p q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hpq : Γ ⊢[PRAAx] le p q) (K j : PTm n) :
    Γ ⊢[PRAAx] XF K j p q ⋏ le (Ev (K + j) p q * Td (K + j) q) (Tn (K + j) p q * Ed (K + j) q) := by
  have hall : Γ ⊢[PRAAx] Fm.all (XF (Syn.shift K) (var 0) (Syn.shift p) (Syn.shift q)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT]
    · exact xf_zero K p q
    · let Δ : List (Fm PTm (n + 1)) := XF (Syn.shift K) (var 0) (Syn.shift p) (Syn.shift q) :: Γ.map Fm.shift
      have hq' : Δ ⊢[PRAAx] Syn.shift q ≐ succ (pred (Syn.shift q)) := by
        have b := hq.shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
        exact b.wk
      have hpq' : Δ ⊢[PRAAx] le (Syn.shift p) (Syn.shift q) := by
        have b := hpq.shift
        simp only [Fm.shift, subst_le] at b
        exact b.wk
      exact xf_step hq' hpq' Prf.hyp0
  have r := Prf.allE j hall
  simp only [Fm.subst_and, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact .andI r (e_up _ _ _)

/-- `eq:exptail`: `T_K − E_K = 2 p^{K+1}/((K+1)! q^{K+1}) ≤ 2/(K+1)!` for `p ≤ q`. -/
theorem exp_tail {p q : PTm n} (hpq : Γ ⊢[PRAAx] le p q) (K : PTm n) :
    Γ ⊢[PRAAx] le (two * pw p (succ K) * Fv (succ K)) (two * Td K q) := by
  have w := pw_le_pw (Γ := Γ) (succ K) hpq
  ipra_le 2 * 𝔞 (Fv (succ K)) * sl w

/-! ## Monotonicity in `x` -/

abbrev EM (K p q p' q' : PTm n) : Fm PTm n := le (Ev K p q * pw q' K) (Ev K p' q' * pw q K)

theorem em_step {K p q p' q' : PTm n} (hx : Γ ⊢[PRAAx] le (p * q') (p' * q)) (ih : Γ ⊢[PRAAx] EM K p q p' q') :
    Γ ⊢[PRAAx] EM (succ K) p q p' q' := by
  have eE := E_succ (Γ := Γ) K p q
  have eE' := E_succ (Γ := Γ) K p' q'
  have eP := pw_succ (Γ := Γ) q K
  have eP' := pw_succ (Γ := Γ) q' K
  have w := pw_le_pw (Γ := Γ) (succ K) hx
  have w1 := natEq (LocalFactor.pw_mul_base (Γ := Γ) p q' (succ K))
  have w2 := natEq (LocalFactor.pw_mul_base (Γ := Γ) p' q (succ K))
  have e1 := natEq eP
  have e2 := natEq eP'
  have pw1 : Γ ⊢[PRAAx] le (pw p (succ K) * (pw q' K * q')) (pw p' (succ K) * (pw q K * q)) := by
    ipra_le sl w with w1 - w2 + 𝔞 (pw p (succ K)) * e2 - 𝔞 (pw p' (succ K)) * e1
  refine le_congr (congrMul eE eP').eqSymm (congrMul eE' eP).eqSymm ?_
  ipra_le 𝔞 (succ K * q * q') * sl ih + sl pw1

/-- `E_K(p/q) ≤ E_K(p'/q')` for `p/q ≤ p'/q'`. -/
theorem e_mono {p q p' q' : PTm n} (hx : Γ ⊢[PRAAx] le (p * q') (p' * q)) (K : PTm n) :
    Γ ⊢[PRAAx] le (Ev K p q * Ed K q') (Ev K p' q' * Ed K q) := by
  have hall : Γ ⊢[PRAAx] Fm.all (EM (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift p') (Syn.shift q')) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
    · have a := natEq (E_zero (Γ := Γ) p q)
      have b := natEq (E_zero (Γ := Γ) p' q')
      have c := natEq (pw_zero (Γ := Γ) q)
      have d := natEq (pw_zero (Γ := Γ) q')
      ipra_le 0 with 𝔞 (pw q zero) * b - 𝔞 (pw q' zero) * a + c - d
    · have hx' : (EM (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift p') (Syn.shift q') :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift p * Syn.shift q') (Syn.shift p' * Syn.shift q) := by
        have b := hx.shift
        simp only [Fm.shift, subst_le, PTm.subst_mul] at b
        exact b.wk
      exact em_step hx' Prf.hyp0
  have r := Prf.allE K hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  ipra_le 𝔞 (Fv K) * sl r

end LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName
