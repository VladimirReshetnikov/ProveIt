import IPRADerivations.AnalyticNumberTheory.RateShell

/-!
# Growth and bounded weighted series are equivalent in iPRA (`riemann_ipra_equivalences_2026-11-20`, `thm:rate`)

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `series.tex`, Theorem `thm:rate`: "the following
are equivalent by primitive-recursive witness transformations. (1) For each `r` there is `c` with
`|M(N)|^{2r} ≤ cN^{r+1}` for all `N ≥ 1`. (2) For each `r` there is `K` with `|S_r(N)| ≤ 2^K` for all `N`."

Here `r = k + 1`, `S_r(N) = W(N)/u_N` (`RateAbel.Wv`), and the sentences are

* (1) `PowerDivisorGrowth.GrowthS (AB a⁺) (AB a⁻) y`: `∀k ∃c ∀N |M(N)|^{2(k+1)} ≤ c N^{k+2}`;
* (2) `RateS`: `∀k ∃K ∀N |W(N)| ≤ 2^K u_N` (`RMat`).

* `rate_to_growth` ((2) ⇒ (1)): `RateAbel.recover`, witness `c = 2^{2r(K+1)}`;
* `growth_to_rate` ((1) ⇒ (2)): the input at `k' = 2k+1` (index `2r`) and `RateShell.w_all`, witness
  `K = c + r + 4`;
* `rate_iff`: `(1) ↔ (2)` in object iPRA, for arbitrary signed coefficient bodies.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RateIff

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RateAbel
open LeanProofs.IPRA.AnalyticNumberTheory.RateShell
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (aP aN : PTm 2)

/-- `|W(N)| ≤ 2^K u_N` at `r = k + 1`. -/
abbrev RMat (x k K N : PTm n) : Fm PTm n :=
  le (absd (Wv aP (succ k) x N) (Wv aN (succ k) x N)) (pw two K * uu (succ k) N)

theorem subst_RMat {m : ℕ} (σ : Fin n → PTm m) (x k K N : PTm n) :
    (RMat aP aN x k K N).subst σ = RMat aP aN (Syn.subst σ x) (Syn.subst σ k) (Syn.subst σ K) (Syn.subst σ N) := by
  simp [RMat, subst_le, subst_ap2, LeanProofs.IPRA.PTm.subst_pred]

/-- (2): `∀k ∃K ∀N |W(N)| ≤ 2^K u_N`. -/
abbrev RateS (y : PTm n) : Fm PTm n :=
  Fm.all (Fm.ex (Fm.all (RMat aP aN (Syn.shift (Syn.shift (Syn.shift y))) (var 2) (var 1) (var 0))))

/-- The output of (2) ⇒ (1): `c = 2^{2r(K+1)}`, `r = k + 1`. -/
abbrev Crec (k K : PTm n) : PTm n := pw two (two * succ k * succ K)

/-- One `∀N` of (2) ⇒ (1). -/
theorem back_all {y k K : PTm n} {X Kk KK X' K' C' : PTm (n + 1)}
    (hX : X = Syn.shift y) (hk : Kk = Syn.shift k) (hK : KK = Syn.shift K)
    (hX' : X' = Syn.shift y) (hK' : K' = Syn.shift k) (hC' : C' = Syn.shift (Crec k K))
    (H : Γ ⊢[PRAAx] Fm.all (RMat aP aN X Kk KK (var 0))) :
    Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) X' K' C' (var 0)) := by
  subst hX hk hK hX' hK' hC'
  refine .allI ?_
  have hr : (Γ.map Fm.shift) ⊢[PRAAx] le one (succ (Syn.shift k)) := by ipra_le 𝔞 (Syn.shift k)
  have hW : (Γ.map Fm.shift) ⊢[PRAAx] WBound aP aN (succ (Syn.shift k)) (Syn.shift y) (Syn.shift K) := by
    have h := H.shift
    simp only [Fm.shift, Fm.subst_all, subst_RMat, up1_v0, subst_up_shift_pal, subst_sh] at h
    have e1 : Syn.shift (succ (Syn.shift k)) = succ (Syn.shift (Syn.shift k)) := by simp [Syn.shift]
    simp only [WBound, e1]
    exact h
  have f := recover aP aN hr hW (var 0)
  have e2 : Syn.shift (Crec k K) = Crec (Syn.shift k) (Syn.shift K) := by simp [Syn.shift]
  rw [e2]
  simp only [Mat, inst2_AB]
  exact f

/-- `thm:rate` (2) ⇒ (1). -/
theorem rate_to_growth (y : PTm n) :
    Γ ⊢[PRAAx] RateS aP aN y ⟶ GrowthS (AB aP) (AB aN) y := by
  refine all_ex_imp (Crec (var 1) (var 0)) ?_
  simp only [GrowthS, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ]
  exact back_all aP aN (y := Syn.shift (Syn.shift y)) (k := var 1) (K := var 0)
    (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
    (by simp [Syn.shift]) Prf.hyp0

/-- One `∀N` of (1) ⇒ (2). -/
theorem fwd_all {y k c : PTm n} {X K C X' Kk KK : PTm (n + 1)}
    (hX : X = Syn.shift y) (hK : K = Syn.shift (succ (two * k))) (hC : C = Syn.shift c)
    (hX' : X' = Syn.shift y) (hk : Kk = Syn.shift k) (hKK : KK = Syn.shift (Kc (succ k) c))
    (H : Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) X K C (var 0))) :
    Γ ⊢[PRAAx] Fm.all (RMat aP aN X' Kk KK (var 0)) := by
  subst hX hK hC hX' hk hKK
  have hr : Γ ⊢[PRAAx] le one (succ k) := by ipra_le 𝔞 k
  have hc : Γ ⊢[PRAAx] InM aP aN (succ k) c y := by
    refine .allI ?_
    have b := H.allOpen
    simp only [Mat, inst2_AB] at b
    rw [show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
    rw [show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
    have ex := exps (Γ := Γ.map Fm.shift) (Syn.shift k)
    exact le_congr (congrPw (.eqRefl _) ex.1) (congrMul (.eqRefl _) (congrPw (.eqRefl _) ex.2)) b
  have w := w_all aP aN hr hc
  simp only [WBound] at w
  have e1 : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
  rw [e1] at w
  exact w

/-- `thm:rate` (1) ⇒ (2). -/
theorem growth_to_rate (y : PTm n) :
    Γ ⊢[PRAAx] GrowthS (AB aP) (AB aN) y ⟶ RateS aP aN y := by
  refine all_ex_imp_at (succ (two * var 0)) (Kc (succ (var 1)) (var 0)) ?_
  simp only [GrowthS, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_Mat, up3_v0, up3_v1, up3_v2, up2_v0, up2_v1, up2_v2,
    up1_v0, up1_v1, up1_v2, inst_v0, inst_v1, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, RateS, subst_RMat]
  exact fwd_all aP aN (y := Syn.shift (Syn.shift y)) (k := var 1) (c := var 0)
    (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
    (by simp [Syn.shift]) Prf.hyp0

/-- `thm:rate`, (1) ↔ (2): `(∀k ∃c ∀N |M(N)|^{2(k+1)} ≤ cN^{k+2}) ↔ (∀k ∃K ∀N |S_{k+1}(N)| ≤ 2^K)` in object iPRA,
for arbitrary signed coefficient bodies, with the packet's witnesses `K = c + r + 4` and `c = 2^{2r(K+1)}`. -/
theorem rate_iff (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (GrowthS (AB aP) (AB aN) y) (RateS aP aN y) :=
  .andI (growth_to_rate aP aN y) (rate_to_growth aP aN y)

end LeanProofs.IPRA.AnalyticNumberTheory.RateIff
