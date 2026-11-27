import IPRADerivations.AnalyticNumberTheory.RateCauchy

/-!
# The Cauchy-modulus form of `thm:rate` (`riemann_ipra_equivalences_2026-11-20`, `thm:rate` (1) ⇔ (3))

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `series.tex`, Theorem `thm:rate` (3): "For each `r`
there is `K` satisfying the preceding prefix bound and `P, Q ≥ 2^{4r(t+K)} ⟹ |S_r(P) − S_r(Q)| ≤ 2^{−t}` (`t ≥ 0`)."

`Rate3S` is `∀k ∃K ((∀N |W(N)| ≤ 2^K u_N) ∧ ∀t ∀P ∀Q (P ≥ 2^{4r(t+K)} → Q ≥ 2^{4r(t+K)} →
2^t |W(P)u_Q − W(Q)u_P| ≤ u_P u_Q))` with `r = k + 1` (the second matrix is `CMat`).

* `growth_to_rate3` ((1) ⇒ (3)): one witness `K = c + r + 4` serves the prefix bound (`RateIff.fwd_all`) and the
  modulus (`RateCauchy.cauchy`, through `cauchy_all`);
* `rate3_to_rate` ((3) ⇒ (2)) drops the modulus;
* `rate3_iff`: `(1) ↔ (3)` in object iPRA.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RateCauchyIff

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RateAbel
open LeanProofs.IPRA.AnalyticNumberTheory.RateShell
open LeanProofs.IPRA.AnalyticNumberTheory.RateIff
open LeanProofs.IPRA.AnalyticNumberTheory.RateCauchy
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (k4)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (aP aN : PTm 2)

/-- `P, Q ≥ 2^{4r(t+K)} → 2^t |W(P)u_Q − W(Q)u_P| ≤ u_P u_Q` at `r = k + 1`. -/
abbrev CMat (x k K t P Q : PTm n) : Fm PTm n :=
  le (pw two (k4 (succ k) * (t + K))) P ⟶ le (pw two (k4 (succ k) * (t + K))) Q ⟶
    le (pw two t * absd (XP aP aN (succ k) x P Q) (XN aP aN (succ k) x P Q)) (UU (succ k) P Q)

theorem subst_CMat {m : ℕ} (σ : Fin n → PTm m) (x k K t P Q : PTm n) :
    (CMat aP aN x k K t P Q).subst σ = CMat aP aN (Syn.subst σ x) (Syn.subst σ k) (Syn.subst σ K) (Syn.subst σ t)
      (Syn.subst σ P) (Syn.subst σ Q) := by
  simp [CMat, subst_le, subst_ap2, LeanProofs.IPRA.PTm.subst_pred]

theorem upf_four {a b : ℕ} (σ : Fin (a + 4) → PTm b) : (up σ : Fin (a + 5) → PTm (b + 1)) 4 = Syn.shift (σ 3) := rfl

/-- (3). -/
abbrev Rate3S (y : PTm n) : Fm PTm n :=
  Fm.all (Fm.ex (Fm.and (Fm.all (RMat aP aN (Syn.shift (Syn.shift (Syn.shift y))) (var 2) (var 1) (var 0)))
    (Fm.all (Fm.all (Fm.all (CMat aP aN
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift (Syn.shift y))))) (var 4) (var 3) (var 2) (var 1) (var 0)))))))

theorem inm_shift (r c y : PTm n) : Fm.shift (InM aP aN r c y) = InM aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) := by
  ipra_ind_simp [InM, Fm.shift, Fm.subst_all, subst_le, subst_ap2, Syn.up_zero, subst_up_shift_pal, subst_sh]

/-- The modulus part of (1) ⇒ (3), under its three binders. -/
theorem cauchy_all {y k c : PTm n} {X K C : PTm (n + 1)} {X3 k3 K3 : PTm (n + 3)}
    (hX : X = Syn.shift y) (hK : K = Syn.shift (succ (two * k))) (hC : C = Syn.shift c)
    (hX3 : X3 = Syn.shift (Syn.shift (Syn.shift y))) (hk3 : k3 = Syn.shift (Syn.shift (Syn.shift k)))
    (hK3 : K3 = Kc (succ (Syn.shift (Syn.shift (Syn.shift k)))) (Syn.shift (Syn.shift (Syn.shift c))))
    (H : Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) X K C (var 0))) :
    Γ ⊢[PRAAx] Fm.all (Fm.all (Fm.all (CMat aP aN X3 k3 K3 (var 2) (var 1) (var 0)))) := by
  subst hX hK hC hX3 hk3 hK3
  have hc : Γ ⊢[PRAAx] InM aP aN (succ k) c y := by
    refine .allI ?_
    have b := H.allOpen
    simp only [Mat, inst2_AB] at b
    rw [show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
    rw [show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
    have ex := exps (Γ := Γ.map Fm.shift) (Syn.shift k)
    exact le_congr (congrPw (.eqRefl _) ex.1) (congrMul (.eqRefl _) (congrPw (.eqRefl _) ex.2)) b
  have hc3 : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      InM aP aN (succ (Syn.shift (Syn.shift (Syn.shift k)))) (Syn.shift (Syn.shift (Syn.shift c)))
        (Syn.shift (Syn.shift (Syn.shift y))) := by
    have b := hc.shift.shift.shift
    rw [inm_shift, inm_shift, inm_shift] at b
    rw [show Syn.shift (Syn.shift (Syn.shift (succ k))) = succ (Syn.shift (Syn.shift (Syn.shift k))) by
      simp [Syn.shift]] at b
    exact b
  have hr : ((Γ.map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx] le one (succ (Syn.shift (Syn.shift (Syn.shift k)))) := by
    ipra_le 𝔞 (Syn.shift (Syn.shift (Syn.shift k)))
  refine .allI (.allI (.allI (.impI (.impI ?_))))
  exact cauchy aP aN hr.wk.wk hc3.wk.wk Prf.hyp1 Prf.hyp0

/-- `thm:rate` (1) ⇒ (3). -/
theorem growth_to_rate3 (y : PTm n) :
    Γ ⊢[PRAAx] GrowthS (AB aP) (AB aN) y ⟶ Rate3S aP aN y := by
  refine all_ex_imp_at (succ (two * var 0)) (Kc (succ (var 1)) (var 0)) ?_
  simp only [Fm.subst_all, subst_Mat, inst_v0, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ, Fm.subst_and, subst_RMat,
    subst_CMat, LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorUniform.upf_three, upf_four]
  refine .andI ?_ ?_
  · exact fwd_all aP aN (y := Syn.shift (Syn.shift y)) (k := var 1) (c := var 0)
      (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
      (by simp [Syn.shift]) Prf.hyp0
  · exact cauchy_all aP aN (y := Syn.shift (Syn.shift y)) (k := var 1) (c := var 0)
      (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
      (by simp [Syn.shift])
      (by simp [Syn.shift])
      (by simp [Syn.shift]) Prf.hyp0

/-- Renaming the binder forms of a prefix-bound matrix. -/
theorem rmat_eq {X k K X' k' K' : PTm (n + 1)} (hX : X = X') (hk : k = k') (hK : K = K')
    (H : Γ ⊢[PRAAx] Fm.all (RMat aP aN X k K (var 0))) : Γ ⊢[PRAAx] Fm.all (RMat aP aN X' k' K' (var 0)) := by
  subst hX hk hK; exact H

/-- `thm:rate` (3) ⇒ (2). -/
theorem rate3_to_rate (y : PTm n) : Γ ⊢[PRAAx] Rate3S aP aN y ⟶ RateS aP aN y := by
  refine all_ex_imp (var 0) ?_
  simp only [Fm.subst_all, subst_RMat, inst_v0, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ]
  exact rmat_eq aP aN (by simp [Syn.shift]) (by simp) (by simp) (Prf.andE₁ Prf.hyp0)

/-- `thm:rate`, (1) ↔ (3): growth is equivalent to bounded weighted sums with the explicit Cauchy modulus
`P, Q ≥ 2^{4r(t+K)} ⟹ |S_r(P) − S_r(Q)| ≤ 2^{−t}`, in object iPRA. -/
theorem rate3_iff (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (GrowthS (AB aP) (AB aN) y) (Rate3S aP aN y) :=
  .andI (growth_to_rate3 aP aN y) (Prf.impTrans (rate3_to_rate aP aN y) (rate_to_growth aP aN y))

end LeanProofs.IPRA.AnalyticNumberTheory.RateCauchyIff
