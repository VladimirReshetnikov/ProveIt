import IPRADerivations.AnalyticNumberTheory.EulerProduct

/-!
# The radical identity

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-rad`:
`φ(n) rad(n) = n φ(rad(n))`, with `rad(n) = ∏_{p ∣ n} p` (`EulerProduct.PP F₁`).

* `peel` data (reusable): for `p ∣ n`, `n ≥ 1`, `p` prime: `v_p(n) ≥ 1`, the cofactor `m ≥ 1`,
  `p ∤ m`, and `m < n`;
* `rad_pos`: `rad(n) ≥ 1`; `rad_dvd`: `rad(n) ∣ n`;
* `phi_rad`: `φ(rad n) = ∏_{p ∣ n} (p − 1)`, peeling `lpf(n)`:
  `rad(p^a m) = rad(m) p` with `gcd(rad m, p) = 1`;
* `radical_identity`: combine with `EulerProduct.euler_product_at`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.Radical

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody coprime_pow totient_prime_power_at)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Peeling data -/

section PeelData

variable {N p : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
  (hpN : Γ ⊢[PRAAx] dvd p N)
include hN hp hpN

theorem two_le_of_prime : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h

theorem val_pos : Γ ⊢[PRAAx] val p N ≐ succ (pred (val p N)) :=
  val_eq_succ_pred_of_dvd (two_le_of_prime hN hp hpN) hN hpN

theorem cof_rem_pos : Γ ⊢[PRAAx] rem (quo N (pw p (val p N))) p ≐ succ (pred (rem (quo N (pw p (val p N))) p)) :=
  cof_rem_eq_succ_pred (two_le_of_prime hN hp hpN) hN

theorem cof_pos : Γ ⊢[PRAAx] quo N (pw p (val p N)) ≐ succ (pred (quo N (pw p (val p N)))) :=
  cof_eq_succ_pred (two_le_of_prime hN hp hpN) hN

theorem cof_lt : Γ ⊢[PRAAx] lt (quo N (pw p (val p N))) N :=
  cof_lt_of_dvd (two_le_of_prime hN hp hpN) hN hpN

end PeelData

/-! ## `rad(n) ≥ 1` -/

abbrev rad (N : PTm n) : PTm n := PP F₁ N

theorem pB_pos (q x : PTm n) : Γ ⊢[PRAAx] inst2 (pB F₁) q x ≐ succ (pred (inst2 (pB F₁) q x)) := by
  rw [inst2_pB, inst2_F₁, inst2_e]
  refine .orE (isP_01 q) ?_ ?_
  · refine eq_succ_pred (y := zero) ((congrAp2 powF ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))
      (.eqRefl _)).eqTrans (pw_zero _))
  · exact pw_pos' (prime_eq_succ_pred (prime_of_isP Prf.hyp0)) _

/-- Variables: `0 = K`, `1 = x`. -/
private abbrev radPosF : Fm PTm 2 :=
  ap2 (prodF (pB F₁)) (var 0) (var 1) ≐ succ (pred (ap2 (prodF (pB F₁)) (var 0) (var 1)))

private theorem rad_pos₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] radPosF := by
  ipra_ind [subst_ap2]
  · exact eq_succ_pred (prod_zero _ _)
  · refine (prod_succ _ _ _).eqTrans ?_
    have t := pB_pos (Γ := [radPosF]) (var 0 : PTm 2) (var 1)
    exact eq_succ_pred ((pos_mul Prf.hyp0 t).eqTrans (.eqRefl _)) |>.eqTrans
      (congrSucc (congrPred (prod_succ _ _ _).eqSymm))

theorem rad_pos (N : PTm n) : Γ ⊢[PRAAx] rad N ≐ succ (pred (rad N)) := by
  have h := inst (Γ := Γ) rad_pos₀ (![succ N, N] : Fin 2 → PTm n)
  simpa using h

theorem pp_zero (F : PTm 2) : Γ ⊢[PRAAx] PP F (zero : PTm n) ≐ one := by
  refine (prod_succ _ _ _).eqTrans ((congrMul (prod_zero _ _) (.eqRefl _)).eqTrans ?_)
  have t₀ : Γ ⊢[PRAAx] inst2 (pB F) zero zero ≐ one := by
    rw [inst2_pB, inst2_e]
    exact (congrAp2 powF ((congrMul isP_zero (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (pw_zero _)
  exact (congrMul (.eqRefl _) t₀).eqTrans (by ipra_ring)

/-- The common peel: `rad(n) = rad(m) p` and `∏_{F₂}(n) = ∏_{F₂}(m)(p − 1)` for `n = p^a m`. -/
theorem rad_peel {N p : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) :
    Γ ⊢[PRAAx] rad N ≐ rad (quo N (pw p (val p N))) * p := by
  have hNe := cof_eq (m := N) (two_le_of_prime hN hp hpN)
  have h := pp_peel hp (val_pos hN hp hpN) (cof_rem_pos hN hp hpN) (cof_pos hN hp hpN) F₁ hF₁
  rw [inst2_F₁] at h
  exact (congrAp2 (prodF (pB F₁)) (congrSucc hNe) hNe).eqTrans h

theorem pm_peel {N p : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) :
    Γ ⊢[PRAAx] PP F₂ N ≐ PP F₂ (quo N (pw p (val p N))) * monus p one := by
  have hNe := cof_eq (m := N) (two_le_of_prime hN hp hpN)
  have h := pp_peel hp (val_pos hN hp hpN) (cof_rem_pos hN hp hpN) (cof_pos hN hp hpN) F₂ hF₂
  rw [inst2_F₂] at h
  exact (congrAp2 (prodF (pB F₂)) (congrSucc hNe) hNe).eqTrans h

/-! ## `rad(n) ∣ n` -/

abbrev rdB : PTm 2 := sg (rem (var 0) (rad (var 0)))

theorem inst2_rd (N x : PTm n) : inst2 rdB N x = sg (rem N (rad N)) := by simp [inst2]

theorem rd_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) (hV : Γ ⊢[PRAAx] ap2 (sumF rdB) N x ≐ zero) :
    Γ ⊢[PRAAx] dvd (rad N) N := by
  have h₀ := sum_zero_elim rdB hV (cof_lt hN hp hpN)
  rw [inst2_rd] at h₀
  have ih := PhiDivides.sg_zero_inv h₀
  refine dvd_of_eq' (rad_pos N) (w := pw p (pred (val p N)) *
    quo (quo N (pw p (val p N))) (rad (quo N (pw p (val p N))))) ?_
  ipra_lc natEq (cof_eq (m := N) (two_le_of_prime hN hp hpN)) +
    Groth.ι (Q.mk _ (quo N (pw p (val p N)))) * natEq ((congrAp2 powF (val_pos hN hp hpN) (.eqRefl p)).eqTrans (pw_succ p (pred (val p N)))) +
    Groth.ι (Q.mk _ (pw p (pred (val p N)))) * Groth.ι (Q.mk _ p) * natEq (eq_of_dvd' (rad_pos _) ih) -
    Groth.ι (Q.mk _ (pw p (pred (val p N)))) * Groth.ι (Q.mk _ (quo (quo N (pw p (val p N))) (rad (quo N (pw p (val p N)))))) * natEq (rad_peel hN hp hpN)

theorem rd_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF rdB) N x ≐ zero) : Γ ⊢[PRAAx] dvd (rad N) N := by
  refine .orE (zero_or_succ N) ((congrAp2 remF Prf.hyp0 (.eqRefl _)).eqTrans (rem_zero _)) ?_
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ one :=
      Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    exact (congrAp2 remF e ((congrAp2 (prodF (pB F₁)) (congrSucc e) e).eqTrans (pp_one F₁))).eqTrans (Euler.rem_one _)
  · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx]
        N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    exact rd_found Prf.hyp1 (lpf_prime _) (dvd_congr e.eqSymm (Prf.andE₁ (lpf_dvd _))) hV.wk.wk

private abbrev rdF : Fm PTm 2 := ap2 (sumF rdB) (var 0) (var 1) ≐ zero

private theorem rd₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] rdF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_rd]
    exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (rd_step Prf.hyp0))).eqTrans sg_zero

/-- `rad(n) ∣ n`. -/
theorem rad_dvd (N : PTm n) : Γ ⊢[PRAAx] dvd (rad N) N := by
  have h := inst (Γ := Γ) rd₀ (![succ N, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim_last rdB h
  rw [inst2_rd] at z
  exact PhiDivides.sg_zero_inv z

/-! ## `φ(rad n) = ∏_{p ∣ n} (p − 1)` -/

abbrev prB : PTm 2 := monus one (eqb (phi (rad (var 0))) (PP F₂ (var 0)))

theorem inst2_pr (N x : PTm n) : inst2 prB N x = monus one (eqb (phi (rad N)) (PP F₂ N)) := by simp [inst2]

/-- `φ(p) = p − 1` for a prime `p`. -/
theorem phi_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] phi p ≐ monus p one := by
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  have t := totient_prime_power_at (k := zero) hp
  have e₁ : Γ ⊢[PRAAx] pw p (succ zero) ≐ p := pw_one _
  have t' := (congrAdd (congrAp2 (sumF totBody) e₁ e₁) (pw_zero _)).eqSymm.eqTrans (t.eqTrans e₁)
  ipra_lc natEq t' + natEq (eq_add_of_le (le_trans (le_succ_self one) hp2))

theorem pr_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) (hV : Γ ⊢[PRAAx] ap2 (sumF prB) N x ≐ zero) :
    Γ ⊢[PRAAx] phi (rad N) ≐ PP F₂ N := by
  have h₀ := sum_zero_elim prB hV (cof_lt hN hp hpN)
  rw [inst2_pr] at h₀
  have ih := EulerProduct.eq_of_viol h₀
  have hp1 := prime_eq_succ_pred hp
  have hr := rad_pos (Γ := Γ) (quo N (pw p (val p N)))
  have hnd : Γ ⊢[PRAAx] neg (dvd p (rad (quo N (pw p (val p N))))) := by
    refine .impI (succ_ne_zero' _ ((cof_rem_pos hN hp hpN).wk.eqSymm.eqTrans ?_))
    exact dvd_trans' hp1.wk hr.wk Prf.hyp0 (rad_dvd _)
  have hg := gcd_comm_one hr (gcd_prime hp hnd)
  have hmul := Multiplicative.phi_mul_at hr hp1 hg
  have hrp := rad_peel hN hp hpN
  refine (congrAp2 (sumF totBody) hrp hrp).eqTrans (hmul.eqTrans ?_)
  exact (congrMul ih (phi_prime hp)).eqTrans (pm_peel hN hp hpN).eqSymm

theorem pr_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF prB) N x ≐ zero) :
    Γ ⊢[PRAAx] phi (rad N) ≐ PP F₂ N := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have e : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    have r0 := (congrAp2 (prodF (pB F₁)) (congrSucc e) e).eqTrans (pp_zero F₁)
    exact (congrAp2 (sumF totBody) r0 r0).eqTrans (phi_one.eqTrans
      ((congrAp2 (prodF (pB F₂)) (congrSucc e) e).eqTrans (pp_zero F₂)).eqSymm)
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ one :=
      Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    have r1 := (congrAp2 (prodF (pB F₁)) (congrSucc e) e).eqTrans (pp_one F₁)
    exact (congrAp2 (sumF totBody) r1 r1).eqTrans (phi_one.eqTrans
      ((congrAp2 (prodF (pB F₂)) (congrSucc e) e).eqTrans (pp_one F₂)).eqSymm)
  · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx]
        N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    exact pr_found Prf.hyp1 (lpf_prime _) (dvd_congr e.eqSymm (Prf.andE₁ (lpf_dvd _))) hV.wk.wk

private abbrev prF : Fm PTm 2 := ap2 (sumF prB) (var 0) (var 1) ≐ zero

private theorem pr₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] prF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_pr]
    exact EulerProduct.viol_of_eq (pr_step Prf.hyp0)

theorem phi_rad (N : PTm n) : Γ ⊢[PRAAx] phi (rad N) ≐ PP F₂ N := by
  have h := inst (Γ := Γ) pr₀ (![succ N, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim_last prB h
  rw [inst2_pr] at z
  exact EulerProduct.eq_of_viol z

/-! ## The identity -/

/-- `thm:phi-rad` at an arbitrary `n`: `φ(n) rad(n) = n φ(rad(n))`. -/
theorem radical_identity_at (N : PTm n) : Γ ⊢[PRAAx] phi N * rad N ≐ N * phi (rad N) :=
  (euler_product_at N).eqTrans (congrMul (.eqRefl _) (phi_rad N).eqSymm)

/-- `thm:phi-rad`: `φ(n) rad(n) = n φ(rad(n))`, with `rad(n) = ∏_{p ∣ n} p`. -/
abbrev radicalFormula : Fm PTm 1 := phi (var 0) * rad (var 0) ≐ var 0 * phi (rad (var 0))

theorem radical_identity : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 radicalFormula :=
  closeUniv 1 (radical_identity_at (var 0))

end LeanProofs.IPRA.AnalyticNumberTheory.Radical

export_ipra AnalyticNumberTheory.Radical (cof_rem_pos two_le_of_prime val_pos)
