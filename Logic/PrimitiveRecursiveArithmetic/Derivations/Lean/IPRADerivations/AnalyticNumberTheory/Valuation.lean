import IPRADerivations.AnalyticNumberTheory.PhiDivides
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Prime-power parts and a prime indicator

Reusable infrastructure for the factorization-based results of
`analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`.

* `lt_pw`: `m < p^m` for `p ≥ 2`;
* the valuation `val p m = μ e ≤ m. p^{e+1} ∤ m` (a bounded search), with `p^v ∣ m`
  (`val_dvd`), `p^{v+1} ∤ m` (`val_not_dvd`), and the cofactor `m = p^v m′` with `p ∤ m′`
  (`cof_eq`, `cof_not_dvd`);
* the prime indicator `isP q = sg(q − 1) · [lpf q = q]`, with `isP q = 1 ⟺ prime q`
  (`isP_of_prime`, `prime_of_isP`) and `isP q ∈ {0, 1}` (`isP_01`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.Valuation

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf μz lpf_dvd lpf_prime prime eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 inst2_lift3 at_pair rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_eq')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `m < p^m` -/

theorem lt_pw_step {p m : PTm n} (hp : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] lt m (pw p m)) :
    Γ ⊢[PRAAx] lt (succ m) (pw p (succ m)) := by
  refine le_congr (.eqRefl _) (pw_succ _ _).eqSymm (le_of_eq_add (d := m + (monus (pw p m) (succ m) +
    monus (pw p m) (succ m)) + monus p two * pw p m) ?_)
  ipra_lc (Groth.ι (Q.mk _ p) - Groth.ι (Q.mk _ (monus p two))) * natEq (eq_add_of_le h) +
    (Groth.ι (Q.mk _ m) + 1 + Groth.ι (Q.mk _ (monus (pw p m) (succ m)))) * natEq (eq_add_of_le hp)

/-- Variables: `0 = m`, `1 = p`. -/
private abbrev ltPwF : Fm PTm 2 := le two (var 1) ⟶ lt (var 0) (pw (var 1) (var 0))

private theorem lt_pw₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] ltPwF := by
  ipra_ind (⟨le_QF _ _, lt_QF _ _⟩) [subst_le, subst_lt, subst_ap2]
  · exact .impI (lt_congr (.eqRefl _) (pw_zero _).eqSymm (zero_lt_succ _))
  · exact .impI (lt_pw_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

theorem lt_pw {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) (m : PTm n) : Γ ⊢[PRAAx] lt m (pw p m) := by
  have h := inst (Γ := Γ) lt_pw₀ (![m, p] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact .impE h hp

theorem pw_pos' {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (k : PTm n) :
    Γ ⊢[PRAAx] pw p k ≐ succ (pred (pw p k)) :=
  eq_succ_pred ((congrAp2 powF (.eqRefl _) hp).eqTrans (DiophantineNumberTheory.FLTMultiples.pw_pos _ _))

/-! ## Indicator facts -/

theorem eq_of_eqb_ne {a b : PTm n} (h : Γ ⊢[PRAAx] neg (eqb a b ≐ zero)) : Γ ⊢[PRAAx] a ≐ b := by
  refine .orE (eq_or_ne a b) Prf.hyp0 ?_
  exact .botE _ (.impE h.wk (eqb_of_ne Prf.hyp0))

theorem ne_of_eqb_zero {a b : PTm n} (h : Γ ⊢[PRAAx] eqb a b ≐ zero) : Γ ⊢[PRAAx] neg (a ≐ b) :=
  .impI (succ_ne_zero' _ (a := zero) ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans h.wk))

/-! ## The valuation -/

/-- `[p^{e+1} ∣ m]`, over `0 = e`, `1 = p`, `2 = m`. -/
abbrev vB3 : PTm 3 := eqb (rem (var 2) (pw (var 1) (succ (var 0)))) zero

abbrev vB : PTm 2 := lift3 vB3

theorem inst3_vB (e p m : PTm n) : inst3 vB3 e p m = eqb (rem m (pw p (succ e))) zero := by
  simp only [inst3, subst_eqb, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem at_vB (e p m : PTm n) :
    Γ ⊢[PRAAx] inst2 vB e (pairT p m) ≐ eqb (rem m (pw p (succ e))) zero :=
  (at_pair vB3 e p m).eqTrans (by rw [inst3_vB]; exact .eqRefl _)

/-- `v_p(m)`: the least `e ≤ m` with `p^{e+1} ∤ m`. -/
abbrev val (p m : PTm n) : PTm n := Search.mu vB (succ m) (pairT p m)

section Val

variable {p m : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
include hp hm

theorem val_found : Γ ⊢[PRAAx] inst2 vB (val p m) (pairT p m) ≐ zero := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) := AnalyticNumberTheory.Euler.N_pos hp
  have hf : Γ ⊢[PRAAx] inst2 vB m (pairT p m) ≐ zero := by
    refine (at_vB m p m).eqTrans (eqb_of_ne (.impI ?_))
    have l := dvd_le' (pw_pos' hp1.wk (succ m)) Prf.hyp0 hm.wk
    exact not_succ_le_self m _ (le_trans (le_succ_self _) (le_trans (lt_pw hp.wk (succ m)) l))
  exact Prf.andE₁ (Prf.andE₂ (Search.search_found (f := vB) (N := succ m) hf
    ((succ_monus_succ _ _).eqTrans (le_refl m))))

/-- `p^{v+1} ∤ m`. -/
theorem val_not_dvd : Γ ⊢[PRAAx] neg (dvd (pw p (succ (val p m))) m) :=
  ne_of_eqb_zero ((at_vB _ p m).eqSymm.eqTrans (val_found hp hm))

omit hp hm in
/-- `p^v ∣ m`. -/
theorem val_dvd {p m : PTm n} : Γ ⊢[PRAAx] dvd (pw p (val p m)) m := by
  refine .orE (zero_or_succ (val p m)) ?_ ?_
  · exact (congrAp2 remF (.eqRefl _) ((congrAp2 powF Prf.hyp0 (.eqRefl _)).eqTrans (pw_zero _))).eqTrans
      (rem_one _)
  · have hlt : ((val p m ≐ succ (pred (val p m))) :: Γ) ⊢[PRAAx] lt (pred (val p m)) (val p m) :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_refl _)
    have hne := Search.search_minimal (f := vB) hlt
    have h := eq_of_eqb_ne (.impI (.impE hne.wk ((at_vB _ p m).eqTrans Prf.hyp0)))
    exact (congrAp2 remF (.eqRefl _) (congrAp2 powF Prf.hyp0 (.eqRefl _))).eqTrans h

omit hm in
theorem pw_val_pos : Γ ⊢[PRAAx] pw p (val p m) ≐ succ (pred (pw p (val p m))) :=
  pw_pos' (AnalyticNumberTheory.Euler.N_pos hp) _

omit hm in
/-- `m = p^v m′`. -/
theorem cof_eq : Γ ⊢[PRAAx] m ≐ pw p (val p m) * quo m (pw p (val p m)) :=
  eq_of_dvd' (pw_val_pos hp) val_dvd

/-- `p ∤ m′`. -/
theorem cof_not_dvd : Γ ⊢[PRAAx] neg (dvd p (quo m (pw p (val p m)))) := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) := AnalyticNumberTheory.Euler.N_pos hp
  refine .impI (.impE (val_not_dvd hp.wk hm.wk) ?_)
  refine dvd_of_eq' (pw_pos' hp1.wk _) (w := quo (quo m (pw p (val p m))) p) ?_
  ipra_lc natEq ((cof_eq (m := m) hp).wk (ψ := dvd p (quo m (pw p (val p m))))) +
    Groth.ι (Q.mk _ (pw p (val p m))) * natEq (eq_of_dvd' hp1.wk (Prf.hyp0 : (dvd p (quo m (pw p (val p m))) :: Γ) ⊢[PRAAx] _)) -
    Groth.ι (Q.mk _ (quo (quo m (pw p (val p m))) p)) * natEq ((pw_succ (Γ := Γ) p (val p m)).wk (ψ := dvd p (quo m (pw p (val p m)))))

end Val

/-! ## A prime indicator -/

/-- `[q is prime] = sg(q − 1) · [lpf q = q]`. -/
abbrev isP (q : PTm n) : PTm n := sg (monus q one) * eqb (lpf q) q

theorem lpf_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] lpf a ≐ lpf b :=
  congrSucc (congrSucc (congrAp2 _ h h))

theorem prime_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) (ha : Γ ⊢[PRAAx] prime a) : Γ ⊢[PRAAx] prime b := by
  unfold prime at ha ⊢
  refine .andI (le_congr (.eqRefl _) h (Prf.andE₁ ha)) (.allI (.impI (.impI (.impI ?_))))
  have hs := shift_eq' h
  have hall := (Prf.andE₂ ha).allOpen
  refine .impE (.impE (.impE hall.wk.wk.wk Prf.hyp1.wk) (lt_congr (.eqRefl _) hs.wk.wk.wk.eqSymm Prf.hyp1)) ?_
  exact dvd_congr hs.wk.wk.wk.eqSymm Prf.hyp0

theorem two_le_lpf (z : PTm n) : Γ ⊢[PRAAx] le two (lpf z) :=
  le_of_eq_add (d := μz z) (by ipra_ring)

/-- A prime is its own least prime factor. -/
theorem lpf_of_prime {q : PTm n} (hp : Γ ⊢[PRAAx] prime q) : Γ ⊢[PRAAx] lpf q ≐ q := by
  have hq2 := prime_eq_succ_succ hp
  have hL := lpf_congr hq2
  have d := lpf_dvd (Γ := Γ) (monus q two)
  refine hL.eqTrans (.eqTrans ?_ hq2.eqSymm)
  refine .orE (lt_or_eq_of_le (Prf.andE₂ d)) ?_ Prf.hyp0
  have hp' := hp
  unfold prime at hp'
  have hall := Prf.allE (lpf (succ (succ (monus q two)))) (Prf.andE₂ hp')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hall
  refine .botE _ (.impE (.impE (.impE hall.wk (two_le_lpf _)) ?_) ?_)
  · exact lt_congr (.eqRefl _) hq2.wk.eqSymm Prf.hyp0
  · exact dvd_congr hq2.wk.eqSymm (Prf.andE₁ d).wk

theorem sg_monus_one_succ (y : PTm n) : Γ ⊢[PRAAx] sg (monus (succ (succ y)) one) ≐ one :=
  (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) ((succ_monus_succ _ _).eqTrans (monus_zero _)))).eqTrans
    (sg_succ _)

theorem isP_of_prime {q : PTm n} (hp : Γ ⊢[PRAAx] prime q) : Γ ⊢[PRAAx] isP q ≐ one := by
  have hq2 := prime_eq_succ_succ hp
  have s : Γ ⊢[PRAAx] sg (monus q one) ≐ one :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus hq2 (.eqRefl _)))).eqTrans (sg_monus_one_succ _)
  exact (congrMul s (eqb_of_eq (lpf_of_prime hp))).eqTrans (one_mul _)

private theorem isP_zero_part {Δ : List (Fm PTm n)} {q : PTm n} (h₁ : Δ ⊢[PRAAx] isP q ≐ one)
    (h₂ : Δ ⊢[PRAAx] monus q one ≐ zero) : Δ ⊢[PRAAx] prime q := by
  refine succ_ne_zero' _ (a := zero) (h₁.eqSymm.eqTrans ?_)
  refine (congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h₂)).eqTrans sg_zero) (.eqRefl _)).eqTrans ?_
  exact zero_mul _

theorem prime_of_isP {q : PTm n} (h : Γ ⊢[PRAAx] isP q ≐ one) : Γ ⊢[PRAAx] prime q := by
  refine .orE (zero_or_succ q) ?_ ?_
  · exact isP_zero_part h.wk ((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _))
  · refine .orE (zero_or_succ (pred q)) ?_ ?_
    · have e : ((pred q ≐ zero) :: (q ≐ succ (pred q)) :: Γ) ⊢[PRAAx] q ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact isP_zero_part h.wk.wk ((congrMonus e (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))
    · have e : ((pred q ≐ succ (pred (pred q))) :: (q ≐ succ (pred q)) :: Γ) ⊢[PRAAx]
          q ≐ succ (succ (pred (pred q))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have s := (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus e (.eqRefl one)))).eqTrans
        (sg_monus_one_succ (Γ := (pred q ≐ succ (pred (pred q))) :: (q ≐ succ (pred q)) :: Γ) (pred (pred q)))
      have hb : ((pred q ≐ succ (pred (pred q))) :: (q ≐ succ (pred q)) :: Γ) ⊢[PRAAx] eqb (lpf q) q ≐ one :=
        (one_mul _).eqSymm.eqTrans ((congrMul s.eqSymm (.eqRefl _)).eqTrans h.wk.wk)
      have hl := eq_of_eqb_ne (.impI (succ_ne_zero' _ (a := zero) (hb.wk.eqSymm.eqTrans Prf.hyp0)))
      exact prime_congr ((lpf_congr e).eqSymm.eqTrans hl) (lpf_prime _)

theorem isP_01 (q : PTm n) : Γ ⊢[PRAAx] (isP q ≐ zero) ⋎ (isP q ≐ one) := by
  refine .orE (zero_or_succ (monus q one)) ?_ ?_
  · refine .orI₁ ((congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero)
      (.eqRefl _)).eqTrans (zero_mul _))
  · have s : ((monus q one ≐ succ (pred (monus q one))) :: Γ) ⊢[PRAAx] sg (monus q one) ≐ one :=
      (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans (sg_succ _)
    refine .orE (eq_or_ne (lpf q) q) ?_ ?_
    · exact .orI₂ ((congrMul s.wk (eqb_of_eq Prf.hyp0)).eqTrans (one_mul _))
    · exact .orI₁ ((congrMul s.wk (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _))

end LeanProofs.IPRA.AnalyticNumberTheory.Valuation
