import IPRADerivations.AnalyticNumberTheory.SigmaMult
import IPRADerivations.AnalyticNumberTheory.PlusPower

/-!
# `σ` at a prime power (`robin_ipra_research_2026-11-19`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `report.tex`, proof of `thm:three`: "Finite geometric
summation gives `A(n) = Π (1 − p_i^{−a_i−1})/(1 − p_i^{−1})`", and `lcm_bridge.tex` ("the finite geometric-series
formula").

For a prime `p` and `a ≥ 0`:

* `sigma_step`: `σ(p · p^a) = p σ(p^a) + 1`. The divisor sum of `P = p · p^a` splits into the multiples of `p`
  (`SumReindex.reindex_eq`, `d = pk`, with `[pk ∣ pQ] = [k ∣ Q]`, `dvd_scale`) and the rest, whose only divisor of `P`
  is `1` (a divisor coprime to `p` is coprime to `p^{a+1}`, `PlusPower.cop_pow`);
* `sigma_pow`: `(p − 1) σ(p^a) + 1 = p^{a+1}`, the finite geometric series.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult (sB sig inst2_sB inst2_v0)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit (mul_cancel pos_of_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor (inst2_v1)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' gcd_comm_one eq_one_of_coprime_dvd
  one_le_of_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul eq_of_rem_zero)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sig_congr {K K' : PTm n} (h : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] sig K ≐ sig K' :=
  congrAp2 _ (congrSucc h) h

theorem pos_pw {p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (a : PTm n) :
    Γ ⊢[PRAAx] pw p a ≐ succ (pred (pw p a)) :=
  Common.pos_pw hp a

/-- `σ(1) = 1`. -/
theorem sig_one : Γ ⊢[PRAAx] sig one ≐ one := by
  refine (sum_succ _ _ _).eqTrans ?_
  refine (congrAdd ((sum_succ _ _ _).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _)))
    (.eqRefl _)).eqTrans ?_
  have e0 : Γ ⊢[PRAAx] Syn.subst ![zero, one] sB ≐ zero := by
    show Γ ⊢[PRAAx] inst2 sB zero one ≐ zero
    rw [inst2_sB]; exact mul_zero _
  have e1 : Γ ⊢[PRAAx] Syn.subst ![one, one] sB ≐ one := by
    show Γ ⊢[PRAAx] inst2 sB one one ≐ one
    rw [inst2_sB]
    exact (congrMul (eqb_of_eq (rem_one _)) (.eqRefl _)).eqTrans (one_mul _)
  exact (congrAdd e0 e1).eqTrans (zero_add _)

/-! ## The bodies -/

/-- `[pk ∣ pQ] pk` over `0 = k`, `1 = ⟨p, Q⟩`. -/
def hB : PTm 2 := eqb (rem (fstT (var 1) * sndT (var 1)) (fstT (var 1) * var 0)) zero * (fstT (var 1) * var 0)
/-- `(1 − [p ∣ d]) [d ∣ P] d` over `0 = d`, `1 = ⟨p, P⟩`. -/
def nB : PTm 2 := monus one (eqb (rem (var 0) (fstT (var 1))) zero) * (eqb (rem (sndT (var 1)) (var 0)) zero * var 0)

theorem hB_at (k p Q : PTm n) :
    Γ ⊢[PRAAx] inst2 hB k (pairT p Q) ≐ eqb (rem (p * Q) (p * k)) zero * (p * k) := by
  have e : inst2 hB k (pairT p Q) = eqb (rem (fstT (pairT p Q) * sndT (pairT p Q)) (fstT (pairT p Q) * k)) zero *
      (fstT (pairT p Q) * k) := by simp [inst2, hB]
  rw [e]
  exact congrMul (congrEqb' (congrAp2 remF (congrMul (fst_pair _ _) (snd_pair _ _)) (congrMul (fst_pair _ _) (.eqRefl _)))
    (.eqRefl _)) (congrMul (fst_pair _ _) (.eqRefl _))

theorem nB_at (d p P : PTm n) :
    Γ ⊢[PRAAx] inst2 nB d (pairT p P) ≐ monus one (eqb (rem d p) zero) * (eqb (rem P d) zero * d) := by
  have e : inst2 nB d (pairT p P) = monus one (eqb (rem d (fstT (pairT p P))) zero) *
      (eqb (rem (sndT (pairT p P)) d) zero * d) := by simp [inst2, nB]
  rw [e]
  exact congrMul (congrMonus (.eqRefl _) (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)))
    (congrMul (congrEqb' (congrAp2 remF (snd_pair _ _) (.eqRefl _)) (.eqRefl _)) (.eqRefl _))

/-! ## Pointwise facts -/

/-- `[pk ∣ pQ] = [k ∣ Q]` for `p, Q ≥ 1`. -/
theorem dvd_scale {p Q : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q)) (k : PTm n) :
    Γ ⊢[PRAAx] eqb (rem (p * Q) (p * k)) zero ≐ eqb (rem Q k) zero := by
  refine .orE (eqb_cases (Γ := Γ) (rem Q k) zero) ?_ ?_
  · -- `k ∤ Q`: then `pk ∤ pQ`
    refine Prf.eqTrans ?_ Prf.hyp0.eqSymm
    refine eqb_of_ne (.impI ?_)
    let C : List (Fm PTm n) := (rem (p * Q) (p * k) ≐ zero) :: (eqb (rem Q k) zero ≐ zero) :: Γ
    have hd : C ⊢[PRAAx] dvd (p * k) (p * Q) := Prf.hyp0
    have hpQ : C ⊢[PRAAx] p * Q ≐ succ (pred (p * Q)) := pos_mul hp.wk.wk hQ.wk.wk
    have hpk := pos_of_dvd hpQ hd
    have e := eq_of_dvd' hpk hd
    have c : C ⊢[PRAAx] p * Q ≐ p * (k * quo (p * Q) (p * k)) :=
      e.eqTrans (by ipra_ring)
    have hk : C ⊢[PRAAx] k ≐ succ (pred k) := by
      refine .orE (zero_or_succ k) ?_ Prf.hyp0
      have z : ((k ≐ zero) :: C) ⊢[PRAAx] p * k ≐ zero := (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)
      exact succ_ne_zero' _ (hpk.wk.eqSymm.eqTrans z)
    have dq : C ⊢[PRAAx] dvd k Q := dvd_of_eq' hk (mul_cancel hp.wk.wk c)
    exact succ_ne_zero' _ ((eqb_of_eq dq).eqSymm.eqTrans Prf.hyp1)
  · -- `k ∣ Q`: then `pk ∣ pQ`
    refine Prf.eqTrans ?_ Prf.hyp0.eqSymm
    have hk : ((eqb (rem Q k) zero ≐ one) :: Γ) ⊢[PRAAx] dvd k Q := eq_of_eqb Prf.hyp0
    have pk := pos_of_dvd hQ.wk hk
    have e := eq_of_dvd' pk hk
    refine eqb_of_eq (dvd_of_eq' (pos_mul hp.wk pk) (w := quo Q k) ?_)
    exact (congrMul (.eqRefl _) e).eqTrans (by ipra_ring)

/-- The split of one divisor term: `[d ∣ pQ] d = [p ∣ d] h(d/p) + (1 − [p ∣ d]) [d ∣ pQ] d`. -/
theorem split_pt {p Q : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (d : PTm n) :
    Γ ⊢[PRAAx] eqb (rem (p * Q) d) zero * d ≐
      eqb (rem d p) zero * inst2 hB (quo d p) (pairT p Q) + monus one (eqb (rem d p) zero) * (eqb (rem (p * Q) d) zero * d) := by
  refine .orE (eqb_cases (Γ := Γ) (rem d p) zero) ?_ ?_
  · have m1 : ((eqb (rem d p) zero ≐ zero) :: Γ) ⊢[PRAAx] monus one (eqb (rem d p) zero) ≐ one :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    refine withEq Prf.hyp0 fun e => withEq m1 fun e' => ?_
    apply deriveNat; ipra_simps; rw [e, e']; ring
  · let C : List (Fm PTm n) := (eqb (rem d p) zero ≐ one) :: Γ
    have m0 : C ⊢[PRAAx] monus one (eqb (rem d p) zero) ≐ zero :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _)
    have ed : C ⊢[PRAAx] d ≐ p * quo d p := eq_of_rem_zero hp.wk (eq_of_eqb Prf.hyp0)
    have h1 : C ⊢[PRAAx] inst2 hB (quo d p) (pairT p Q) ≐ eqb (rem (p * Q) d) zero * d :=
      (hB_at _ _ _).eqTrans (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) ed.eqSymm) (.eqRefl _)) ed.eqSymm)
    refine withEq Prf.hyp0 fun e1 => withEq h1 fun e2 => withEq m0 fun e3 => ?_
    apply deriveNat; ipra_simps; rw [e1, e2, e3]; ring

/-- The non-multiples of `p` dividing `p · p^a`: only `d = 1`. -/
theorem rest_pt {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a d : PTm n) :
    Γ ⊢[PRAAx] monus one (eqb (rem d p) zero) * (eqb (rem (p * pw p a) d) zero * d) ≐ eqb one d * one := by
  have hp1 := prime_eq_succ_pred hp
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  have hP := pos_mul hp1 (pos_pw hp1 a)
  refine .orE (eqb_cases (Γ := Γ) (rem d p) zero) ?_ ?_
  · -- `p ∤ d`
    let C : List (Fm PTm n) := (eqb (rem d p) zero ≐ zero) :: Γ
    have m1 : C ⊢[PRAAx] monus one (eqb (rem d p) zero) ≐ one :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    refine .orE (eqb_cases (Γ := C) (rem (p * pw p a) d) zero) ?_ ?_
    · -- `d ∤ P`, so `d ≠ 1`
      let C' : List (Fm PTm n) := (eqb (rem (p * pw p a) d) zero ≐ zero) :: C
      have l : C' ⊢[PRAAx] monus one (eqb (rem d p) zero) * (eqb (rem (p * pw p a) d) zero * d) ≐ zero :=
        (congrMul m1.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
      have r : C' ⊢[PRAAx] eqb one d ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        have e : ((one ≐ d) :: C') ⊢[PRAAx] eqb (rem (p * pw p a) d) zero ≐ one :=
          (congrEqb' (congrAp2 remF (.eqRefl _) Prf.hyp0.eqSymm) (.eqRefl _)).eqTrans (eqb_of_eq (rem_one _))
        exact succ_ne_zero' _ (e.eqSymm.eqTrans Prf.hyp1)
      exact l.eqTrans ((congrMul r (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
    · -- `d ∣ P` and `p ∤ d`: `d = 1`
      let C' : List (Fm PTm n) := (eqb (rem (p * pw p a) d) zero ≐ one) :: C
      have hd : C' ⊢[PRAAx] dvd d (p * pw p a) := eq_of_eqb Prf.hyp0
      have pd := pos_of_dvd hP.wk.wk hd
      have nd : C' ⊢[PRAAx] neg (dvd p d) := by
        refine .impI ?_
        exact succ_ne_zero' _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans Prf.hyp1.wk)
      have g1 : C' ⊢[PRAAx] gcd p d ≐ one := gcd_prime hp.wk.wk nd
      have g2 : C' ⊢[PRAAx] gcd d p ≐ one := gcd_comm_one pd g1
      have g3 : C' ⊢[PRAAx] gcd d (pw p (succ a)) ≐ one := cop_pow pd g2 (succ a)
      have g4 : C' ⊢[PRAAx] gcd d (p * pw p a) ≐ one :=
        (LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep.congrGcd (.eqRefl _)
          ((mul_comm _ _).eqTrans (pw_succ p a).eqSymm)).eqTrans g3
      have d1 : C' ⊢[PRAAx] d ≐ one := eq_one_of_coprime_dvd pd g4 hd
      have l : C' ⊢[PRAAx] monus one (eqb (rem d p) zero) * (eqb (rem (p * pw p a) d) zero * d) ≐ one :=
        (congrMul m1.wk (congrMul Prf.hyp0 d1)).eqTrans (by ipra_ring)
      have r : C' ⊢[PRAAx] eqb one d * one ≐ one :=
        (congrMul (eqb_of_eq d1.eqSymm) (.eqRefl _)).eqTrans (by ipra_ring)
      exact l.eqTrans r.eqSymm
  · -- `p ∣ d`: the term vanishes and `d ≠ 1`
    let C : List (Fm PTm n) := (eqb (rem d p) zero ≐ one) :: Γ
    have l : C ⊢[PRAAx] monus one (eqb (rem d p) zero) * (eqb (rem (p * pw p a) d) zero * d) ≐ zero :=
      (congrMul ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _)) (.eqRefl _)).eqTrans (zero_mul _)
    have r : C ⊢[PRAAx] eqb one d ≐ zero := by
      refine eqb_of_ne (.impI ?_)
      have rs : ((one ≐ d) :: C) ⊢[PRAAx] rem one p ≐ one :=
        LeanProofs.IPRA.AnalyticNumberTheory.Euler.rem_small hp2.wk.wk (hp2.wk.wk : ((one ≐ d) :: C) ⊢[PRAAx] lt one p)
      have z : ((one ≐ d) :: C) ⊢[PRAAx] (one : PTm n) ≐ zero :=
        rs.eqSymm.eqTrans ((congrAp2 remF Prf.hyp0 (.eqRefl _)).eqTrans (eq_of_eqb Prf.hyp1))
      exact succ_ne_zero' _ z
    exact l.eqTrans ((congrMul r (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

/-! ## The recursion `σ(p^{a+1}) = p σ(p^a) + 1` -/

theorem sh_pw (p a : PTm n) : Syn.shift (pw p a) = pw (Syn.shift p) (Syn.shift a) := by simp [Syn.shift]
theorem sh_P (p a : PTm n) : Syn.shift (p * pw p a) = Syn.shift p * pw (Syn.shift p) (Syn.shift a) := by
  simp [Syn.shift]

theorem sigma_step {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a : PTm n) :
    Γ ⊢[PRAAx] sig (p * pw p a) ≐ p * sig (pw p a) + one := by
  have hp1 := prime_eq_succ_pred hp
  have hQ := pos_pw hp1 a
  have hP := pos_mul hp1 hQ
  have hp1' := Common.pos_shift hp1
  have hQ' : Γ.map Fm.shift ⊢[PRAAx] pw (Syn.shift p) (Syn.shift a) ≐ succ (pred (pw (Syn.shift p) (Syn.shift a))) :=
    pos_pw hp1' _
  have hpr' := prime_shift hp
  -- split every term
  have sp := sum_add2 (Γ := Γ) (riB hB) nB sB (K := succ (p * pw p a)) (x := pairT p (pairT p (pw p a)))
    (x' := pairT p (p * pw p a)) (z := p * pw p a) (.allI (.impI (by
      simp only [inst2_sB, inst2_riB, shift_pairT, sh_P, sh_pw]
      refine (split_pt hp1'.wk (var 0)).eqTrans (congrAdd ?_ (nB_at _ _ _).eqSymm)
      exact (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
        (congrInst2 hB (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))).eqSymm)))
  -- the multiples of `p`
  have cm : Γ ⊢[PRAAx] cM (succ (p * pw p a)) p ≐ succ (pw p a) :=
    (multiples_upto hp1).eqTrans (congrSucc (quo_mul hp1 (.eqRefl _)))
  have p1 : Γ ⊢[PRAAx] ap2 (sumF (riB hB)) (succ (p * pw p a)) (pairT p (pairT p (pw p a))) ≐ p * sig (pw p a) := by
    refine (reindex_eq hB (succ (p * pw p a)) hp1).eqTrans ((congrAp2 _ cm (.eqRefl _)).eqTrans ?_)
    refine Prf.eqTrans ?_ (sum_const_mul sB (succ (pw p a)) p (pw p a))
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_cmB, inst2_sB, shift_pairT, sh_pw]
    refine (hB_at _ _ _).eqTrans ?_
    refine (congrMul (dvd_scale hp1'.wk hQ'.wk (var 0)) (.eqRefl _)).eqTrans ?_
    refine Prf.eqTrans ?_ (congrMul (fst_pair _ _).eqSymm
      (congrMul (congrEqb' (congrAp2 remF (snd_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)) (.eqRefl _)))
    ipra_ring
  -- the rest: only `d = 1`
  have p2 : Γ ⊢[PRAAx] ap2 (sumF nB) (succ (p * pw p a)) (pairT p (p * pw p a)) ≐ one := by
    have h1 : Γ ⊢[PRAAx] lt one (succ (p * pw p a)) := by
      have l := one_le_of_pos hP
      ipra_le sl l
    refine Prf.eqTrans ?_ ((sum_delta (var 1) (x := one) h1).eqTrans (by rw [inst2_v1]; exact .eqRefl _))
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_dB, inst2_v1, shift_pairT, sh_P]
    refine (nB_at _ _ _).eqTrans ((rest_pt hpr'.wk _ _).eqTrans ?_)
    have e : Syn.shift (one : PTm n) = one := by simp [Syn.shift]
    rw [e]
    exact congrMul (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)) (snd_pair _ _).eqSymm
  exact sp.eqTrans (congrAdd p1 p2)

/-- `(p − 1) σ(p^a) + 1 = p^{a+1}`: the finite geometric series. -/
theorem sigma_pow {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a : PTm n) :
    Γ ⊢[PRAAx] pred p * sig (pw p a) + one ≐ pw p (succ a) := by
  have hall : Γ ⊢[PRAAx] Fm.all (pred (Syn.shift p) * sig (pw (Syn.shift p) (var 0)) + one ≐
      pw (Syn.shift p) (succ (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, LeanProofs.IPRA.PTm.subst_pred,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have hp1 := prime_eq_succ_pred hp
      have s1 : Γ ⊢[PRAAx] sig (pw p zero) ≐ one := (sig_congr (pw_zero p)).eqTrans sig_one
      have e1 := natEq s1
      have e2 := natEq hp1
      have e3 := natEq ((pw_succ (Γ := Γ) p zero).eqTrans ((congrMul (pw_zero p) (.eqRefl _)).eqTrans (one_mul _)))
      refine withEq s1 fun _ => ?_
      apply deriveNat; ipra_simps; rw [e1, e3]; linear_combination -e2
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, LeanProofs.IPRA.PTm.subst_pred,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := (pred (Syn.shift p) * sig (pw (Syn.shift p) (var 0)) + one ≐
        pw (Syn.shift p) (succ (var 0))) :: Γ.map Fm.shift
      have hpr : Δ ⊢[PRAAx] prime (Syn.shift p) := (prime_shift hp).wk
      have hp1 := prime_eq_succ_pred hpr
      have st := sigma_step hpr (var 0)
      have s1 : Δ ⊢[PRAAx] sig (pw (Syn.shift p) (succ (var 0))) ≐
          Syn.shift p * sig (pw (Syn.shift p) (var 0)) + one :=
        (sig_congr ((pw_succ _ _).eqTrans (mul_comm _ _))).eqTrans st
      have e1 := natEq s1
      have e2 := natEq (Prf.hyp0 : Δ ⊢[PRAAx] pred (Syn.shift p) * sig (pw (Syn.shift p) (var 0)) + one ≐
        pw (Syn.shift p) (succ (var 0)))
      have e3 := natEq hp1
      have e4 := natEq (pw_succ (Γ := Δ) (Syn.shift p) (succ (var 0)))
      apply deriveNat; ipra_simps
      rw [e1, e4]
      linear_combination 𝔞 (Syn.shift p) * e2 - e3
  have r := Prf.allE a hall
  simpa [Syn.subst_inst_shift] using r

end LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower

export_ipra AnalyticNumberTheory.SigmaPrimePower (pos_pw sig_congr sigma_pow)
