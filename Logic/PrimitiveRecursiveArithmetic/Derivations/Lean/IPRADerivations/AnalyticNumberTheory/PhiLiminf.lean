import IPRADerivations.AnalyticNumberTheory.EulerDomination

/-!
# Finite witnesses for `liminf φ(n)/n = 0`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:liminf-phi`:
for every `K` the primorial `n = ∏_{p ≤ B} p` with `B = 2^{2K}` satisfies `K φ(n) < n`.

As in the paper, `n/φ(n) = ∏_{p ≤ B} p/(p − 1) = E_B ≥ H_B ≥ 1 + K`:

* `cop_A`: a prime `p` is coprime to `A(M) = ∏_{q < M} q` for `M ≤ p`;
* `phi_A`: `φ(A(N)) = D(N) = ∏_{q < N} (q − 1)`, by induction on `N` from the multiplicativity of
  `φ` (`Multiplicative.phi_mul_at`) and `φ(p) = p − 1`;
* `liminf_at`: `(1 + K) · DenE_B ≤ ProdP_B` from `EulerDomination.euler_domination` and
  `Harmonic.harmonic_dyadic`, hence `K φ(ProdP_B) < ProdP_B`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiLiminf

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime fact_pos)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_eq_one_of_dvd)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (phi_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (A Dn pB pBt dBt A_succ Dn_succ A_pos pBt_zero pBt_one
  dBt_zero dBt_one ProdP DenE)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (euler_domination Dn_pos mul_one')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## A prime is coprime to the product of the smaller primes -/

theorem cop_prime_case {p M : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h : Γ ⊢[PRAAx] le (succ M) p)
    (hI : Γ ⊢[PRAAx] isP M ≐ one) : Γ ⊢[PRAAx] gcd p (pBt M) ≐ one := by
  have hq := prime_of_isP hI
  have hne : Γ ⊢[PRAAx] neg (M ≐ p) :=
    .impI (lt_irrefl p _ (le_congr (congrSucc Prf.hyp0) (.eqRefl _) h.wk))
  exact (congrGcd (.eqRefl _) (pBt_one hI)).eqTrans
    (gcd_comm_one (prime_eq_succ_pred hp) (gcd_distinct_primes hq hp hne))

theorem cop_pBt {p M : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h : Γ ⊢[PRAAx] le (succ M) p) :
    Γ ⊢[PRAAx] gcd p (pBt M) ≐ one :=
  .orE (isP_01 M)
    (gcd_eq_one_of_dvd (gcd_pos (prime_eq_succ_pred hp).wk) (.orI₂ (pBt_zero Prf.hyp0)))
    (cop_prime_case hp.wk h.wk Prf.hyp0)

theorem cop_step {p M : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (ih : Γ ⊢[PRAAx] le M p ⟶ (gcd p (A M) ≐ one)) (h : Γ ⊢[PRAAx] le (succ M) p) :
    Γ ⊢[PRAAx] gcd p (A (succ M)) ≐ one :=
  (congrGcd (.eqRefl _) (A_succ M)).eqTrans
    (coprime_mul (prime_eq_succ_pred hp) (Prf.impE ih (le_trans (le_succ_self M) h)) (cop_pBt hp h))

/-- A prime `p` is coprime to `A(M)` for `M ≤ p`. -/
theorem cop_A {p M : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h : Γ ⊢[PRAAx] le M p) : Γ ⊢[PRAAx] gcd p (A M) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift p) ⟶ (gcd (Syn.shift p) (A (var 0)) ≐ one)) := by
    ipra_qfind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2, subst_ex2]
    · exact .impI (gcd_eq_one_of_dvd (gcd_pos (prime_eq_succ_pred hp).wk) (.orI₂ (prod_zero pB zero)))
    · exact .impI (cop_step (prime_shift hp).wk.wk Prf.hyp1 Prf.hyp0)
  have h2 := Prf.allE M hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_ex2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 h

/-! ## `φ` of the primorial -/

alias congrPhi := PhiTwo.phi_congr'

theorem phiA_step0 {N : PTm n} (ih : Γ ⊢[PRAAx] phi (A N) ≐ Dn N) (h0 : Γ ⊢[PRAAx] isP N ≐ zero) :
    Γ ⊢[PRAAx] phi (A (succ N)) ≐ Dn (succ N) :=
  (congrPhi ((A_succ N).eqTrans ((congrMul (.eqRefl _) (pBt_zero h0)).eqTrans (mul_one' _)))).eqTrans
    (ih.eqTrans ((Dn_succ N).eqTrans ((congrMul (.eqRefl _) (dBt_zero h0)).eqTrans (mul_one' _))).eqSymm)

theorem phiA_step1 {N : PTm n} (ih : Γ ⊢[PRAAx] phi (A N) ≐ Dn N) (h1 : Γ ⊢[PRAAx] isP N ≐ one) :
    Γ ⊢[PRAAx] phi (A (succ N)) ≐ Dn (succ N) := by
  have hp := prime_of_isP h1
  have ppos := prime_eq_succ_pred hp
  have g := gcd_comm_one (A_pos N) (cop_A hp (le_refl N))
  have e₁ : Γ ⊢[PRAAx] phi (A (succ N)) ≐ phi (A N) * phi N :=
    (congrPhi ((A_succ N).eqTrans (congrMul (.eqRefl _) (pBt_one h1)))).eqTrans (phi_mul_at (A_pos N) ppos g)
  have e₂ : Γ ⊢[PRAAx] phi N ≐ pred N :=
    (phi_prime hp).eqTrans ((congrMonus ppos (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))
  exact e₁.eqTrans ((congrMul ih e₂).eqTrans
    ((Dn_succ N).eqTrans (congrMul (.eqRefl _) (dBt_one h1))).eqSymm)

theorem phiA_step {N : PTm n} (ih : Γ ⊢[PRAAx] phi (A N) ≐ Dn N) : Γ ⊢[PRAAx] phi (A (succ N)) ≐ Dn (succ N) :=
  .orE (isP_01 N) (phiA_step0 ih.wk Prf.hyp0) (phiA_step1 ih.wk Prf.hyp0)

private abbrev phiAF : Fm PTm 1 := phi (A (var 0)) ≐ Dn (var 0)

private theorem phiA₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] phiAF := by
  ipra_ind [subst_ap2]
  · have eA : ([] : List (Fm PTm 0)) ⊢[PRAAx] A (zero : PTm 0) ≐ one := prod_zero _ _
    exact (congrPhi eA).eqTrans ((AnalyticNumberTheory.EulerProduct.phi_one).eqTrans (prod_zero _ _).eqSymm)
  · exact phiA_step Prf.hyp0

/-- `φ(A(N)) = D(N)`. -/
theorem phi_A (N : PTm n) : Γ ⊢[PRAAx] phi (A N) ≐ Dn N := by
  have h := inst (Γ := Γ) phiA₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## The witnesses -/

/-- `thm:liminf-phi`: `K φ(n) < n` for `n = ProdP_B`, `B = 2^{2K}`. -/
theorem liminf_at (K : PTm n) :
    Γ ⊢[PRAAx] lt (K * phi (ProdP (pw two (two * K)))) (ProdP (pw two (two * K))) := by
  have ed := euler_domination (Γ := Γ) (pw two (two * K)) (fact (pw two (two * K)))
  have hd := Harmonic.harmonic_dyadic (Γ := Γ) K
  have hF := fact_pos (Γ := Γ) (pw two (two * K))
  have hD := Dn_pos (Γ := Γ) (succ (pw two (two * K)))
  have c : Γ ⊢[PRAAx] le (fact (pw two (two * K)) * ((one + K) * DenE (pw two (two * K))))
      (fact (pw two (two * K)) * ProdP (pw two (two * K))) := by
    refine le_congr ?_ (.eqRefl _) (le_trans (le_mul_mono hd (le_refl (DenE (pw two (two * K))))) ed)
    ipra_ring
  have c' := mul_le_cancel_at hF c
  refine le_trans (le_of_eq_add (d := pred (DenE (pw two (two * K)))) ?_) c'
  ipra_lc -Groth.ι (IPRA.Q.mk Γ K) * natEq (phi_A (succ (pw two (two * K)))) + natEq hD

/-- `thm:liminf-phi`, variable `0 = K`. -/
abbrev liminfFormula : Fm PTm 1 :=
  lt (var 0 * phi (ProdP (pw two (two * var 0)))) (ProdP (pw two (two * var 0)))

theorem liminf_phi : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 liminfFormula :=
  closeUniv 1 (liminf_at _)

end LeanProofs.IPRA.AnalyticNumberTheory.PhiLiminf
