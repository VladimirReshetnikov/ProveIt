import IPRADerivations.AnalyticNumberTheory.PhiEvenPow

/-!
# The Euler product for `φ`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-product`
(second part), in its denominator-cleared form:
`φ(n) · ∏_{p ∣ n} p = n · ∏_{p ∣ n} (p − 1)`.

With `e(q, n) = [q prime][q ∣ n]` and `∏_F(n) = ∏_{q ≤ n} F(q)^{e(q, n)}`:

* `peelE`: for a prime `p`, `n = p^a m`, `a ≥ 1`, `p ∤ m`: `e(q, n) = e(q, m) + [q = p]`;
* `pp_peel`: `∏_F(p^a m) = ∏_F(m) · F(p)` (a delta product, `MultiSums.prod2_delta`);
* the theorem by strong induction on `n`, peeling `p = lpf(n)` with `Valuation`:
  `φ(p^a) · p = p^a (p − 1)` and `φ(p^a m) = φ(p^a) φ(m)`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot coprime_pow totient_prime_power_at)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (eqb_iff shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_eq' shift_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation
open LeanProofs.IPRA.AnalyticNumberTheory.PhiEvenPow (isP_congr p_dvd_n shift_pw' shift_rpos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The prime-divisor indicator -/

/-- `e(q, n) = [q prime][q ∣ n]`, over `0 = q`, `1 = n`. -/
abbrev eB : PTm 2 := isP (var 0) * eqb (rem (var 1) (var 0)) zero

theorem inst2_e (q N : PTm n) : inst2 eB q N = isP q * eqb (rem N q) zero := by simp [inst2]

theorem eqb_comm' (a b : PTm n) : Γ ⊢[PRAAx] eqb a b ≐ eqb b a := by
  unfold eqb; exact congrMonus (.eqRefl _) (add_comm _ _)

section Peel

variable {p a m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
  (hrm : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p)))
include hp ha hrm

theorem peelE (q : PTm n) : Γ ⊢[PRAAx] inst2 eB q (pw p a * m) ≐ inst2 eB q m + eqb q p := by
  rw [inst2_e, inst2_e]
  refine .orE (isP_01 q) ?_ ?_
  · have hI : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    have hE : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] eqb q p ≐ zero := by
      refine eqb_of_ne (.impI (succ_ne_zero' _ (a := zero) ?_))
      exact (isP_of_prime hp.wk.wk).eqSymm.eqTrans ((isP_congr Prf.hyp0).eqSymm.eqTrans hI.wk)
    refine (congrMul hI (.eqRefl _)).eqTrans ((zero_mul _).eqTrans ?_)
    refine .eqTrans ?_ (congrAdd ((congrMul hI (.eqRefl _)).eqTrans (zero_mul _)) hE).eqSymm
    exact (add_zero _).eqSymm
  · have hI : ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    refine .orE (eq_or_ne q p) ?_ ?_
    · have hqp : ((q ≐ p) :: (isP q ≐ one) :: Γ) ⊢[PRAAx] q ≐ p := Prf.hyp0
      have hDn := eqb_of_eq ((congrAp2 remF (.eqRefl _) hqp).eqTrans (p_dvd_n (m := m) hp.wk.wk ha.wk.wk))
      have hDm : ((q ≐ p) :: (isP q ≐ one) :: Γ) ⊢[PRAAx] eqb (rem m q) zero ≐ zero :=
        eqb_of_ne (.impI (succ_ne_zero' _ (hrm.wk.wk.wk.eqSymm.eqTrans
          ((congrAp2 remF (.eqRefl _) hqp.wk).eqSymm.eqTrans Prf.hyp0))))
      refine (congrMul hI.wk hDn).eqTrans ((one_mul _).eqTrans ?_)
      refine .eqTrans ?_ (congrAdd ((congrMul hI.wk hDm).eqTrans (mul_zero _)) (eqb_of_eq hqp)).eqSymm
      exact (zero_add _).eqSymm
    · have hq := (prime_of_isP hI).wk (ψ := neg (q ≐ p))
      have hq1 := prime_eq_succ_pred hq
      have gq := coprime_pow hq1 (gcd_distinct_primes hq hp.wk.wk Prf.hyp0) a
      have hD : ((neg (q ≐ p)) :: (isP q ≐ one) :: Γ) ⊢[PRAAx] eqb (rem (pw p a * m) q) zero ≐ eqb (rem m q) zero := by
        refine eqb_iff (.impI (gauss hq1.wk gq.wk Prf.hyp0)) (.impI ?_)
        exact dvd_congr (mul_comm _ _) (dvd_mul' hq1.wk (pw p a) Prf.hyp0)
      exact (congrMul (.eqRefl _) hD).eqTrans ((add_zero _).eqSymm.eqTrans
        (congrAdd (.eqRefl _) (eqb_of_ne Prf.hyp0).eqSymm))

end Peel

/-! ## Prime-indexed products -/

alias mul_one' := Common.mul_one_right

/-- `F(q)^{e(q, n)}`, over `0 = q`, `1 = n`. -/
abbrev pB (F : PTm 2) : PTm 2 := pw F eB

/-- `∏_{q ≤ n} F(q)^{e(q, n)}`. -/
abbrev PP (F : PTm 2) (N : PTm n) : PTm n := ap2 (prodF (pB F)) (succ N) N

theorem inst2_pB (F : PTm 2) (q N : PTm n) : inst2 (pB F) q N = pw (inst2 F q N) (inst2 eB q N) := by
  simp [inst2]

theorem e_far {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] inst2 eB (succ m + k) m ≐ zero := by
  rw [inst2_e]
  have hQ : Γ ⊢[PRAAx] succ m + k ≐ succ (pred (succ m + k)) :=
    eq_succ_pred (y := m + k) (by ipra_ring)
  have hr := rem_eq' hQ (z := m) (q := zero) (r := m) (by ipra_ring)
    (le_of_eq_add (d := k) (by apply deriveNat; ipra_simps))
  have he : Γ ⊢[PRAAx] eqb (rem m (succ m + k)) zero ≐ zero :=
    (congrEqb hr (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (hm.wk.eqSymm.eqTrans Prf.hyp0))))
  exact (congrMul (.eqRefl _) he).eqTrans (mul_zero _)

theorem prod_extend (F : PTm 2) {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (pB F)) (succ m + k) m ≐ ap2 (prodF (pB F)) (succ m) m := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (prodF (pB F)) (succ (Syn.shift m) + var 0) (Syn.shift m) ≐
      ap2 (prodF (pB F)) (succ (Syn.shift m)) (Syn.shift m)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ]
      exact congrAp2 (prodF (pB F)) (add_zero _) (.eqRefl _)
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, Syn.subst_shift, Syn.repl_succ,
        ConciseIPRA.PTm.subst_succ]
      refine (congrAp2 (prodF (pB F)) (add_succ _ _) (.eqRefl _)).eqTrans ((prod_succ _ _ _).eqTrans ?_)
      have t : ((ap2 (prodF (pB F)) (succ (Syn.shift m) + var 0) (Syn.shift m) ≐
          ap2 (prodF (pB F)) (succ (Syn.shift m)) (Syn.shift m)) :: Γ.map Fm.shift) ⊢[PRAAx]
          inst2 (pB F) (succ (Syn.shift m) + var 0) (Syn.shift m) ≐ one := by
        rw [inst2_pB]
        exact (congrAp2 powF (e_far (shift_pos hm).wk _) (.eqRefl _)).eqTrans (pw_zero _)
      exact (congrMul Prf.hyp0 t).eqTrans (mul_one' _)
  have h := Prf.allE k hall
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

theorem inst3_sub2 (G : PTm 2) (j c x : PTm n) : inst3 (Syn.subst ![var 0, var 2] G) j c x = inst2 G j x := by
  simp only [inst3, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

theorem inst3_mul' (A B : PTm 3) (j c x : PTm n) : inst3 (A * B) j c x = inst3 A j c x * inst3 B j c x := by
  simp only [inst3, PTm.subst_mul]

section PP

variable {p a m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
  (hrm : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p))) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
include hp ha hrm hm

/-- `∏_F(p^a m) = ∏_F(m) · F(p)` for a base `F` not depending on the parameter. -/
theorem pp_peel (F : PTm 2) (hF : ∀ {k : ℕ} (q x y : PTm k), inst2 F q x = inst2 F q y) :
    Γ ⊢[PRAAx] PP F (pw p a * m) ≐ PP F m * inst2 F p m := by
  have hP := pw_pos' (prime_eq_succ_pred hp) a
  have hn := pos_mul hP hm
  have s₁ := (Permutation.prod2_eq_prod (Γ := Γ) (pB F) (succ (pw p a * m)) p (pw p a * m)).eqSymm
  have s₂ : Γ ⊢[PRAAx] ap3 (prod2F (Syn.subst ![var 0, var 2] (pB F))) (succ (pw p a * m)) p (pw p a * m) ≐
      ap3 (prod2F (Syn.subst ![var 0, var 2] (pB F) * deltaBody F)) (succ (pw p a * m)) p m := by
    refine prod2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst3_mul', inst3_sub2, inst3_sub2, inst3_delta, inst2_pB, inst2_pB,
      hF _ (Syn.shift (pw p a * m)) (Syn.shift m), shift_mul', shift_pw']
    exact (congrAp2 powF ((peelE (prime_shift hp).wk (shift_pos ha).wk (shift_rpos hrm).wk (var 0)).eqTrans
      (congrAdd (.eqRefl _) (eqb_comm' _ _))) (.eqRefl _)).eqTrans (pw_add _ _ _)
  have s₃ := prod2_mul (Γ := Γ) (Syn.subst ![var 0, var 2] (pB F)) (deltaBody F) (succ (pw p a * m)) p m
  have e : Γ ⊢[PRAAx] succ (pw p a * m) ≐ succ m + pred (pw p a) * m := by
    ipra_lc Groth.ι (Q.mk _ m) * natEq hP
  have s₄ := (Permutation.prod2_eq_prod (Γ := Γ) (pB F) (succ (pw p a * m)) p m).eqTrans
    ((congrAp2 (prodF (pB F)) e (.eqRefl m)).eqTrans (prod_extend F hm _))
  have hlt : Γ ⊢[PRAAx] lt p (succ (pw p a * m)) :=
    (succ_monus_succ _ _).eqTrans (dvd_le' (prime_eq_succ_pred hp) (p_dvd_n (m := m) hp ha) hn)
  have s₅ := prod2_delta F (x := m) hlt
  exact s₁.eqTrans (s₂.eqTrans (s₃.eqTrans (congrMul s₄ s₅)))

end PP

/-- The bases `q` and `q − 1`. -/
abbrev F₁ : PTm 2 := var 0
abbrev F₂ : PTm 2 := monus (var 0) one

theorem hF₁ {k : ℕ} (q x y : PTm k) : inst2 F₁ q x = inst2 F₁ q y := by simp [inst2]
theorem hF₂ {k : ℕ} (q x y : PTm k) : inst2 F₂ q x = inst2 F₂ q y := by simp [inst2]
theorem inst2_F₁ (q x : PTm n) : inst2 F₁ q x = q := by simp [inst2]
theorem inst2_F₂ (q x : PTm n) : inst2 F₂ q x = monus q one := by simp [inst2]

/-! ## Small cases -/

theorem isP_zero : Γ ⊢[PRAAx] isP (zero : PTm n) ≐ zero :=
  (congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (zero_monus _))).eqTrans sg_zero) (.eqRefl _)).eqTrans
    (zero_mul _)

theorem isP_one : Γ ⊢[PRAAx] isP (one : PTm n) ≐ zero :=
  (congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _)
    ((succ_monus_succ _ _).eqTrans (monus_zero _)))).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)

theorem pp_one (F : PTm 2) : Γ ⊢[PRAAx] PP F (one : PTm n) ≐ one := by
  refine (prod_succ _ _ _).eqTrans ?_
  refine (congrMul ((prod_succ _ _ _).eqTrans (congrMul (prod_zero _ _) (.eqRefl _))) (.eqRefl _)).eqTrans ?_
  have t₀ : Γ ⊢[PRAAx] inst2 (pB F) zero one ≐ one := by
    rw [inst2_pB, inst2_e]
    exact (congrAp2 powF ((congrMul isP_zero (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (pw_zero _)
  have t₁ : Γ ⊢[PRAAx] inst2 (pB F) one one ≐ one := by
    rw [inst2_pB, inst2_e]
    exact (congrAp2 powF ((congrMul isP_one (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (pw_zero _)
  refine (congrMul (congrMul (.eqRefl _) t₀) t₁).eqTrans ?_
  ipra_ring

theorem phi_one : Γ ⊢[PRAAx] phi (one : PTm n) ≐ one := by
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have g := LeanProofs.IPRA.AnalyticNumberTheory.Order.gcd_pos_right (a := zero) h1
  have hg := eq_one_of_dvd_one g (Prf.andE₂ (gcd_dvd_at g))
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) ?_).eqTrans (zero_add _))
  rw [inst2_tot]; exact eqb_of_eq hg

/-! ## Strong induction -/

/-- The claim `φ(n) ∏_{p∣n} p = n ∏_{p∣n} (p − 1)` at `N`, as two terms. -/
abbrev LHS (N : PTm n) : PTm n := phi N * PP F₁ N
abbrev RHS (N : PTm n) : PTm n := N * PP F₂ N

/-- `1 ∸ [LHS(N) = RHS(N)]`, over `0 = N`, `1 = x` (unused). -/
abbrev euB : PTm 2 := monus one (eqb (LHS (var 0)) (RHS (var 0)))

theorem inst2_eu (N x : PTm n) : inst2 euB N x = monus one (eqb (LHS N) (RHS N)) := by simp [inst2]

theorem eq_of_viol {A B : PTm n} (h : Γ ⊢[PRAAx] monus one (eqb A B) ≐ zero) : Γ ⊢[PRAAx] A ≐ B :=
  Common.eq_of_eqb_compl_zero h

theorem viol_of_eq {A B : PTm n} (h : Γ ⊢[PRAAx] A ≐ B) : Γ ⊢[PRAAx] monus one (eqb A B) ≐ zero :=
  Common.eqb_compl_zero_of_eq h

/-- The step when the prime `p` divides `n`. -/
theorem eu_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) (hV : Γ ⊢[PRAAx] ap2 (sumF euB) N x ≐ zero) :
    Γ ⊢[PRAAx] LHS N ≐ RHS N := by
  have hp2 : Γ ⊢[PRAAx] le two p := by have h := hp; unfold prime at h; exact Prf.andE₁ h
  have ha := val_eq_succ_pred_of_dvd hp2 hN hpN
  have hNe := cof_eq (m := N) hp2
  have hrm := cof_rem_eq_succ_pred hp2 hN
  have hm := cof_eq_succ_pred hp2 hN
  have hlt := cof_lt_of_dvd hp2 hN hpN
  -- The induction hypothesis at `m`.
  have h₀ := sum_zero_elim euB hV hlt
  rw [inst2_eu] at h₀
  have ih := eq_of_viol h₀
  -- Multiplicativity and the peeled products.
  have h₁ := pp_peel hp ha hrm hm F₁ hF₁
  have h₂ := pp_peel hp ha hrm hm F₂ hF₂
  rw [inst2_F₁] at h₁
  rw [inst2_F₂] at h₂
  -- The local factor: `φ(p^a) p = p^a (p − 1)`.
  have t := totient_prime_power_at (k := pred (val p N)) hp
  have e₂ : Γ ⊢[PRAAx] pw p (succ (pred (val p N))) ≐ pw p (val p N) := congrAp2 powF ha.eqSymm (.eqRefl _)
  have t' := (congrAdd (congrAp2 (sumF totBody) e₂ e₂) (.eqRefl _)).eqSymm.eqTrans (t.eqTrans e₂)
  have ps := (congrAp2 powF ha (.eqRefl p)).eqTrans (pw_succ p (pred (val p N)))
  have pq := eq_add_of_le (le_trans (le_succ_self _) hp2)
  -- Transport to `N = p^a m`.
  have hφ := Valuation.phi_prime_power_product hp hN
  have k₁ := (congrAp2 (prodF (pB F₁)) (congrSucc hNe) hNe).eqTrans h₁
  have k₂ := (congrAp2 (prodF (pB F₂)) (congrSucc hNe) hNe).eqTrans h₂
  ipra_lc Groth.ι (Q.mk _ (PP F₁ N)) * natEq hφ +
    Groth.ι (Q.mk _ (phi (pw p (val p N)))) * Groth.ι (Q.mk _ (phi (quo N (pw p (val p N))))) * natEq k₁ +
    Groth.ι (Q.mk _ (phi (pw p (val p N)))) * Groth.ι (Q.mk _ p) * natEq ih +
    Groth.ι (Q.mk _ (quo N (pw p (val p N)))) * Groth.ι (Q.mk _ (PP F₂ (quo N (pw p (val p N))))) * Groth.ι (Q.mk _ p) * natEq t' -
    Groth.ι (Q.mk _ N) * natEq k₂ -
    Groth.ι (Q.mk _ (PP F₂ (quo N (pw p (val p N))))) * Groth.ι (Q.mk _ (monus p one)) * natEq hNe +
    Groth.ι (Q.mk _ (quo N (pw p (val p N)))) * Groth.ι (Q.mk _ (PP F₂ (quo N (pw p (val p N))))) * natEq ps +
    Groth.ι (Q.mk _ (quo N (pw p (val p N)))) * Groth.ι (Q.mk _ (PP F₂ (quo N (pw p (val p N))))) * Groth.ι (Q.mk _ (pw p (val p N))) * natEq pq

theorem eu_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF euB) N x ≐ zero) : Γ ⊢[PRAAx] LHS N ≐ RHS N := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have hz : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    have h0 : ((N ≐ zero) :: Γ) ⊢[PRAAx] phi N ≐ zero := (congrAp2 (sumF totBody) hz hz).eqTrans (sum_zero _ _)
    exact ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)).eqTrans
      ((congrMul hz (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · refine .orE (zero_or_succ (pred N)) ?_ ?_
    · have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      refine (congrMul (congrAp2 (sumF totBody) e e) (congrAp2 (prodF (pB F₁)) (congrSucc e) e)).eqTrans ?_
      refine .eqTrans ?_ (congrMul e (congrAp2 (prodF (pB F₂)) (congrSucc e) e)).eqSymm
      exact (congrMul phi_one (pp_one F₁)).eqTrans (congrMul (.eqRefl _) (pp_one F₂)).eqSymm
    · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx]
          N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hpN := dvd_congr e.eqSymm (Prf.andE₁ (lpf_dvd (pred (pred N))))
      exact eu_found Prf.hyp1 (lpf_prime _) hpN hV.wk.wk

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev euF : Fm PTm 2 := ap2 (sumF euB) (var 0) (var 1) ≐ zero

private theorem eu₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] euF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_eu]
    exact viol_of_eq (eu_step Prf.hyp0)

/-- `thm:phi-product` (Euler product, denominator-cleared) at an arbitrary `n`:
`φ(n) ∏_{p ∣ n} p = n ∏_{p ∣ n} (p − 1)`, the products over primes `p ≤ n`. -/
theorem euler_product_at (N : PTm n) : Γ ⊢[PRAAx] LHS N ≐ RHS N := by
  have h := inst (Γ := Γ) eu₀ (![succ N, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim_last euB h
  rw [inst2_eu] at z
  exact eq_of_viol z

/-- `thm:phi-product` (Euler product): `φ(n) ∏_{p∣n} p = n ∏_{p∣n} (p − 1)`. -/
abbrev eulerProductFormula : Fm PTm 1 := LHS (var 0) ≐ RHS (var 0)

theorem euler_product : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 eulerProductFormula :=
  closeUniv 1 (euler_product_at (var 0))

end LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct

export_ipra AnalyticNumberTheory.EulerProduct (eq_of_viol eqb_comm' phi_one viol_of_eq)
