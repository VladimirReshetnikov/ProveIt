import IPRADerivations.AnalyticNumberTheory.SigmaPrimePower

/-!
# The divisor sum as a product over primes (`robin_ipra_research_2026-11-19`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `report.tex` (proof of `thm:three`: "Finite geometric
summation gives `A(n) = Π_i (1 − p_i^{−a_i−1})/(1 − p_i^{−1})`") and `lcm_bridge.tex` (Lemma "Exact finite
identity": "The finite geometric-series formula and multiplicativity of `σ` give `A(L_P) = Π_{p≤P} (1 −
p^{−a_p(P)−1})/(1 − p^{−1})`").

Cleared of denominators, for every `n ≥ 1`:

  `σ(n) · Π_{p ∣ n} (p − 1) = Π_{p ∣ n} (p^{v_p(n)+1} − 1)`                                   (`sigma_product`)

with the prime-indexed products `EulerProduct.PP` (`F₂ = q − 1` and `G(q, n) = q^{v_q(n)+1} − 1`). The factor `G`
depends on `n` through the valuation, so `EulerProduct.pp_peel` is generalized (`g_peel`): for `n = p^a m` with `p ∤ m`,
`v_q(n) = v_q(m)` for primes `q ≠ p` (`val_off`, `ValuationMul.val_unique` and Gauss's lemma) and `v_p(n) = a`
(`val_at`), so `Π_G(n) = Π_G(m) · (p^{a+1} − 1)`. The identity then follows by course-of-values induction through the
least prime factor (as in `Radical.phi_rad`), with `SigmaMult.sigma_mul` and `SigmaPrimePower.sigma_pow`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SigmaProduct

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower (sigma_pow sig_congr sig_one)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (PP inst2_pB eB inst2_e peelE prod_extend F₂ inst3_sub2
  inst3_mul' eqb_comm' eq_of_viol viol_of_eq pp_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (two_le_of_prime val_pos cof_rem_pos cof_pos cof_lt pm_peel)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val cof_eq cof_not_dvd isP isP_01 prime_of_isP isP_of_prime
  pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiEvenPow (shift_pw' shift_rpos p_dvd_n)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_mul')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `G(q, n) = q^{v_q(n)+1} − 1`, over `0 = q`, `1 = n`. -/
abbrev G : PTm 2 := monus (pw (var 0) (succ (val (var 0) (var 1)))) one

theorem inst2_G (q N : PTm n) : inst2 G q N = monus (pw q (succ (val q N))) one := by simp [inst2]

theorem monus_succ_one (x : PTm n) : Γ ⊢[PRAAx] monus (succ x) one ≐ x :=
  (succ_monus_succ _ _).eqTrans (monus_zero _)

theorem two_le_prime' {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] le two p := by
  have h := hp; unfold prime at h; exact Prf.andE₁ h

/-! ## Valuations along `n = p^a m` -/

section Peel

variable {p a m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
  (hrm : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p))) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))

theorem not_dvd_m (hrm : Γ ⊢[PRAAx] rem m p ≐ succ (pred (rem m p))) : Γ ⊢[PRAAx] neg (dvd p m) :=
  .impI (succ_ne_zero' _ (hrm.wk.eqSymm.eqTrans Prf.hyp0))

include hp hrm hm in
/-- `v_p(p^a m) = a` for `p ∤ m`. -/
theorem val_at : Γ ⊢[PRAAx] val p (pw p a * m) ≐ a :=
  val_unique (two_le_prime' hp) (pos_mul (pw_pos' (prime_eq_succ_pred hp) a) hm) (.eqRefl _) (not_dvd_m hrm)

include hp hm in
/-- `v_q(p^a m) = v_q(m)` for a prime `q ≠ p`. -/
theorem val_off {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hne : Γ ⊢[PRAAx] neg (q ≐ p)) :
    Γ ⊢[PRAAx] val q (pw p a * m) ≐ val q m := by
  have hq2 := two_le_prime' hq
  have hq1 := prime_eq_succ_pred hq
  have em := cof_eq (m := m) hq2
  have ndc := cof_not_dvd hq2 hm
  have gqp : Γ ⊢[PRAAx] gcd q p ≐ one := gcd_distinct_primes hq hp hne
  have gqP : Γ ⊢[PRAAx] gcd q (pw p a) ≐ one := cop_pow hq1 gqp a
  have nd : Γ ⊢[PRAAx] neg (dvd q (pw p a * quo m (pw q (val q m)))) :=
    .impI (.impE ndc.wk (gauss hq1.wk gqP.wk Prf.hyp0))
  have eN : Γ ⊢[PRAAx] pw p a * m ≐ pw q (val q m) * (pw p a * quo m (pw q (val q m))) :=
    (congrMul (.eqRefl _) em).eqTrans (by ipra_ring)
  exact val_unique hq2 (pos_mul (pw_pos' (prime_eq_succ_pred hp) a) hm) eN nd

include hp ha hrm hm in
/-- One factor of the peel: `G(q,n)^{e(q,n)} = G(q,m)^{e(q,m)} · G(q,n)^{[p = q]}`. -/
theorem pw_split (q : PTm n) :
    Γ ⊢[PRAAx] pw (inst2 G q (pw p a * m)) (inst2 eB q (pw p a * m)) ≐
      pw (inst2 G q m) (inst2 eB q m) * pw (inst2 G q (pw p a * m)) (eqb p q) := by
  have pe := peelE hp ha hrm q
  refine (congrAp2 powF pe (.eqRefl _)).eqTrans ((pw_add _ _ _).eqTrans (congrMul ?_
    (congrAp2 powF (eqb_comm' _ _) (.eqRefl _))))
  -- `G(q,n)^{e(q,m)} = G(q,m)^{e(q,m)}`
  refine .orE (isP_01 (Γ := Γ) q) ?_ ?_
  · let C : List (Fm PTm n) := (isP q ≐ zero) :: Γ
    have e0 : C ⊢[PRAAx] inst2 eB q m ≐ zero := by
      rw [inst2_e]; exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    exact ((congrAp2 powF e0 (.eqRefl _)).eqTrans (pw_zero _)).eqTrans
      ((congrAp2 powF e0 (.eqRefl _)).eqTrans (pw_zero _)).eqSymm
  · let C : List (Fm PTm n) := (isP q ≐ one) :: Γ
    have hq : C ⊢[PRAAx] prime q := prime_of_isP Prf.hyp0
    refine .orE (eq_or_ne (Γ := C) q p) ?_ ?_
    · -- `q = p`: `p ∤ m`, so `e(p, m) = 0`
      let C' : List (Fm PTm n) := (q ≐ p) :: C
      have r : C' ⊢[PRAAx] eqb (rem m q) zero ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        have e : ((rem m q ≐ zero) :: C') ⊢[PRAAx] rem m p ≐ zero :=
          (congrAp2 remF (.eqRefl _) Prf.hyp1.eqSymm).eqTrans Prf.hyp0
        exact succ_ne_zero' _ (hrm.wk.wk.wk.eqSymm.eqTrans e)
      have e0 : C' ⊢[PRAAx] inst2 eB q m ≐ zero := by
        rw [inst2_e]; exact (congrMul (.eqRefl _) r).eqTrans (mul_zero _)
      exact ((congrAp2 powF e0 (.eqRefl _)).eqTrans (pw_zero _)).eqTrans
        ((congrAp2 powF e0 (.eqRefl _)).eqTrans (pw_zero _)).eqSymm
    · -- `q ≠ p`: `v_q(n) = v_q(m)`
      let C' : List (Fm PTm n) := neg (q ≐ p) :: C
      have v := val_off hp.wk.wk hm.wk.wk hq.wk Prf.hyp0 (a := a)
      rw [inst2_G, inst2_G]
      exact congrAp2 powF (.eqRefl _) (congrMonus (congrAp2 powF (congrSucc v) (.eqRefl _)) (.eqRefl _))

/-! ## The peel of the product -/

/-- `G(q, n)^{e(q,n)}` read at `⟨m, n⟩`: the first factor at `m`. -/
def f1 : PTm 3 := Syn.subst ![var 0, fstT (var 2)] (EulerProduct.pB G)
/-- The delta factor at `n`. -/
def f2 : PTm 3 := Syn.subst ![var 0, var 1, sndT (var 2)] (deltaBody G)

theorem inst3_f1 (j c x : PTm n) : inst3 f1 j c x = inst2 (EulerProduct.pB G) j (fstT x) := by
  simp only [inst3, inst2, f1, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem inst3_f2 (j c x : PTm n) : inst3 f2 j c x = inst3 (deltaBody G) j c (sndT x) := by
  simp only [inst3, f2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

include hp ha hrm hm in
/-- `Π_G(p^a m) = Π_G(m) · (p^{a+1} − 1)`. -/
theorem g_peel : Γ ⊢[PRAAx] PP G (pw p a * m) ≐ PP G m * monus (pw p (succ a)) one := by
  have hP := pw_pos' (prime_eq_succ_pred hp) a
  have hn := pos_mul hP hm
  have s₁ := (Permutation.prod2_eq_prod (Γ := Γ) (EulerProduct.pB G) (succ (pw p a * m)) p (pw p a * m)).eqSymm
  have s₂ : Γ ⊢[PRAAx] ap3 (prod2F (Syn.subst ![var 0, var 2] (EulerProduct.pB G))) (succ (pw p a * m)) p (pw p a * m) ≐
      ap3 (prod2F (f1 * f2)) (succ (pw p a * m)) p (pairT m (pw p a * m)) := by
    refine prod2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst3_sub2, inst3_mul', inst3_f1, inst3_f2, inst3_delta, shift_pairT, shift_mul', shift_pw', EulerProduct.inst2_pB, EulerProduct.inst2_pB]
    refine (pw_split (prime_shift hp).wk (shift_pos ha).wk (shift_rpos hrm).wk (shift_pos hm).wk (var 0)).eqTrans ?_
    exact congrMul (congrAp2 powF (congrInst2 eB (.eqRefl _) (fst_pair _ _)).eqSymm
        (congrInst2 G (.eqRefl _) (fst_pair _ _)).eqSymm)
      (congrAp2 powF (.eqRefl _) (congrInst2 G (.eqRefl _) (snd_pair _ _)).eqSymm)
  have s₃ := prod2_mul (Γ := Γ) f1 f2 (succ (pw p a * m)) p (pairT m (pw p a * m))
  have e : Γ ⊢[PRAAx] succ (pw p a * m) ≐ succ m + pred (pw p a) * m := by
    ipra_lc Groth.ι (Q.mk _ m) * natEq hP
  have s₄ : Γ ⊢[PRAAx] ap3 (prod2F f1) (succ (pw p a * m)) p (pairT m (pw p a * m)) ≐ PP G m := by
    refine (prod2_congr_bounded f1 (Syn.subst ![var 0, var 2] (EulerProduct.pB G)) p (pairT m (pw p a * m)) p m _
      (.allI (.impI ?_))).eqTrans ?_
    · rw [inst3_f1, inst3_sub2, shift_pairT]
      exact congrInst2 (EulerProduct.pB G) (.eqRefl _) (fst_pair _ _)
    · exact (Permutation.prod2_eq_prod (EulerProduct.pB G) (succ (pw p a * m)) p m).eqTrans
        ((congrAp2 (prodF (EulerProduct.pB G)) e (.eqRefl m)).eqTrans (prod_extend G hm _))
  have hlt : Γ ⊢[PRAAx] lt p (succ (pw p a * m)) :=
    (succ_monus_succ _ _).eqTrans (dvd_le' (prime_eq_succ_pred hp) (p_dvd_n (m := m) hp ha) hn)
  have s₅ : Γ ⊢[PRAAx] ap3 (prod2F f2) (succ (pw p a * m)) p (pairT m (pw p a * m)) ≐
      monus (pw p (succ a)) one := by
    refine (prod2_congr_bounded f2 (deltaBody G) p (pairT m (pw p a * m)) p (pw p a * m) _
      (.allI (.impI ?_))).eqTrans ((prod2_delta G hlt).eqTrans ?_)
    · rw [inst3_f2, shift_pairT]
      exact congrInst3 (deltaBody G) (.eqRefl _) (.eqRefl _) (snd_pair _ _)
    · rw [inst2_G]
      exact congrMonus (congrAp2 powF (congrSucc (val_at hp hrm hm)) (.eqRefl _)) (.eqRefl _)
  exact s₁.eqTrans (s₂.eqTrans (s₃.eqTrans (congrMul s₄ s₅)))

end Peel

/-! ## The identity, by course-of-values induction -/

/-- The violation `sg(N) · [σ(N) Π_{F₂}(N) ≠ Π_G(N)]` over `0 = N`. -/
abbrev vB : PTm 2 := sg (var 0) * monus one (eqb (sig (var 0) * PP F₂ (var 0)) (PP G (var 0)))

theorem inst2_vB (N x : PTm n) :
    inst2 vB N x = sg N * monus one (eqb (sig N * PP F₂ N) (PP G N)) := by simp [inst2]

/-- The identity at `N ≥ 2`, given it below `N`. -/
theorem sp_found {N p x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp : Γ ⊢[PRAAx] prime p)
    (hpN : Γ ⊢[PRAAx] dvd p N) (hV : Γ ⊢[PRAAx] ap2 (sumF vB) N x ≐ zero) :
    Γ ⊢[PRAAx] sig N * PP F₂ N ≐ PP G N := by
  have hp1 := prime_eq_succ_pred hp
  have hmp := cof_pos hN hp hpN
  have h₀ := sum_zero_elim vB hV (cof_lt hN hp hpN)
  rw [inst2_vB] at h₀
  have sg1 : Γ ⊢[PRAAx] sg (quo N (pw p (val p N))) ≐ one := (congrSg hmp).eqTrans (sg_succ _)
  have ih := eq_of_viol ((one_mul _).eqSymm.eqTrans ((congrMul sg1.eqSymm (.eqRefl _)).eqTrans h₀))
  have hNe := cof_eq (m := N) (two_le_of_prime hN hp hpN)
  have hrm := cof_rem_pos hN hp hpN
  have ha := val_pos hN hp hpN
  -- multiplicativity
  have g4 := Valuation.coprime_prime_power_cofactor hp hN
  have s1 : Γ ⊢[PRAAx] sig N ≐ sig (pw p (val p N)) * sig (quo N (pw p (val p N))) :=
    (sig_congr hNe).eqTrans (sigma_mul (pw_pos' hp1 _) hmp g4)
  have s2 := pm_peel hN hp hpN
  have s3 : Γ ⊢[PRAAx] PP G N ≐ PP G (quo N (pw p (val p N))) * monus (pw p (succ (val p N))) one :=
    (congrAp2 (prodF (EulerProduct.pB G)) (congrSucc hNe) hNe).eqTrans (g_peel hp ha hrm hmp)
  have s4 : Γ ⊢[PRAAx] monus (pw p (succ (val p N))) one ≐ pred p * sig (pw p (val p N)) :=
    (congrMonus ((sigma_pow hp (val p N)).eqSymm.eqTrans ((add_succ _ _).eqTrans (congrSucc (add_zero _))))
      (.eqRefl _)).eqTrans (monus_succ_one _)
  have s5 : Γ ⊢[PRAAx] monus p one ≐ pred p := (congrMonus hp1 (.eqRefl _)).eqTrans (monus_succ_one _)
  ipra_lc 𝔞 (PP F₂ N) * natEq s1 + 𝔞 (sig (pw p (val p N))) * 𝔞 (sig (quo N (pw p (val p N)))) * natEq s2 +
    𝔞 (sig (pw p (val p N))) * 𝔞 (sig (quo N (pw p (val p N)))) * 𝔞 (PP F₂ (quo N (pw p (val p N)))) * natEq s5 +
    𝔞 (sig (pw p (val p N))) * 𝔞 (pred p) * natEq ih - 𝔞 (PP G (quo N (pw p (val p N)))) * natEq s4 - natEq s3

/-- The violation vanishes at every `N`, given it below `N`. -/
theorem sp_step {N x : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF vB) N x ≐ zero) :
    Γ ⊢[PRAAx] sg N * monus one (eqb (sig N * PP F₂ N) (PP G N)) ≐ zero := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · -- `N = 1`
    have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ one :=
      Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    have eq1 : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] sig N * PP F₂ N ≐ PP G N := by
      refine (congrMul ((sig_congr e).eqTrans sig_one) ((congrAp2 (prodF (EulerProduct.pB F₂)) (congrSucc e) e).eqTrans
        (pp_one F₂))).eqTrans ?_
      exact (one_mul _).eqTrans ((congrAp2 (prodF (EulerProduct.pB G)) (congrSucc e) e).eqTrans (pp_one G)).eqSymm
    exact (congrMul (.eqRefl _) (viol_of_eq eq1)).eqTrans (mul_zero _)
  · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx]
        N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
    have f := sp_found Prf.hyp1 (lpf_prime _) (dvd_congr e.eqSymm (Prf.andE₁ (lpf_dvd _))) hV.wk.wk
    exact (congrMul (.eqRefl _) (viol_of_eq f)).eqTrans (mul_zero _)

private abbrev spF : Fm PTm 2 := ap2 (sumF vB) (var 0) (var 1) ≐ zero

private theorem sp₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] spF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_vB]
    exact sp_step Prf.hyp0

/-- `σ(n) Π_{p ∣ n} (p − 1) = Π_{p ∣ n} (p^{v_p(n)+1} − 1)` for `n ≥ 1`. -/
theorem sigma_product {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] sig N * PP F₂ N ≐ PP G N := by
  have h := inst (Γ := Γ) sp₀ (![succ N, zero] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim_last vB h
  rw [inst2_vB] at z
  have sg1 : Γ ⊢[PRAAx] sg N ≐ one := (congrSg hN).eqTrans (sg_succ _)
  exact eq_of_viol ((one_mul _).eqSymm.eqTrans ((congrMul sg1.eqSymm (.eqRefl _)).eqTrans z))

end LeanProofs.IPRA.AnalyticNumberTheory.SigmaProduct
