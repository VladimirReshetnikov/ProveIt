import IPRADerivations.AnalyticNumberTheory.BinomialLcm
import IPRADerivations.Probability.MedianOfMedians

/-!
# Explicit Chebyshev bounds, integer form

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Corollary `cor:chebyshev-bounds`.
Since `ψ(N) = log lcm(1, …, N)` (`thm:psi-lcm`), the logarithmic bounds are the integer inequalities

* `double_lcm`: `lcm(1, …, 2n) ≤ lcm(1, …, n) · 4^n`, i.e. `ψ(2n) − ψ(n) ≤ 2n log 2`: by valuations
  `lcm(1, …, 2n) ∣ lcm(1, …, n) · ∏_{n<p^a≤2n} p` (`val_double`, `double_dvd`), and the window product
  divides `C(2n, n) ≤ 4^n` (`thm:binomial-lcm`);
* `lcmu_upper`: `lcm(1, …, x) ≤ 2^{4x}`, i.e. `ψ(x) ≤ 4 x log 2`, by course-of-values induction
  (`strong_ind`) through `x ≤ 2⌈x/2⌉`;
* `lcmu_lower2`: `2^n ≤ lcm(1, …, 2n)` for `n ≥ 3`, from `4^n ≤ (2n + 1) C(2n, n)`, `2n + 1 ≤ 2^n`
  (`two_pow_ge`) and `C(2n, n) ∣ lcm(1, …, 2n)`;
* `lcmu_lower`: `2^x ≤ lcm(1, …, x)^3` for `x ≥ 6`, i.e. `ψ(x) ≥ (log 2 / 3) x`.

The passage to real logarithms (rational approximations of `log 2`) is not formalized.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (subst_dvd one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu lcmu_pos lcmu_dvd lcmu_succ lcmu_zero lcm_valuation)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (dvd_of_val_le Pw PE cB XE val_PE inst2_XE inst2_cB
  window_dvd central_dvd_lcm PE_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg)
open LeanProofs.IPRA.Combinatorics.Catalan (cb)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Monotonicity of `lcm(1, …, N)` -/

theorem lcmu_dvd_add (a d : PTm n) : Γ ⊢[PRAAx] dvd (lcmu a) (lcmu (a + d)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (dvd (lcmu (Syn.shift a)) (lcmu (Syn.shift a + var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_dvd, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact (congrAp2 remF (congrAp2 LcmUpto.lcmuF (add_zero _) (.eqRefl _)) (.eqRefl _)).eqTrans (dvd_self' (lcmu_pos a))
    · simp only [subst_dvd, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero]
      let D : List (Fm PTm (n + 1)) := dvd (lcmu (Syn.shift a)) (lcmu (Syn.shift a + var 0)) :: Γ.map Fm.shift
      have h2 := Prf.andE₁ (lcmu_dvd (Γ := D) (Syn.shift a + var 0))
      have e : D ⊢[PRAAx] lcmu (Syn.shift a + succ (var 0)) ≐ lcmu (succ (Syn.shift a + var 0)) :=
        congrAp2 LcmUpto.lcmuF (add_succ _ _) (.eqRefl _)
      exact (congrAp2 remF e (.eqRefl _)).eqTrans (dvd_trans' (lcmu_pos _) (lcmu_pos _) Prf.hyp0 h2)
  have h := Prf.allE d hall
  simp only [subst_dvd, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at h
  exact h

/-- `lcm(1, …, a) ≤ lcm(1, …, b)` for `a ≤ b`. -/
theorem lcmu_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (lcmu a) (lcmu b) :=
  dvd_le' (lcmu_pos a) ((congrAp2 remF (congrAp2 LcmUpto.lcmuF (eq_add_of_le h) (.eqRefl _)) (.eqRefl _)).eqTrans
    (lcmu_dvd_add a _)) (lcmu_pos b)

/-! ## The doubling bound -/

/-- `v_q(lcm(1, …, 2k)) ≤ v_q(lcm(1, …, k)) + [q prime][k < q^E][q ≤ 2k]` with `E = v_q(lcm(1, …, 2k))`. -/
theorem val_double {q k : PTm n} (hq : Γ ⊢[PRAAx] prime q) :
    Γ ⊢[PRAAx] le (val q (lcmu (two * k))) (val q (lcmu k) +
      (isP q * sg (monus (pw q (val q (lcmu (two * k)))) k)) * sg (monus (succ (two * k)) q)) := by
  have hq2 := prime_two hq
  have qpos := p_pos hq2
  have IA := lcm_valuation hq (two * k); have IB := lcm_valuation hq k
  have A1 := Prf.andE₁ IA; have B2 := Prf.andE₂ IB
  refine .orE (zero_or_succ (val q (lcmu (two * k)))) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)) ?_
  let C : List (Fm PTm n) := (val q (lcmu (two * k)) ≐ succ (pred (val q (lcmu (two * k))))) :: Γ
  have Ep : C ⊢[PRAAx] val q (lcmu (two * k)) ≐ succ (pred (val q (lcmu (two * k)))) := Prf.hyp0
  have sE : C ⊢[PRAAx] sg (val q (lcmu (two * k))) ≐ one := (congrSg Ep).eqTrans (sg_succ _)
  have pE : C ⊢[PRAAx] le (pw q (val q (lcmu (two * k)))) (two * k) :=
    le_congr ((congrMul sE (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) A1.wk
  have l1E : C ⊢[PRAAx] le one (val q (lcmu (two * k))) :=
    le_of_eq_add (d := pred (val q (lcmu (two * k)))) (Ep.eqTrans (by ipra_ring))
  have qE : C ⊢[PRAAx] le q (pw q (val q (lcmu (two * k)))) :=
    le_congr (pw_one q) (.eqRefl _) (PowerCleared.pw_le_exp qpos.wk l1E)
  have s1 : C ⊢[PRAAx] sg (monus (succ (two * k)) q) ≐ one :=
    sg_lt ((succ_monus_succ _ _).eqTrans (le_trans qE pE))
  have rhs : C ⊢[PRAAx] val q (lcmu k) + (isP q * sg (monus (pw q (val q (lcmu (two * k)))) k)) *
      sg (monus (succ (two * k)) q) ≐ val q (lcmu k) + sg (monus (pw q (val q (lcmu (two * k)))) k) :=
    congrAdd (.eqRefl _) ((congrMul ((congrMul (isP_of_prime hq.wk) (.eqRefl _)).eqTrans (one_mul _)) s1).eqTrans
      (EulerDomination.mul_one' _))
  refine le_congr (.eqRefl _) rhs.eqSymm ?_
  refine .orE (lt_or_le k (pw q (val q (lcmu (two * k))))) ?_ ?_
  · -- `k < q^E`: `E ≤ e + 1`, since `q^{e+2} ≥ 2(k + 1) > 2k`
    let C1 : List (Fm PTm n) := lt k (pw q (val q (lcmu (two * k)))) :: C
    refine le_congr (.eqRefl _) (congrAdd (.eqRefl _) (sg_lt Prf.hyp0)).eqSymm ?_
    refine .orE (lt_or_le (succ (val q (lcmu k))) (val q (lcmu (two * k)))) ?_ ?_
    · have h : (lt (succ (val q (lcmu k))) (val q (lcmu (two * k))) :: C1) ⊢[PRAAx]
          le (succ (succ (val q (lcmu k)))) (val q (lcmu (two * k))) := Prf.hyp0
      have p1 := le_trans (PowerCleared.pw_le_exp qpos.wk.wk.wk h) pE.wk.wk
      have p2 := le_congr (pw_succ _ _) (.eqRefl _) p1
      have p3 := le_trans (le_mul_mono B2.wk.wk.wk hq2.wk.wk.wk) p2
      have p4 : (lt (succ (val q (lcmu k))) (val q (lcmu (two * k))) :: C1) ⊢[PRAAx]
          le (succ (two * k)) (succ k * two) := le_of_eq_add (d := one) (by ipra_ring)
      exact not_succ_le_self _ _ (le_trans p4 p3)
    · exact le_congr (.eqRefl _) (by ipra_ring) Prf.hyp0
  · -- `q^E ≤ k`: `E ≤ e`
    let C2 : List (Fm PTm n) := le (pw q (val q (lcmu (two * k)))) k :: C
    refine le_congr (.eqRefl _) ((congrAdd (.eqRefl _) (sg_le Prf.hyp0)).eqTrans (add_zero _)).eqSymm ?_
    refine .orE (lt_or_le (val q (lcmu k)) (val q (lcmu (two * k)))) ?_ Prf.hyp0
    have h : (lt (val q (lcmu k)) (val q (lcmu (two * k))) :: C2) ⊢[PRAAx]
        le (succ (val q (lcmu k))) (val q (lcmu (two * k))) := Prf.hyp0
    exact le_lt_absurd _ (le_trans (PowerCleared.pw_le_exp qpos.wk.wk.wk h) (Prf.hyp1 : _ ⊢[PRAAx] le (pw q (val q (lcmu (two * k)))) k)) B2.wk.wk.wk

/-- `lcm(1, …, 2k) ∣ lcm(1, …, k) · ∏_{k<p^a≤2k} p`. -/
theorem double_dvd (k : PTm n) : Γ ⊢[PRAAx] dvd (lcmu (two * k)) (lcmu k * Pw k) := by
  have pp := Combinatorics.Binomial.pos_mul (lcmu_pos (Γ := Γ) k) (PE_pos (Γ := Γ) cB (succ (two * k)) k)
  have hs1 : Syn.shift (lcmu (two * k)) = lcmu (two * Syn.shift k) := by simp [Syn.shift]
  have hs2 : Syn.shift (lcmu k * Pw k) = lcmu (Syn.shift k) * Pw (Syn.shift k) := by simp [Syn.shift]
  refine dvd_of_val_le (N := succ (lcmu (two * k) + lcmu k * Pw k)) (lcmu_pos _) pp
    ((succ_monus_succ _ _).eqTrans (le_add_right _ _)) ((succ_monus_succ _ _).eqTrans (le_add_left _ _))
    (.allI (.impI (.impI ?_)))
  rw [hs1, hs2]
  let Q : List (Fm PTm (n + 1)) :=
    (isP (var 0) ≐ one) :: lt (var 0) (Syn.shift (succ (lcmu (two * k) + lcmu k * Pw k))) :: Γ.map Fm.shift
  have hv : Q ⊢[PRAAx] prime (var 0) := prime_of_isP Prf.hyp0
  have vm := val_mul hv (lcmu_pos (Syn.shift k)) (PE_pos cB (succ (two * Syn.shift k)) (Syn.shift k))
  have vp := val_PE hv cB (succ (two * Syn.shift k)) (Syn.shift k)
  rw [inst2_XE, inst2_cB] at vp
  exact le_congr (.eqRefl _) (vm.eqTrans (congrAdd (.eqRefl _) vp)).eqSymm (val_double hv)

/-- `cor:chebyshev-bounds`, `ψ(2n) − ψ(n) ≤ 2n log 2`: `lcm(1, …, 2k) ≤ lcm(1, …, k) · 4^k`. -/
theorem double_lcm (k : PTm n) : Γ ⊢[PRAAx] le (lcmu (two * k)) (lcmu k * pw two (two * k)) := by
  have pp := Combinatorics.Binomial.pos_mul (lcmu_pos (Γ := Γ) k) (PE_pos (Γ := Γ) cB (succ (two * k)) k)
  have cpos := BinomialThree.pos_of_one_le (Combinatorics.CentralBinomial.central_pos (Γ := Γ) k)
  have l1 := dvd_le' (lcmu_pos _) (double_dvd k) pp
  have l2 : Γ ⊢[PRAAx] le (Pw k) (cb k) := dvd_le' (PE_pos _ _ _) (window_dvd k) cpos
  exact le_trans l1 (le_mul_mono (le_refl _) (le_trans l2 (Combinatorics.CentralBinomial.central_upper k)))

/-! ## The upper bound `lcm(1, …, x) ≤ 2^{4x}` -/

/-- `lcm(1, …, x) ∸ 2^{4x}`, over `0 = x`. -/
abbrev QB : PTm 2 := monus (lcmu (var 0)) (pw two (two * (two * var 0)))

theorem inst2_QB (m x : PTm n) : inst2 QB m x = monus (lcmu m) (pw two (two * (two * m))) := by simp [inst2]

theorem two_pos' : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

theorem lcmu_one : Γ ⊢[PRAAx] lcmu (one : PTm n) ≐ one := by
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have g1 : Γ ⊢[PRAAx] gcd (one : PTm n) one ≐ one := eq_one_of_dvd_one (gcd_pos h1) (Prf.andE₁ (gcd_dvd' (b := one) h1))
  have cg : Γ ⊢[PRAAx] gcd (lcmu (zero : PTm n)) (succ zero) ≐ one :=
    (DiophantineNumberTheory.QuarticStep.congrGcd lcmu_zero (.eqRefl _)).eqTrans g1
  refine (lcmu_succ zero).eqTrans ((congrAp2 quoF (congrMul lcmu_zero (.eqRefl _)) cg).eqTrans ?_)
  exact Totient.quo_eq h1 (r := zero) (by ipra_ring) (Multiplicative.zero_lt' h1)

/-- The course-of-values step: from `lcm(1, …, i) ≤ 2^{4i}` for all `i < m`, the bound at `m`. -/
theorem upper_step {m x : PTm n} (hS : Γ ⊢[PRAAx] ap2 (sumF QB) m x ≐ zero) :
    Γ ⊢[PRAAx] le (lcmu m) (pw two (two * (two * m))) := by
  refine .orE (lt_or_le m two) ?_ ?_
  · -- `m ≤ 1`
    refine .orE (zero_or_succ m) ?_ ?_
    · have h : ((m ≐ zero) :: lt m two :: Γ) ⊢[PRAAx] m ≐ zero := Prf.hyp0
      refine le_congr ((congrAp2 LcmUpto.lcmuF h (.eqRefl _)).eqTrans lcmu_zero).eqSymm (.eqRefl _) ?_
      exact one_le_pos (pw_pos' two_pos' _)
    · have h : ((m ≐ succ (pred m)) :: lt m two :: Γ) ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
      have l : ((m ≐ succ (pred m)) :: lt m two :: Γ) ⊢[PRAAx] le m one :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1
      have m1 : ((m ≐ succ (pred m)) :: lt m two :: Γ) ⊢[PRAAx] m ≐ one := le_antisymm l (one_le_pos h)
      refine le_congr ((congrAp2 LcmUpto.lcmuF m1 (.eqRefl _)).eqTrans lcmu_one).eqSymm (.eqRefl _) ?_
      exact one_le_pos (pw_pos' two_pos' _)
  · let C : List (Fm PTm n) := le two m :: Γ
    have h2 : C ⊢[PRAAx] le two m := Prf.hyp0
    have dvP : C ⊢[PRAAx] m ≐ two * quo m two + rem m two := GcdFiber.div_eq two_pos'
    have rl : C ⊢[PRAAx] le (rem m two) one := (succ_monus_succ _ _).eqSymm.eqTrans (Multiplicative.rem_lt' two_pos' m)
    -- `s = ⌊m/2⌋ ≥ 1`
    have spos : C ⊢[PRAAx] quo m two ≐ succ (pred (quo m two)) := by
      refine .orE (zero_or_succ (quo m two)) ?_ Prf.hyp0
      have mr : ((quo m two ≐ zero) :: C) ⊢[PRAAx] m ≐ rem m two :=
        dvP.wk.eqTrans ((congrAdd ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_add _))
      have h21 : ((quo m two ≐ zero) :: C) ⊢[PRAAx] le two one := le_trans h2.wk (le_congr mr.eqSymm (.eqRefl _) rl.wk)
      exact lt_zero_absurd _ ((succ_monus_succ one zero).eqSymm.eqTrans h21)
    have dv := natEq dvP
    have sp := natEq spos
    have r1 := natEq (eq_add_of_le rl)
    have tl : C ⊢[PRAAx] lt (quo m two + rem m two) m :=
      le_of_eq_add (d := pred (quo m two)) (by ipra_lc dv + sp)
    have mt : C ⊢[PRAAx] le m (two * (quo m two + rem m two)) :=
      le_of_eq_add (d := rem m two) (by ipra_lc -dv)
    have ex : C ⊢[PRAAx] le (two * (two * (quo m two + rem m two)) + two * (quo m two + rem m two)) (two * (two * m)) :=
      le_of_eq_add (d := two * (pred (quo m two) + monus one (rem m two)))
        (by ipra_lc 4 * dv + 2 * sp + 2 * r1)
    have ih := sum_zero_elim QB hS.wk tl
    rw [inst2_QB] at ih
    exact le_trans (lcmu_le mt) (le_trans (double_lcm _) (le_trans (mul_le_mul_right _ ih)
      (le_congr (pw_add _ _ _) (.eqRefl _) (PowerCleared.pw_le_exp two_pos' ex))))

/-- `cor:chebyshev-bounds`, `ψ(x) ≤ 4 x log 2`: `lcm(1, …, x) ≤ 2^{4x}` for every `x`. -/
theorem lcmu_upper (x : PTm n) : Γ ⊢[PRAAx] le (lcmu x) (pw two (two * (two * x))) := by
  have h := Probability.MedianOfMedians.strong_ind (Γ := Γ) QB zero (.allI (.impI (by
    rw [inst2_QB]
    exact upper_step Prf.hyp0))) x
  rw [inst2_QB] at h
  exact h

/-! ## The lower bounds -/

/-- `2n + 1 ≤ 2^n` for `n ≥ 3`. -/
theorem two_pow_ge {N : PTm n} (h : Γ ⊢[PRAAx] le (succ two) N) : Γ ⊢[PRAAx] le (succ (two * N)) (pw two N) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (succ (two * (succ two + var 0))) (pw two (succ two + var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have p3 := natEq ((pw_succ (Γ := Γ) two (succ (succ zero))).eqTrans (congrMul ((pw_succ two (succ zero)).eqTrans
        (congrMul ((pw_succ two zero).eqTrans (congrMul (pw_zero two) (.eqRefl _))) (.eqRefl _))) (.eqRefl _)))
      exact le_of_eq_add (d := one) (by ipra_lc natEq (congrAp2 powF (add_zero (Γ := Γ) (succ two)) (.eqRefl two)) + p3)
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := le (succ (two * (succ two + var 0))) (pw two (succ two + var 0)) :: Γ.map Fm.shift
      refine le_of_eq_add (d := monus (pw two (succ two + var 0)) (succ (two * (succ two + var 0))) +
        monus (pw two (succ two + var 0)) (succ (two * (succ two + var 0))) + two * var 0 + succ (succ (succ two))) ?_
      ipra_lc natEq ((congrAp2 powF (add_succ (Γ := D) (succ two) (var 0)) (.eqRefl two)).eqTrans (pw_succ two _)) +
        2 * natEq (eq_add_of_le (Prf.hyp0 : D ⊢[PRAAx] _))
  have i := Prf.allE (monus N (succ two)) hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  have e := (eq_add_of_le h).eqSymm
  exact le_congr (congrSucc (congrMul (.eqRefl _) e)) (congrAp2 powF e (.eqRefl _)) i

/-- `ψ(2n) ≥ n log 2` for `n ≥ 3`: `2^n ≤ lcm(1, …, 2n)`. -/
theorem lcmu_lower2 {N : PTm n} (h : Γ ⊢[PRAAx] le (succ two) N) : Γ ⊢[PRAAx] le (pw two N) (lcmu (two * N)) := by
  have cpos := BinomialThree.pos_of_one_le (Combinatorics.CentralBinomial.central_pos (Γ := Γ) N)
  have cl := Combinatorics.CentralBinomial.central_lower (Γ := Γ) N
  have m1 := mul_le_mul_right (binom (two * N) N) (two_pow_ge h)
  have e : Γ ⊢[PRAAx] pw two (two * N) ≐ pw two N * pw two N :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] two * N ≐ N + N) (.eqRefl two)).eqTrans (pw_add _ _ _)
  have c := le_cancel_pos (pw_pos' two_pos' N) (le_congr e (.eqRefl _) (le_trans cl m1))
  exact le_trans c (dvd_le' cpos (central_dvd_lcm N) (lcmu_pos _))

/-- `cor:chebyshev-bounds`, `ψ(x) ≥ (log 2 / 3) x` for `x ≥ 6`: `2^x ≤ lcm(1, …, x)^3`. -/
theorem lcmu_lower {x : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ (succ (succ two)))) x) :
    Γ ⊢[PRAAx] le (pw two x) (lcmu x * (lcmu x * lcmu x)) := by
  have dvP : Γ ⊢[PRAAx] x ≐ two * quo x two + rem x two := GcdFiber.div_eq two_pos'
  have rl : Γ ⊢[PRAAx] le (rem x two) one := (succ_monus_succ _ _).eqSymm.eqTrans (Multiplicative.rem_lt' two_pos' x)
  have dv := natEq dvP; have r1 := natEq (eq_add_of_le rl); have h6 := natEq (eq_add_of_le h)
  -- `s = ⌊x/2⌋ ≥ 3`
  have s3 : Γ ⊢[PRAAx] le (succ two) (quo x two) := by
    refine .orE (lt_or_le (quo x two) (succ two)) ?_ Prf.hyp0
    have l := natEq (eq_add_of_le ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0 :
      (lt (quo x two) (succ two) :: Γ) ⊢[PRAAx] le (quo x two) two))
    let C : List (Fm PTm n) := lt (quo x two) (succ two) :: Γ
    have dv' := natEq (dvP.wk : C ⊢[PRAAx] _); have r1' := natEq (eq_add_of_le (rl.wk : C ⊢[PRAAx] _))
    have h6' := natEq (eq_add_of_le (h.wk : C ⊢[PRAAx] _))
    refine succ_ne_zero' (a := two * monus two (quo x two) + monus one (rem x two) + monus x (succ (succ (succ (succ two))))) _ ?_
    ipra_lc -h6' + dv' - 2 * l - r1'
  have l2 : Γ ⊢[PRAAx] le (two * quo x two) x := le_of_eq_add (d := rem x two) dvP
  have l3 : Γ ⊢[PRAAx] le x (quo x two + (quo x two + quo x two)) := by
    have e3 := natEq (eq_add_of_le s3)
    exact le_of_eq_add (d := monus one (rem x two) + monus (quo x two) (succ two) + two)
      (by ipra_lc -dv + r1 + e3)
  have b := le_trans (lcmu_lower2 s3) (lcmu_le l2)
  refine le_trans (PowerCleared.pw_le_exp two_pos' l3) ?_
  refine le_congr ((congrMul (.eqRefl _) (pw_add _ _ _)).eqSymm.eqTrans (pw_add _ _ _).eqSymm) (.eqRefl _) ?_
  exact le_mul_mono b (le_mul_mono b b)

end LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds
