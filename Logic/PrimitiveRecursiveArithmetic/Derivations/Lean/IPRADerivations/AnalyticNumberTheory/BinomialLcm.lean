import IPRADerivations.AnalyticNumberTheory.LcmUpto
import IPRADerivations.Combinatorics.CentralBinomial
import IPRADerivations.AnalyticNumberTheory.Smooth
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The central binomial coefficient divides `lcm(1, …, 2n)`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:binomial-lcm`,
the divisibility chain `∏_{n<p^a≤2n} p ∣ C(2n, n) ∣ lcm(1, …, 2n)` (`binomial_lcm`).

* `dvd_of_val_le`: a divisibility criterion from valuations — if `1 ≤ a, b < N` and
  `v_p(a) ≤ v_p(b)` for every prime `p < N`, then `a ∣ b` (from `FactorVector.reconstruct`
  and the factorwise divisibility of `∏_{p<N} p^{v_p}`, `R_dvd`);
* `quo_two`: `⌊2k/q⌋ ∈ {2⌊k/q⌋, 2⌊k/q⌋ + 1}`;
* `binom_val`: Legendre's formula for `C(2k, k)`:
  `v_p(C(2k, k)) + 2 ∑_{j<2k} ⌊k/p^{j+1}⌋ = ∑_{j<2k} ⌊2k/p^{j+1}⌋`;
* `binom_val_le`: `v_p(C(2k, k)) ≤ v_p(lcm(1, …, 2k))`, since each term `⌊2k/q⌋ − 2⌊k/q⌋` is at most
  one and vanishes once `q = p^{j+1} > 2k`, i.e. for `j ≥ v_p(lcm(1, …, 2k))` (`lem:lcm-valuation`);
* `central_dvd_lcm`: `C(2k, k) ∣ lcm(1, …, 2k)`;
* `val_PE`: `v_q(∏_{i<M} i^{[i prime] E(i)}) = [q prime] E(q) [q < M]`;
* `window_dvd`: `∏_{n<p^a≤2n} p ∣ C(2n, n)`. For a prime `p` the only power that can lie in `(n, 2n]` is
  `p^e` with `e = v_p(lcm(1, …, 2n))` (the largest power `≤ 2n`), so the product is
  `Pw n = ∏_{p ≤ 2n} p^{[n < p^e]}`; when `n < p^e`, the Legendre term at `j = e − 1` is
  `⌊2n/p^e⌋ − 2⌊n/p^e⌋ ≥ 1` (`low_pt`, `binom_val_ge`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime pw_pos' lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (R fB f_zero f_one f_pos R_pos R_succ reconstruct subst_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu Inv lcm_valuation lcmu_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos val_mul val_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_le' dvd_self')
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_fact)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' qB'_at quo_small)
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact ltB inst2_ltB count_lt shift_le_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Divisibility from valuations -/

theorem one_pos' : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm

theorem f_dvd {i a b : PTm n} (h : Γ ⊢[PRAAx] isP i ≐ one ⟶ le (val i a) (val i b)) :
    Γ ⊢[PRAAx] dvd (pw i (isP i * val i a)) (pw i (isP i * val i b)) := by
  refine .orE (isP_01 i) ?_ ?_
  · exact (congrAp2 remF (f_zero Prf.hyp0) (f_zero Prf.hyp0)).eqTrans (dvd_self' one_pos')
  · exact (congrAp2 remF (f_one Prf.hyp0) (f_one Prf.hyp0)).eqTrans
      (Combinatorics.LegendreFact.pw_dvd_pw (p_pos (prime_two (prime_of_isP Prf.hyp0))) (Prf.impE h.wk Prf.hyp0))

/-- `∏_{p<N} p^{v_p(a)} ∣ ∏_{p<N} p^{v_p(b)}` when `v_p(a) ≤ v_p(b)` for every prime `p < N`. -/
theorem R_dvd {a b N : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ isP (var 0) ≐ one ⟶
      le (val (var 0) (Syn.shift a)) (val (var 0) (Syn.shift b)))) :
    Γ ⊢[PRAAx] dvd (R N a) (R N b) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      dvd (R (var 0) (Syn.shift a)) (R (var 0) (Syn.shift b))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_dvd, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI ((congrAp2 remF (prod_zero _ _) (prod_zero _ _)).eqTrans (dvd_self' one_pos'))
    · simp only [Fm.subst_imp, subst_le, subst_dvd, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let C : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) :: (le (var 0) (Syn.shift N) ⟶
          dvd (R (var 0) (Syn.shift a)) (R (var 0) (Syn.shift b))) :: Γ.map Fm.shift
      have hle : C ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : C ⊢[PRAAx] _) hle
      have hb : C ⊢[PRAAx] lt (var 0) (Syn.shift N) ⟶ isP (var 0) ≐ one ⟶
          le (val (var 0) (Syn.shift a)) (val (var 0) (Syn.shift b)) := h.allOpen.wk.wk
      have fd := f_dvd (Prf.impE hb Prf.hyp0)
      exact (congrAp2 remF (R_succ _ _) (R_succ _ _)).eqTrans (Smooth.dvd_mul_mul (R_pos _ _) (f_pos _ _) ih fd)
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_dvd, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-- If `1 ≤ a, b < N` and `v_p(a) ≤ v_p(b)` for every prime `p < N`, then `a ∣ b`. -/
theorem dvd_of_val_le {a b N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hla : Γ ⊢[PRAAx] lt a N) (hlb : Γ ⊢[PRAAx] lt b N)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ isP (var 0) ≐ one ⟶
      le (val (var 0) (Syn.shift a)) (val (var 0) (Syn.shift b)))) :
    Γ ⊢[PRAAx] dvd a b :=
  (congrAp2 remF (reconstruct hb hlb).eqSymm (reconstruct ha hla).eqSymm).eqTrans (R_dvd h)

/-! ## Doubling a floor -/

/-- `⌊2k/q⌋ = 2⌊k/q⌋` or `2⌊k/q⌋ + 1`. -/
theorem quo_two {q k : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) :
    Γ ⊢[PRAAx] (quo (two * k) q ≐ two * quo k q) ⋎ (quo (two * k) q ≐ succ (two * quo k q)) := by
  have rl := Multiplicative.rem_lt' hq k
  refine .orE (lt_or_le (two * rem k q) q) ?_ ?_
  · have dv := natEq (GcdFiber.div_eq (j := k) (hq.wk : (lt (two * rem k q) q :: Γ) ⊢[PRAAx] _))
    refine .orI₁ (Totient.quo_eq hq.wk (r := two * rem k q) ?_ Prf.hyp0)
    ipra_lc 2 * dv
  · let C : List (Fm PTm n) := le q (two * rem k q) :: Γ
    have dv := natEq (GcdFiber.div_eq (j := k) (hq.wk : C ⊢[PRAAx] _))
    have e1 := natEq ((eq_add_of_le rl.wk : C ⊢[PRAAx] q ≐ succ (rem k q) + monus q (succ (rem k q))))
    have e2 := natEq ((eq_add_of_le Prf.hyp0 : C ⊢[PRAAx] two * rem k q ≐ q + monus (two * rem k q) q))
    have hr : C ⊢[PRAAx] lt (monus (two * rem k q) q) q :=
      le_of_eq_add (d := succ (monus q (succ (rem k q)) + monus q (succ (rem k q))))
        (by apply deriveNat; ipra_simps; linear_combination 2 * e1 + e2)
    refine .orI₂ (Totient.quo_eq hq.wk (r := monus (two * rem k q) q) ?_ hr)
    ipra_lc 2 * dv + e2

/-! ## Legendre's formula for `C(2k, k)` -/

/-- `⌊k/p^{j+1}⌋ = 0` for `j ≥ k`. -/
theorem qz {p k j : PTm n} (hp2 : Γ ⊢[PRAAx] le two p) (hj : Γ ⊢[PRAAx] le k j) :
    Γ ⊢[PRAAx] quo k (pw p (succ j)) ≐ zero :=
  quo_small (pw_pos' (p_pos hp2) _) (le_trans ((succ_monus_succ k j).eqTrans hj) (le_of_lt (lt_pw hp2 (succ j))))

theorem binom_val {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (k : PTm n) :
    Γ ⊢[PRAAx] val p (cb k) + two * ap2 (sumF qB') (two * k) (pairT p k) ≐
      ap2 (sumF qB') (two * k) (pairT p (two * k)) := by
  have hp2 := prime_two hp
  have fk := Primes.fact_pos (Γ := Γ) k
  have cpos := BinomialThree.pos_of_one_le (Combinatorics.CentralBinomial.central_pos (Γ := Γ) k)
  have e1 := natEq ((val_congr p (cb_fact (Γ := Γ) k)).eqTrans ((val_mul hp (Combinatorics.Binomial.pos_mul fk fk) cpos).eqTrans
    (congrAdd (val_mul hp fk fk) (.eqRefl _))))
  have f2 := natEq (legendre_fact (Γ := Γ) hp (two * k))
  have f1 := natEq (legendre_fact (Γ := Γ) hp k)
  have s1 := natEq (sum_succ' (Γ := Γ) qB' (two * k) (pairT p k))
  have z1 := natEq ((qB'_at (Γ := Γ) (two * k) p k).eqTrans (qz hp2 (le_of_eq_add (d := k) (by ipra_ring))))
  have s2 := natEq (sum_ext (Γ := Γ) qB' (B := k) (N := succ (two * k)) (x := pairT p k) (fun Δ a hs hl => by
    rw [shift_pairT]
    exact (qB'_at _ _ _).eqTrans (qz ((shift_le_two hp2).weaken hs) (le_of_lt hl)))
    ((succ_monus_succ _ _).eqTrans (le_of_eq_add (d := k) (by ipra_ring))))
  have s3 := natEq (sum_succ' (Γ := Γ) qB' k (pairT p k))
  have z3 := natEq ((qB'_at (Γ := Γ) k p k).eqTrans (qz hp2 (le_refl k)))
  apply deriveNat; ipra_simps
  linear_combination -e1 + f2 - 2 * f1 + 2 * (-s1 + s2 + s3 - z1 + z3)

/-! ## The upper valuation bound -/

/-- `⌊2k/p^{j+1}⌋`, over `0 = j`, `1 = ⟨⟨p, k⟩, e⟩`. -/
abbrev hB : PTm 2 := quo (two * sndT (fstT (var 1))) (pw (fstT (fstT (var 1))) (succ (var 0)))
/-- `2⌊k/p^{j+1}⌋ + [j < e]`. -/
abbrev gB : PTm 2 := two * quo (sndT (fstT (var 1))) (pw (fstT (fstT (var 1))) (succ (var 0))) +
  sg (monus (sndT (var 1)) (var 0))
/-- `2⌊k/p^{j+1}⌋`, over `0 = j`, `1 = ⟨p, k⟩`. -/
abbrev tB : PTm 2 := two * qB'

theorem pr_fst {p k e : PTm n} : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT p k) e)) ≐ p :=
  (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
theorem pr_snd {p k e : PTm n} : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT p k) e)) ≐ k :=
  (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)

theorem hB_at (j p k e : PTm n) :
    Γ ⊢[PRAAx] inst2 hB j (pairT (pairT p k) e) ≐ quo (two * k) (pw p (succ j)) := by
  have h : inst2 hB j (pairT (pairT p k) e) =
      quo (two * sndT (fstT (pairT (pairT p k) e))) (pw (fstT (fstT (pairT (pairT p k) e))) (succ j)) := by
    simp [inst2]
  rw [h]
  exact congrAp2 quoF (congrMul (.eqRefl _) pr_snd) (Combinatorics.BinomialTheorem.congrPw pr_fst (.eqRefl _))

theorem gB_at (j p k e : PTm n) :
    Γ ⊢[PRAAx] inst2 gB j (pairT (pairT p k) e) ≐ two * quo k (pw p (succ j)) + sg (monus e j) := by
  have h : inst2 gB j (pairT (pairT p k) e) =
      two * quo (sndT (fstT (pairT (pairT p k) e))) (pw (fstT (fstT (pairT (pairT p k) e))) (succ j)) +
        sg (monus (sndT (pairT (pairT p k) e)) j) := by
    simp [inst2]
  rw [h]
  exact congrAdd (congrMul (.eqRefl _) (congrAp2 quoF pr_snd (Combinatorics.BinomialTheorem.congrPw pr_fst (.eqRefl _))))
    (congrSg (congrMonus (snd_pair _ _) (.eqRefl _)))

theorem inst2_tB (j x : PTm n) : inst2 tB j x = two * inst2 qB' j x := by simp [inst2]

/-- The termwise bound `⌊2k/p^{j+1}⌋ ≤ 2⌊k/p^{j+1}⌋ + [j < e]` for `e = v_p(lcm(1, …, 2k))`. -/
theorem term_le {p k j : PTm n} (hp2 : Γ ⊢[PRAAx] le two p) (hI2 : Γ ⊢[PRAAx] lt (two * k) (pw p (succ (val p (lcmu (two * k)))))) :
    Γ ⊢[PRAAx] le (quo (two * k) (pw p (succ j))) (two * quo k (pw p (succ j)) + sg (monus (val p (lcmu (two * k))) j)) := by
  have qpos := pw_pos' (p_pos hp2) (succ j)
  refine .orE (lt_or_le j (val p (lcmu (two * k)))) ?_ ?_
  · refine le_congr (.eqRefl _) (congrAdd (.eqRefl _) (sg_lt Prf.hyp0)).eqSymm ?_
    exact .orE (quo_two qpos.wk)
      (le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_of_eq_add (d := one) (.eqRefl _)))
      (le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_of_eq_add (d := zero) (by ipra_ring)))
  · have big : (le (val p (lcmu (two * k))) j :: Γ) ⊢[PRAAx] lt (two * k) (pw p (succ j)) :=
      le_trans hI2.wk (PowerCleared.pw_le_exp (p_pos hp2).wk ((succ_monus_succ _ _).eqTrans Prf.hyp0))
    exact le_congr (quo_small qpos.wk big).eqSymm (.eqRefl _) (zero_le _)

/-- `v_p(lcm(1, …, 2k)) ≤ 2k`. -/
theorem e_le {p k : PTm n} (hp2 : Γ ⊢[PRAAx] le two p)
    (hI1 : Γ ⊢[PRAAx] le (sg (val p (lcmu (two * k))) * pw p (val p (lcmu (two * k)))) (two * k)) :
    Γ ⊢[PRAAx] le (val p (lcmu (two * k))) (two * k) := by
  refine .orE (zero_or_succ (val p (lcmu (two * k)))) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)) ?_
  have s : ((val p (lcmu (two * k)) ≐ succ (pred (val p (lcmu (two * k))))) :: Γ) ⊢[PRAAx]
      sg (val p (lcmu (two * k))) ≐ one := (congrSg Prf.hyp0).eqTrans (sg_succ _)
  have pe := le_congr ((congrMul s (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) hI1.wk
  exact le_trans (le_of_lt (lt_pw hp2.wk _)) pe

/-- `v_p(C(2k, k)) ≤ v_p(lcm(1, …, 2k))`. -/
theorem binom_val_le {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (k : PTm n) :
    Γ ⊢[PRAAx] le (val p (cb k)) (val p (lcmu (two * k))) := by
  have hp2 := prime_two hp
  have I := lcm_valuation hp (two * k)
  have I1 := Prf.andE₁ I; have I2 := Prf.andE₂ I
  have hp2' := shift_le_two hp2
  have hs : Syn.shift (val p (lcmu (two * k))) = val (Syn.shift p) (lcmu (two * Syn.shift k)) := by simp [Syn.shift]
  have I2' : Γ.map Fm.shift ⊢[PRAAx] lt (two * Syn.shift k) (pw (Syn.shift p) (succ (val (Syn.shift p) (lcmu (two * Syn.shift k))))) := by
    have e := I2.shift
    simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e
    simpa [Syn.shift] using e
  -- `∑ ⌊2k/q⌋ ≤ ∑ (2⌊k/q⌋ + [j < e])`
  have sl := Analysis.PowerSums.sum_le (Γ := Γ) hB gB (pairT (pairT p k) (val p (lcmu (two * k)))) (two * k)
    (.allI (.impI (by
      rw [shift_pairT, shift_pairT, hs]
      exact le_congr (hB_at _ _ _ _).eqSymm (gB_at _ _ _ _).eqSymm (term_le hp2'.wk I2'.wk))))
  have cH : Γ ⊢[PRAAx] ap2 (sumF hB) (two * k) (pairT (pairT p k) (val p (lcmu (two * k)))) ≐
      ap2 (sumF qB') (two * k) (pairT p (two * k)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT, shift_pairT]
    refine (hB_at _ _ _ _).eqTrans (.eqTrans ?_ (qB'_at _ _ _).eqSymm)
    have e2 : Syn.shift (two * k) = two * Syn.shift k := by simp [Syn.shift]
    rw [e2]; exact .eqRefl _
  have cG : Γ ⊢[PRAAx] ap2 (sumF gB) (two * k) (pairT (pairT p k) (val p (lcmu (two * k)))) ≐
      ap2 (sumF tB) (two * k) (pairT p k) + ap2 (sumF ltB) (two * k) (val p (lcmu (two * k))) := by
    refine LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda.sum_add2 _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT, inst2_tB, inst2_ltB]
    refine (gB_at _ _ _ _).eqTrans (congrAdd (congrMul (.eqRefl _) (qB'_at _ _ _).eqSymm) (.eqRefl _))
  have cT : Γ ⊢[PRAAx] ap2 (sumF tB) (two * k) (pairT p k) ≐ two * ap2 (sumF qB') (two * k) (pairT p k) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_tB]
    have e2 : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
    rw [e2]; exact .eqRefl _
  have cL := count_lt (Γ := Γ) (e_le hp2 I1)
  have u := natEq cH; have v := natEq cG; have t := natEq cT; have l := natEq cL
  refine le_of_add_le_add_right (c := two * ap2 (sumF qB') (two * k) (pairT p k)) ?_
  refine le_congr ?_ ?_ sl
  · ipra_lc u - natEq (binom_val hp k)
  · ipra_lc v + t + l

/-- `thm:binomial-lcm`, right divisibility: `C(2k, k) ∣ lcm(1, …, 2k)`. -/
theorem central_dvd_lcm (k : PTm n) : Γ ⊢[PRAAx] dvd (cb k) (lcmu (two * k)) := by
  have cpos := BinomialThree.pos_of_one_le (Combinatorics.CentralBinomial.central_pos (Γ := Γ) k)
  have lpos := lcmu_pos (Γ := Γ) (two * k)
  have hs1 : Syn.shift (cb k) = cb (Syn.shift k) := by simp [Syn.shift]
  have hs2 : Syn.shift (lcmu (two * k)) = lcmu (two * Syn.shift k) := by simp [Syn.shift]
  refine dvd_of_val_le (N := succ (cb k + lcmu (two * k))) cpos lpos
    ((succ_monus_succ _ _).eqTrans (le_add_right _ _)) ((succ_monus_succ _ _).eqTrans (le_add_left _ _))
    (.allI (.impI (.impI ?_)))
  rw [hs1, hs2]
  exact binom_val_le (prime_of_isP Prf.hyp0) _

/-! ## The prime product of the window `(n, 2n]` -/

section Window

open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrIsP congrVal zero_mul_l congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.PrimePowerMangoldt (val_pw_prime)

/-- `[i prime] E(i, x)`, over `0 = i`, `1 = x`. -/
abbrev XE (E : PTm 2) : PTm 2 := isP (var 0) * E
/-- `i^{[i prime] E(i, x)}`. -/
abbrev PE (E : PTm 2) : PTm 2 := pw (var 0) (XE E)

theorem inst2_XE (E : PTm 2) (i x : PTm n) : inst2 (XE E) i x = isP i * inst2 E i x := by
  simp only [inst2, XE, PTm.subst_mul, FactorVector.subst_isP]
  simp
theorem inst2_PE (E : PTm 2) (i x : PTm n) : inst2 (PE E) i x = pw i (inst2 (XE E) i x) := by
  simp [inst2]

theorem PE_pos (E : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (PE E)) M x ≐ succ (pred (ap2 (prodF (PE E)) M x)) :=
  prod_pos_bounded _ _ _ (.allI (.impI (by rw [inst2_PE, inst2_XE]; exact f_pos _ _)))

/-- `v_q(i^{[i prime] e}) = [i prime] e [i = q]` for a prime `q`. -/
theorem vf_at {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (i e : PTm n) :
    Γ ⊢[PRAAx] val q (pw i (isP i * e)) ≐ (isP i * e) * eqb i q := by
  refine .orE (isP_01 i) ?_ ?_
  · exact ((congrVal (.eqRefl _) (f_zero Prf.hyp0)).eqTrans (ValuationMul.val_one (prime_two hq).wk)).eqTrans
      (zero_mul_l (zero_mul_l Prf.hyp0 _) _).eqSymm
  · refine ((congrVal (.eqRefl _) (f_one Prf.hyp0)).eqTrans (val_pw_prime hq.wk (prime_of_isP Prf.hyp0) e)).eqTrans ?_
    exact (congrMul ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)).eqSymm

/-- `v_q(∏_{i<M} i^{[i prime] E(i)}) = [q prime] E(q) [q < M]`. -/
abbrev vpF (E : PTm 2) (q x M : PTm n) : Fm PTm n :=
  val q (ap2 (prodF (PE E)) M x) ≐ inst2 (XE E) q x * sg (monus M q)

theorem subst_vpF {m : ℕ} (E : PTm 2) (σ : Fin n → PTm m) (q x M : PTm n) :
    (vpF E q x M).subst σ = vpF E (Syn.subst σ q) (Syn.subst σ x) (Syn.subst σ M) := by
  simp [vpF, FactorVector.subst_val]

/-- `v_q(∏_{i<M} i^{[i prime] E(i)}) = [q prime] E(q) [q < M]` for a prime `q`. -/
theorem val_PE {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (E : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] val q (ap2 (prodF (PE E)) M x) ≐ inst2 (XE E) q x * sg (monus M q) := by
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] prime (Syn.shift q) := by simpa [Fm.shift, Syn.shift] using hq.shift
  have hall : Γ ⊢[PRAAx] Fm.all (vpF E (Syn.shift q) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · rw [subst_vpF]
      simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine ((congrVal (.eqRefl _) (prod_zero _ _)).eqTrans (ValuationMul.val_one (prime_two hq))).eqTrans ?_
      exact ((congrMul (.eqRefl _) ((congrSg (zero_monus _)).eqTrans sg_zero)).eqTrans (mul_zero _)).eqSymm
    · rw [subst_vpF]
      simp only [Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ, vpF]
      let D : List (Fm PTm (n + 1)) := (val (Syn.shift q) (ap2 (prodF (PE E)) (var 0) (Syn.shift x)) ≐
        inst2 (XE E) (Syn.shift q) (Syn.shift x) * sg (monus (var 0) (Syn.shift q))) :: Γ.map Fm.shift
      have hqD : D ⊢[PRAAx] prime (Syn.shift q) := hq'.wk
      have pv := Probability.ProductReplacement.prod_succ' (Γ := D) (PE E) (var 0) (Syn.shift x)
      rw [inst2_PE, inst2_XE] at pv
      have vm := (congrVal (.eqRefl _) pv).eqTrans (val_mul hqD (PE_pos _ _ _) (f_pos _ _))
      have vf := vf_at hqD (var 0) (inst2 E (var 0) (Syn.shift x))
      have ih : D ⊢[PRAAx] _ := Prf.hyp0
      have xq : D ⊢[PRAAx] inst2 (XE E) (Syn.shift q) (Syn.shift x) ≐ isP (Syn.shift q) * inst2 E (Syn.shift q) (Syn.shift x) := by
        rw [inst2_XE]; exact .eqRefl _
      refine vm.eqTrans ((congrAdd ih vf).eqTrans ?_)
      refine (congrAdd (congrMul xq (.eqRefl _)) (.eqRefl _)).eqTrans (.eqTrans ?_ (congrMul xq (.eqRefl _)).eqSymm)
      refine .orE (eq_or_ne (var 0) (Syn.shift q)) ?_ ?_
      · let C : List (Fm PTm (n + 1)) := (var 0 ≐ Syn.shift q) :: D
        have h : C ⊢[PRAAx] var 0 ≐ Syn.shift q := Prf.hyp0
        have s0 : C ⊢[PRAAx] sg (monus (var 0) (Syn.shift q)) ≐ zero :=
          (congrSg ((congrMonus h (.eqRefl _)).eqTrans (monus_self _))).eqTrans sg_zero
        have eb : C ⊢[PRAAx] eqb (var 0) (Syn.shift q) ≐ one := eqb_of_eq h
        have s1 : C ⊢[PRAAx] sg (monus (succ (var 0)) (Syn.shift q)) ≐ one :=
          sg_lt ((succ_monus_succ _ _).eqTrans (le_congr h (.eqRefl _) (le_refl _)))
        have hB : C ⊢[PRAAx] isP (var 0) * inst2 E (var 0) (Syn.shift x) ≐
            isP (Syn.shift q) * inst2 E (Syn.shift q) (Syn.shift x) :=
          congrMul (congrIsP h) (congrInst2 E h (.eqRefl _))
        refine (congrAdd (congrMul (.eqRefl _) s0) (congrMul hB eb)).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) s1).eqSymm)
        ipra_ring
      · let C : List (Fm PTm (n + 1)) := neg (var 0 ≐ Syn.shift q) :: D
        have ne : C ⊢[PRAAx] neg (var 0 ≐ Syn.shift q) := Prf.hyp0
        have ss : C ⊢[PRAAx] sg (monus (var 0) (Syn.shift q)) ≐ sg (monus (succ (var 0)) (Syn.shift q)) := by
          refine .orE (lt_or_le (Syn.shift q) (var 0)) ?_ ?_
          · exact (sg_lt Prf.hyp0).eqTrans (sg_lt (le_trans Prf.hyp0 (le_succ_self _))).eqSymm
          · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
            · exact (sg_le (le_of_lt Prf.hyp0)).eqTrans (sg_le Prf.hyp0).eqSymm
            · exact .botE _ (Prf.impE ne.wk.wk Prf.hyp0)
        exact (congrAdd (.eqRefl _) ((congrMul (.eqRefl _) (eqb_of_ne ne)).eqTrans (mul_zero _))).eqTrans
          ((add_zero _).eqTrans (congrMul (.eqRefl _) ss))
  have h2 := Prf.allE M hall
  rw [subst_vpF] at h2
  simp only [Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact h2

/-- `[k < i^{v_i(lcm(1, …, 2k))}]`, over `0 = i`, `1 = k`: the only power of `i` that can lie in
`(k, 2k]` is `i^{v_i(lcm(1, …, 2k))}`, the largest one `≤ 2k`. -/
abbrev cB : PTm 2 := sg (monus (pw (var 0) (val (var 0) (lcmu (two * var 1)))) (var 1))

theorem inst2_cB (i k : PTm n) : inst2 cB i k = sg (monus (pw i (val i (lcmu (two * k)))) k) := by
  simp [inst2, FactorVector.subst_val]

/-- `∏_{n < p^a ≤ 2n} p = ∏_{p ≤ 2n prime} p^{[n < p^{e_p}]}` with `e_p = v_p(lcm(1, …, 2n))`. -/
abbrev Pw (k : PTm n) : PTm n := ap2 (prodF (PE cB)) (succ (two * k)) k

/-- `2⌊k/q⌋ + [c = j]`, over `0 = j`, `1 = ⟨⟨q, k⟩, c⟩`. -/
abbrev g2B : PTm 2 := two * quo (sndT (fstT (var 1))) (pw (fstT (fstT (var 1))) (succ (var 0))) +
  eqb (sndT (var 1)) (var 0)

theorem g2B_at (j p k c : PTm n) :
    Γ ⊢[PRAAx] inst2 g2B j (pairT (pairT p k) c) ≐ two * quo k (pw p (succ j)) + eqb c j := by
  have h : inst2 g2B j (pairT (pairT p k) c) =
      two * quo (sndT (fstT (pairT (pairT p k) c))) (pw (fstT (fstT (pairT (pairT p k) c))) (succ j)) +
        eqb (sndT (pairT (pairT p k) c)) j := by
    simp [inst2]
  rw [h]
  exact congrAdd (congrMul (.eqRefl _) (congrAp2 quoF pr_snd (Combinatorics.BinomialTheorem.congrPw pr_fst (.eqRefl _))))
    (congrEqb' (snd_pair _ _) (.eqRefl _))

/-- The pointwise lower bound `2⌊k/q^{j+1}⌋ + [V − 1 = j] ≤ ⌊2k/q^{j+1}⌋` when `k < q^V ≤ 2k`, `V ≥ 1`. -/
theorem low_pt {q k j V : PTm n} (hq2 : Γ ⊢[PRAAx] le two q) (ep : Γ ⊢[PRAAx] V ≐ succ (pred V))
    (hk : Γ ⊢[PRAAx] lt k (pw q V)) (pe : Γ ⊢[PRAAx] le (pw q V) (two * k)) :
    Γ ⊢[PRAAx] le (two * quo k (pw q (succ j)) + eqb (pred V) j) (quo (two * k) (pw q (succ j))) := by
  have qV := pw_pos' (p_pos hq2) V
  have qj := pw_pos' (p_pos hq2) (succ j)
  refine .orE (eq_or_ne (pred V) j) ?_ ?_
  · let C : List (Fm PTm n) := (pred V ≐ j) :: Γ
    have hj : C ⊢[PRAAx] pred V ≐ j := Prf.hyp0
    have ej : C ⊢[PRAAx] pw q (succ j) ≐ pw q V :=
      Combinatorics.BinomialTheorem.congrPw (.eqRefl _) ((congrSucc hj.eqSymm).eqTrans ep.wk.eqSymm)
    have a0 : C ⊢[PRAAx] quo k (pw q (succ j)) ≐ zero :=
      (congrAp2 quoF (.eqRefl _) ej).eqTrans (quo_small qV.wk hk.wk)
    have t1 : C ⊢[PRAAx] le one (quo (two * k) (pw q (succ j))) :=
      le_congr (.eqRefl _) (congrAp2 quoF (.eqRefl _) ej).eqSymm
        (SumReindex.le_quo_of_mul_le qV.wk (le_congr (EulerDomination.mul_one' _).eqSymm (.eqRefl _) pe.wk))
    exact le_congr ((congrAdd ((congrMul (.eqRefl _) a0).eqTrans (mul_zero _)) (eqb_of_eq hj)).eqTrans (zero_add _)).eqSymm
      (.eqRefl _) t1
  · let C : List (Fm PTm n) := neg (pred V ≐ j) :: Γ
    have hj : C ⊢[PRAAx] neg (pred V ≐ j) := Prf.hyp0
    exact le_congr ((congrAdd (.eqRefl _) (eqb_of_ne hj)).eqTrans (add_zero _)).eqSymm (.eqRefl _)
      (.orE (quo_two qj.wk) (le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_refl _))
        (le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_succ_self _)))

/-- `[k < q^e] ≤ v_q(C(2k, k))` for a prime `q ≤ 2k`, `e = v_q(lcm(1, …, 2k))`: at `j = e − 1` the
term `⌊2k/q^e⌋ − 2⌊k/q^e⌋` is at least one. -/
theorem binom_val_ge {q k : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hqk : Γ ⊢[PRAAx] le q (two * k)) :
    Γ ⊢[PRAAx] le (sg (monus (pw q (val q (lcmu (two * k)))) k)) (val q (cb k)) := by
  have hq2 := prime_two hq
  have qpos := p_pos hq2
  have I := lcm_valuation hq (two * k)
  have I1 := Prf.andE₁ I; have I2 := Prf.andE₂ I
  refine .orE (lt_or_le k (pw q (val q (lcmu (two * k))))) ?_ ?_
  swap
  · exact le_congr (sg_le Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  let C : List (Fm PTm n) := lt k (pw q (val q (lcmu (two * k)))) :: Γ
  have hk : C ⊢[PRAAx] lt k (pw q (val q (lcmu (two * k)))) := Prf.hyp0
  -- `e ≥ 1`, since `q ≤ 2k < q^{e+1}`
  have epos : C ⊢[PRAAx] val q (lcmu (two * k)) ≐ succ (pred (val q (lcmu (two * k)))) := by
    refine .orE (zero_or_succ (val q (lcmu (two * k)))) ?_ Prf.hyp0
    have c1 : ((val q (lcmu (two * k)) ≐ zero) :: C) ⊢[PRAAx] lt (two * k) q :=
      lt_congr (.eqRefl _) ((Combinatorics.BinomialTheorem.congrPw (.eqRefl _) (congrSucc Prf.hyp0)).eqTrans (pw_one _)) I2.wk.wk
    exact le_lt_absurd _ hqk.wk.wk c1
  have se : C ⊢[PRAAx] sg (val q (lcmu (two * k))) ≐ one := (congrSg epos).eqTrans (sg_succ _)
  have pe : C ⊢[PRAAx] le (pw q (val q (lcmu (two * k)))) (two * k) :=
    le_congr ((congrMul se (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) I1.wk
  have eL := e_le (Γ := C) hq2.wk I1.wk
  have hp2' := shift_le_two hq2
  let x : PTm n := pairT (pairT q k) (pred (val q (lcmu (two * k))))
  have hsx : Syn.shift x = pairT (pairT (Syn.shift q) (Syn.shift k)) (pred (val (Syn.shift q) (lcmu (two * Syn.shift k)))) := by
    simp [x, Syn.shift]
  have hsS : Syn.shift (two * k) = two * Syn.shift k := by simp [Syn.shift]
  -- the shifted facts used pointwise
  have hk' : C.map Fm.shift ⊢[PRAAx] lt (Syn.shift k) (pw (Syn.shift q) (val (Syn.shift q) (lcmu (two * Syn.shift k)))) := by
    have e := hk.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  have pe' : C.map Fm.shift ⊢[PRAAx] le (pw (Syn.shift q) (val (Syn.shift q) (lcmu (two * Syn.shift k)))) (two * Syn.shift k) := by
    have e := pe.shift; simp only [Fm.shift, subst_le] at e; simpa [Syn.shift] using e
  have ep' := MobiusBounds.shift_pos epos
  rw [show Syn.shift (val q (lcmu (two * k))) = val (Syn.shift q) (lcmu (two * Syn.shift k)) by simp [Syn.shift]] at ep'
  have qpos' : C.map Fm.shift ⊢[PRAAx] pw (Syn.shift q) (val (Syn.shift q) (lcmu (two * Syn.shift k))) ≐
      succ (pred (pw (Syn.shift q) (val (Syn.shift q) (lcmu (two * Syn.shift k))))) :=
    pw_pos' (p_pos hp2'.wk) _
  -- `∑ (2⌊k/q^{j+1}⌋ + [e − 1 = j]) ≤ ∑ ⌊2k/q^{j+1}⌋`
  have sl := Analysis.PowerSums.sum_le (Γ := C) g2B hB x (two * k) (.allI (.impI (by
    rw [hsx, hsS]
    exact le_congr (g2B_at _ _ _ _).eqSymm (hB_at _ _ _ _).eqSymm
      (low_pt hp2'.wk.wk ep'.wk hk'.wk pe'.wk))))
  -- identify the two sums
  have cH : C ⊢[PRAAx] ap2 (sumF hB) (two * k) x ≐ ap2 (sumF qB') (two * k) (pairT q (two * k)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [hsx, shift_pairT, hsS]
    exact (hB_at _ _ _ _).eqTrans (qB'_at _ _ _).eqSymm
  have cG : C ⊢[PRAAx] ap2 (sumF g2B) (two * k) x ≐
      ap2 (sumF tB) (two * k) (pairT q k) + ap2 (sumF (dB (one : PTm 2))) (two * k)
        (pairT (pred (val q (lcmu (two * k)))) zero) := by
    refine LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda.sum_add2 _ _ _ (.allI (.impI ?_))
    rw [hsx, shift_pairT, shift_pairT, inst2_tB, inst2_dB, Combinatorics.LegendreFact.inst2_one2]
    have hz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
    have hv : Syn.shift (pred (val q (lcmu (two * k)))) = pred (val (Syn.shift q) (lcmu (two * Syn.shift k))) := by
      simp [Syn.shift]
    rw [hz, hv]
    refine (g2B_at _ _ _ _).eqTrans (congrAdd (congrMul (.eqRefl _) (qB'_at _ _ _).eqSymm) ?_)
    exact (EulerDomination.mul_one' _).eqSymm.eqTrans (congrMul (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _))
  have cT : C ⊢[PRAAx] ap2 (sumF tB) (two * k) (pairT q k) ≐ two * ap2 (sumF qB') (two * k) (pairT q k) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_tB]
    have e2 : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
    rw [e2]; exact .eqRefl _
  have cD : C ⊢[PRAAx] ap2 (sumF (dB (one : PTm 2))) (two * k) (pairT (pred (val q (lcmu (two * k)))) zero) ≐ one := by
    refine (sum_delta (one : PTm 2) (le_congr epos (.eqRefl _) eL)).eqTrans ?_
    rw [Combinatorics.LegendreFact.inst2_one2]; exact .eqRefl _
  have u := natEq cH; have v := natEq cG; have t := natEq cT; have d := natEq cD
  have v1 : C ⊢[PRAAx] le one (val q (cb k)) := by
    refine le_of_add_le_add_right (c := two * ap2 (sumF qB') (two * k) (pairT q k)) ?_
    refine le_congr ?_ ?_ sl
    · ipra_lc v + t + d
    · ipra_lc u - natEq (binom_val (Γ := C) hq.wk k)
  exact le_congr (sg_lt hk).eqSymm (.eqRefl _) v1

/-- `thm:binomial-lcm`, left divisibility: `∏_{n < p^a ≤ 2n} p ∣ C(2n, n)`. -/
theorem window_dvd (k : PTm n) : Γ ⊢[PRAAx] dvd (Pw k) (cb k) := by
  have Ppos := PE_pos (Γ := Γ) cB (succ (two * k)) k
  have cpos := BinomialThree.pos_of_one_le (Combinatorics.CentralBinomial.central_pos (Γ := Γ) k)
  have hs1 : Syn.shift (Pw k) = Pw (Syn.shift k) := by simp [Syn.shift]
  have hs2 : Syn.shift (cb k) = cb (Syn.shift k) := by simp [Syn.shift]
  refine dvd_of_val_le (N := succ (Pw k + cb k)) Ppos cpos
    ((succ_monus_succ _ _).eqTrans (le_add_right _ _)) ((succ_monus_succ _ _).eqTrans (le_add_left _ _))
    (.allI (.impI (.impI ?_)))
  rw [hs1, hs2]
  let Q : List (Fm PTm (n + 1)) :=
    (isP (var 0) ≐ one) :: lt (var 0) (Syn.shift (succ (Pw k + cb k))) :: Γ.map Fm.shift
  have h1 : Q ⊢[PRAAx] isP (var 0) ≐ one := Prf.hyp0
  have hv : Q ⊢[PRAAx] prime (var 0) := prime_of_isP h1
  have vp := val_PE hv cB (succ (two * Syn.shift k)) (Syn.shift k)
  rw [inst2_XE, inst2_cB] at vp
  refine .orE (lt_or_le (var 0) (succ (two * Syn.shift k))) ?_ ?_
  · let Q1 : List (Fm PTm (n + 1)) := lt (var 0) (succ (two * Syn.shift k)) :: Q
    have hl : Q1 ⊢[PRAAx] lt (var 0) (succ (two * Syn.shift k)) := Prf.hyp0
    have hvk : Q1 ⊢[PRAAx] le (var 0) (two * Syn.shift k) := (succ_monus_succ _ _).eqSymm.eqTrans hl
    have e : Q1 ⊢[PRAAx] val (var 0) (Pw (Syn.shift k)) ≐
        sg (monus (pw (var 0) (val (var 0) (lcmu (two * Syn.shift k)))) (Syn.shift k)) :=
      vp.wk.eqTrans ((congrMul (.eqRefl _) (sg_lt hl)).eqTrans ((EulerDomination.mul_one' _).eqTrans
        ((congrMul h1.wk (.eqRefl _)).eqTrans (one_mul _))))
    exact le_congr e.eqSymm (.eqRefl _) (binom_val_ge hv.wk hvk)
  · let Q2 : List (Fm PTm (n + 1)) := le (succ (two * Syn.shift k)) (var 0) :: Q
    have hl : Q2 ⊢[PRAAx] le (succ (two * Syn.shift k)) (var 0) := Prf.hyp0
    exact le_congr (vp.wk.eqTrans ((congrMul (.eqRefl _) (sg_le hl)).eqTrans (mul_zero _))).eqSymm (.eqRefl _) (zero_le _)

/-- `thm:binomial-lcm`: `∏_{n < p^a ≤ 2n} p ∣ C(2n, n) ∣ lcm(1, …, 2n)`. -/
theorem binomial_lcm (k : PTm n) : Γ ⊢[PRAAx] dvd (Pw k) (cb k) ⋏ dvd (cb k) (lcmu (two * k)) :=
  .andI (window_dvd k) (central_dvd_lcm k)

end Window

end LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm
