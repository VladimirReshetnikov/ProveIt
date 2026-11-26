import IPRADerivations.AnalyticNumberTheory.PrimorialLower
import IPRADerivations.AnalyticNumberTheory.PrimeRank
import IPRADerivations.AnalyticNumberTheory.WeightedMangoldt
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# An integer Chebyshev lower bound for the prime count

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/growth.tex`, Proposition "Integer Chebyshev
bounds", the lower half: "`L_n ≤ n^{π(n)}` ... the latter bound using the largest power of each prime separately".

With `L_P = lcm(1, …, P)` (`LcmUpto.lcmu`) and `π = PrimeRank.pc`:

* `val_full`: for a prime `q`, `v_q(L_P) ≤ [q prime] v_q(L_P) [q ≤ P]`, since `q^v ≤ P` forces `q ≤ P`;
* `lcm_dvd_full`: `L_P ∣ ∏_{i ≤ P} i^{[i prime] v_i(L_P)}`, by comparing valuations (`BinomialLcm.dvd_of_val_le`);
* `factor_le_pw`: each factor is at most `P^{[i prime]}`, for `P ≥ 1`;
* `prod_le_pi`: `∏_{i ≤ j} i^{[i prime] v_i(L_P)} ≤ P^{π(j)}`, by induction on `j`;
* **`lcm_le_pi`**: `L_P ≤ P^{π(P)}` for `P ≥ 1`;
* **`cheb_lower`**: `2^{P−1} ≤ (P + 1) · P^{π(P)}` for `P ≥ 1`, that is
  `π(P) log P ≥ (P − 1) log 2 − log(P + 1)`, from `PrimorialLower.two_pow_lcm`;
* `exp_le_of_pw_le`: `2^a ≤ 2^b` gives `a ≤ b`;
* **`cheb_lower_log`**: for `1 ≤ P < 2^{b+1}`, `P − 1 ≤ (b + 1)(π(P) + 1)`: the prime count is at least of the
  order `P / log₂ P`, with the binary length `b + 1` of `P` in place of the logarithm (the packet states this
  half as `⌊n/2⌋ ≤ (b + 1) π(n)`);
* `cb_succ_ge`, `cb_lower`: `2 C(2k, k) ≤ C(2k + 2, k + 1)` (from `Catalan.cat_telescope`) and `2^k ≤ C(2k, k)`;
* **`cb_le_pi`**: `C(2m, m) ≤ (2m)^{π(2m)}` for `m ≥ 1`
  (`number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, `an:binomial`, second inequality);
* **`cheb_dyadic_lower`**: `2^k ≤ (k + 1) π(2^{k+1})` for every `k`, the lower bound `2^{K−1} ≤ K π(2^K)` of
  `an:chebyshev` in the same packet (there for `K ≥ 3`; here for every `K ≥ 1`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevPi

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (f_zero f_one one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu lcmu_pos lcm_valuation)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (dvd_of_val_le PE XE val_PE inst2_XE inst2_PE PE_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower (vB inst2_vB Sm factor_le two_pow_lcm)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc pc_zero pc_succ congrPc)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (central_dvd_lcm)
open LeanProofs.IPRA.Combinatorics.Catalan (cb cat cb_zero cat_spec cat_telescope)
open LeanProofs.IPRA.Combinatorics.CentralBinomial (central_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le')
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The prime powers of `lcm(1, …, P)` -/

theorem alg_full {I V S : PTm n} (i : Γ ⊢[PRAAx] I ≐ one) (s : Γ ⊢[PRAAx] S ≐ one) :
    Γ ⊢[PRAAx] I * V * S ≐ V + zero := by
  ipra_lc 𝔞 V * 𝔞 S * natEq i + 𝔞 V * natEq s

/-- For a prime `q`: `v_q(L_P) ≤ [q prime] v_q(L_P) [q ≤ P]`. -/
theorem val_full {q P : PTm n} (hq : Γ ⊢[PRAAx] prime q) :
    Γ ⊢[PRAAx] le (val q (lcmu P)) (isP q * val q (lcmu P) * sg (monus (succ P) q)) := by
  have qpos := p_pos (prime_two hq)
  have ip := isP_of_prime hq
  have A1 := Prf.andE₁ (lcm_valuation hq P)
  refine .orE (zero_or_succ (val q (lcmu P))) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)) ?_
  let C : List (Fm PTm n) := (val q (lcmu P) ≐ succ (pred (val q (lcmu P)))) :: Γ
  have Ep : C ⊢[PRAAx] val q (lcmu P) ≐ succ (pred (val q (lcmu P))) := Prf.hyp0
  have sE : C ⊢[PRAAx] sg (val q (lcmu P)) ≐ one := (congrSg Ep).eqTrans (sg_succ _)
  have pE : C ⊢[PRAAx] le (pw q (val q (lcmu P))) P :=
    le_congr ((congrMul sE (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) A1.wk
  have l1E : C ⊢[PRAAx] le one (val q (lcmu P)) := one_le_pos Ep
  have qE : C ⊢[PRAAx] le q (pw q (val q (lcmu P))) :=
    le_congr (pw_one q) (.eqRefl _) (PowerCleared.pw_le_exp qpos.wk l1E)
  have s2 : C ⊢[PRAAx] sg (monus (succ P) q) ≐ one :=
    sg_lt ((succ_monus_succ _ _).eqTrans (le_trans qE pE))
  exact le_of_eq_add (d := zero) (alg_full ip.wk s2)

/-- `L_P ∣ ∏_{i ≤ P} i^{[i prime] v_i(L_P)}`. -/
theorem lcm_dvd_full (P : PTm n) : Γ ⊢[PRAAx] dvd (lcmu P) (Sm P P) := by
  have hs1 : Syn.shift (lcmu P) = lcmu (Syn.shift P) := by simp [Syn.shift]
  have hs2 : Syn.shift (Sm P P) = Sm (Syn.shift P) (Syn.shift P) := by simp [Syn.shift]
  refine dvd_of_val_le (N := succ (lcmu P + Sm P P)) (lcmu_pos _) (PE_pos vB (succ P) P)
    ((succ_monus_succ _ _).eqTrans (le_add_right _ _)) ((succ_monus_succ _ _).eqTrans (le_add_left _ _))
    (.allI (.impI (.impI ?_)))
  rw [hs1, hs2]
  let Q : List (Fm PTm (n + 1)) :=
    (isP (var 0) ≐ one) :: lt (var 0) (Syn.shift (succ (lcmu P + Sm P P))) :: Γ.map Fm.shift
  have hv : Q ⊢[PRAAx] prime (var 0) := prime_of_isP Prf.hyp0
  have v1 := val_PE hv vB (succ (Syn.shift P)) (Syn.shift P)
  rw [inst2_XE, inst2_vB] at v1
  exact le_congr (.eqRefl _) v1.eqSymm (val_full hv)

/-! ## The product against `P^{π}` -/

/-- Each factor `i^{[i prime] v_i(L_P)}` is at most `P^{[i prime]}`, for `P ≥ 1`. -/
theorem factor_le_pw {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (i : PTm n) :
    Γ ⊢[PRAAx] le (pw i (isP i * val i (lcmu P))) (pw P (isP i)) := by
  refine .orE (isP_01 i) ?_ ?_
  · have h0 : ((isP i ≐ zero) :: Γ) ⊢[PRAAx] isP i ≐ zero := Prf.hyp0
    exact le_congr (f_zero h0).eqSymm ((congrAp2 powF h0 (.eqRefl P)).eqTrans (pw_zero P)).eqSymm (le_refl one)
  · have h1 : ((isP i ≐ one) :: Γ) ⊢[PRAAx] isP i ≐ one := Prf.hyp0
    exact le_congr (.eqRefl _) ((congrAp2 powF h1 (.eqRefl P)).eqTrans (pw_one P)).eqSymm (factor_le hP.wk i)

/-- `∏_{i ≤ j} i^{[i prime] v_i(L_P)} ≤ P^{π(j)}` for `P ≥ 1`. -/
theorem prod_le_pi {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (j : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (prodF (PE vB)) (succ j) P) (pw P (pc j)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (ap2 (prodF (PE vB)) (succ (var 0)) (Syn.shift P))
      (pw (Syn.shift P) (pc (var 0)))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have e := (Probability.ProductReplacement.prod_succ' (Γ := Γ) (PE vB) zero P).eqTrans
        (congrMul (prod_zero _ _) (.eqRefl _))
      rw [inst2_PE, inst2_XE, inst2_vB] at e
      have f0 : Γ ⊢[PRAAx] pw zero (isP zero * val zero (lcmu P)) ≐ one := f_zero Mobius.isP_zero
      have p0 : Γ ⊢[PRAAx] pw P (pc zero) ≐ one := (congrAp2 powF pc_zero (.eqRefl P)).eqTrans (pw_zero P)
      exact le_congr (e.eqTrans ((one_mul _).eqTrans f0)).eqSymm p0.eqSymm (le_refl _)
    · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      let D : List (Fm PTm (n + 1)) :=
        le (ap2 (prodF (PE vB)) (succ (var 0)) (Syn.shift P)) (pw (Syn.shift P) (pc (var 0))) :: Γ.map Fm.shift
      have hP' : D ⊢[PRAAx] Syn.shift P ≐ succ (pred (Syn.shift P)) := by
        have b := hP.shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
        exact b.wk
      have ih : D ⊢[PRAAx] le (ap2 (prodF (PE vB)) (succ (var 0)) (Syn.shift P))
          (pw (Syn.shift P) (pc (var 0))) := Prf.hyp0
      have e := Probability.ProductReplacement.prod_succ' (Γ := D) (PE vB) (succ (var 0)) (Syn.shift P)
      rw [inst2_PE, inst2_XE, inst2_vB] at e
      have fl := factor_le_pw hP' (succ (var 0))
      have ex : D ⊢[PRAAx] pw (Syn.shift P) (pc (succ (var 0))) ≐
          pw (Syn.shift P) (pc (var 0)) * pw (Syn.shift P) (isP (succ (var 0))) :=
        (congrAp2 powF (pc_succ _) (.eqRefl _)).eqTrans (pw_add _ _ _)
      exact le_congr e.eqSymm ex.eqSymm (le_mul_mono ih fl)
  have r := Prf.allE j hall
  simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at r
  exact r

/-! ## The bounds -/

/-- `lcm(1, …, P) ≤ P^{π(P)}` for `P ≥ 1`. -/
theorem lcm_le_pi {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) : Γ ⊢[PRAAx] le (lcmu P) (pw P (pc P)) :=
  le_trans (dvd_le' (lcmu_pos _) (lcm_dvd_full P) (PE_pos vB (succ P) P)) (prod_le_pi hP P)

/-- **Integer Chebyshev lower bound**: `2^{P−1} ≤ (P + 1) · P^{π(P)}` for `P ≥ 1`. -/
theorem cheb_lower {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) :
    Γ ⊢[PRAAx] le (pw two (pred P)) (succ P * pw P (pc P)) :=
  le_trans (two_pow_lcm P) (le_mul_mono (le_refl _) (lcm_le_pi hP))

/-! ## The logarithmic form -/

/-- `2^a ≤ 2^b` gives `a ≤ b`. -/
theorem exp_le_of_pw_le {a b : PTm n} (h : Γ ⊢[PRAAx] le (pw two a) (pw two b)) : Γ ⊢[PRAAx] le a b := by
  refine .orE (lt_or_le b a) ?_ Prf.hyp0
  have hl : (lt b a :: Γ) ⊢[PRAAx] lt b a := Prf.hyp0
  exact le_lt_absurd _ h.wk (WeightedMangoldt.pw_lt_exp (le_refl two) hl)

theorem expo_alg (B Q : PTm n) : Γ ⊢[PRAAx] succ B + succ B * Q ≐ succ B * succ Q := by
  ipra_ring

/-- For `1 ≤ P < 2^{b+1}`: `P − 1 ≤ (b + 1)(π(P) + 1)`. -/
theorem cheb_lower_log {P b : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P))
    (hb : Γ ⊢[PRAAx] lt P (pw two (succ b))) : Γ ⊢[PRAAx] le (pred P) (succ b * succ (pc P)) := by
  have c := cheb_lower hP
  have h1 : Γ ⊢[PRAAx] le (succ P) (pw two (succ b)) := hb
  have h2 : Γ ⊢[PRAAx] le (pw P (pc P)) (pw (pw two (succ b)) (pc P)) := pw_le_pw (pc P) (le_of_lt hb)
  have e : Γ ⊢[PRAAx] pw two (succ b) * pw (pw two (succ b)) (pc P) ≐ pw two (succ b * succ (pc P)) :=
    (congrMul (.eqRefl _) (RSA.pw_mul two (succ b) (pc P))).eqTrans
      ((pw_add two (succ b) (succ b * pc P)).eqSymm.eqTrans (congrAp2 powF (expo_alg b (pc P)) (.eqRefl _)))
  exact exp_le_of_pw_le (le_trans c (le_congr (.eqRefl _) e (le_mul_mono h1 h2)))

/-! ## The central binomial coefficient and the dyadic bound -/

theorem ge_alg {c S C K : PTm n} (t : Γ ⊢[PRAAx] two * c + S ≐ (two * two) * C)
    (s : Γ ⊢[PRAAx] succ K * c ≐ C) : Γ ⊢[PRAAx] S ≐ two * C + two * (K * c) := by
  ipra_lc natEq t - 2 * natEq s

/-- `2 C(2k, k) ≤ C(2k + 2, k + 1)`. -/
theorem cb_succ_ge (k : PTm n) : Γ ⊢[PRAAx] le (two * cb k) (cb (succ k)) :=
  le_of_eq_add (ge_alg (cat_telescope k) (cat_spec k))

/-- `2^k ≤ C(2k, k)`; variable `0 = k`. -/
abbrev cbF : Fm PTm 1 := le (pw two (var 0)) (cb (var 0))

theorem cb_lower_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] cbF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (pw_zero two).eqSymm cb_zero.eqSymm (le_refl one)
  · have ih : [cbF] ⊢[PRAAx] le (pw two (var 0)) (cb (var 0)) := Prf.hyp0
    have a : [cbF] ⊢[PRAAx] le (two * pw two (var 0)) (two * cb (var 0)) := le_mul_mono (le_refl two) ih
    have e : [cbF] ⊢[PRAAx] pw two (succ (var 0)) ≐ two * pw two (var 0) :=
      (pw_succ two (var 0)).eqTrans (mul_comm _ _)
    exact le_congr e.eqSymm (.eqRefl _) (le_trans a (cb_succ_ge (var 0)))

/-- `2^k ≤ C(2k, k)`. -/
theorem cb_lower (k : PTm n) : Γ ⊢[PRAAx] le (pw two k) (cb k) := by
  have i := inst (Γ := Γ) cb_lower_open ![k]
  simpa using i

/-- `an:binomial`, second inequality: `C(2m, m) ≤ (2m)^{π(2m)}` for `m ≥ 1`. -/
theorem cb_le_pi {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (cb m) (pw (two * m) (pc (two * m))) := by
  have cpos := BinomialThree.pos_of_one_le (central_pos (Γ := Γ) m)
  have hP : Γ ⊢[PRAAx] two * m ≐ succ (pred (two * m)) := Combinatorics.Binomial.pos_mul two_pos' hm
  exact le_trans (dvd_le' cpos (central_dvd_lcm m) (lcmu_pos _)) (lcm_le_pi hP)

/-- **`an:chebyshev`, the lower bound**: `2^k ≤ (k + 1) · π(2^{k+1})`, that is `2^{K−1} ≤ K π(2^K)` for
`K = k + 1 ≥ 1`. -/
theorem cheb_dyadic_lower (k : PTm n) : Γ ⊢[PRAAx] le (pw two k) (succ k * pc (pw two (succ k))) := by
  have Tpos : Γ ⊢[PRAAx] pw two k ≐ succ (pred (pw two k)) := pw_pos' two_pos' k
  have e2 : Γ ⊢[PRAAx] two * pw two k ≐ pw two (succ k) := (mul_comm _ _).eqTrans (pw_succ two k).eqSymm
  have c1 := cb_lower (Γ := Γ) (pw two k)
  have c2 := cb_le_pi Tpos
  have r : Γ ⊢[PRAAx] pw (two * pw two k) (pc (two * pw two k)) ≐ pw two (succ k * pc (pw two (succ k))) :=
    (congrAp2 powF (congrPc e2) e2).eqTrans (RSA.pw_mul two (succ k) (pc (pw two (succ k))))
  exact exp_le_of_pw_le (le_congr (.eqRefl _) r (le_trans c1 c2))

end LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevPi
