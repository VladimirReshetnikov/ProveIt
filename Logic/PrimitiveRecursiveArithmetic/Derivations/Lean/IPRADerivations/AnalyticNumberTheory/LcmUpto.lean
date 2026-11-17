import IPRADerivations.AnalyticNumberTheory.TotientCorollaries
import IPRADerivations.AnalyticNumberTheory.PrimePowerMangoldt
import IPRADerivations.AnalyticNumberTheory.MuLambda

/-!
# The initial lcm `lcm(1, …, N)` and its valuations

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Lemma `lem:lcm-valuation`.

* `val_lcm`: `v_p(lcm(m, N)) = max(v_p(m), v_p(N))`, written `v_p(m) + (v_p(N) ∸ v_p(m))`, for a prime
  `p` and `m, N ≥ 1`: with `g = gcd(m, N)`, `lcm = g (m/g)(N/g)` and the coprime cofactors cannot
  both be divisible by `p` (`cop_val`);
* `lcmu N = lcm(1, …, N)` by the primitive recursion `lcmu 0 = 1`, `lcmu (N+1) = lcm(lcmu N, N+1)`
  (`lcmu_zero`, `lcmu_succ`), and `lcmu N ≥ 1` (`lcmu_pos`);
* `lcm_valuation` (`lem:lcm-valuation`): for a prime `p`, `e = v_p(lcmu N)` is the largest exponent
  with `p^e ≤ N`, stated as `sg(e) p^e ≤ N < p^{e+1}` (for `N ≥ 1`, `p^e ≤ N < p^{e+1}`);
* `val_lcmu_succ`: `v_p(lcmu (N+1)) = v_p(lcmu N) + [N+1 is a positive power of p]`, the valuation
  form of `thm:lcm-quotient`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (ppI)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (lcm lcm_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul dvd_le' gcd_greatest' gcd_dvd'
  coprime_quotients eq_one_of_dvd_one)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The valuation of an lcm -/

theorem pdvd_of_val_pos {p A : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
    (h : Γ ⊢[PRAAx] val p A ≐ succ (pred (val p A))) : Γ ⊢[PRAAx] dvd p A := by
  have l1 : Γ ⊢[PRAAx] le one (val p A) :=
    le_of_eq_add (d := pred (val p A)) (h.eqTrans (by apply deriveNat; ipra_simps; ring))
  exact dvd_congr_left (pw_one p) ((WeightedMangoldt.dvd_iff_le_val hp hA).2 l1)

/-- Coprime numbers are not both divisible by a prime. -/
theorem cop_val {p A B : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hc : Γ ⊢[PRAAx] gcd A B ≐ one) :
    Γ ⊢[PRAAx] (val p A ≐ zero) ⋎ (val p B ≐ zero) := by
  refine .orE (zero_or_succ (val p A)) (.orI₁ Prf.hyp0) ?_
  refine .orE (zero_or_succ (val p B)) (.orI₂ Prf.hyp0) ?_
  let C : List (Fm PTm n) := (val p B ≐ succ (pred (val p B))) :: (val p A ≐ succ (pred (val p A))) :: Γ
  have hp2 : C ⊢[PRAAx] le two p := (prime_two hp).wk.wk
  have ppos := ValuationMul.p_pos hp2
  have dA := pdvd_of_val_pos hp2 hA.wk.wk Prf.hyp1
  have dB := pdvd_of_val_pos hp2 hB.wk.wk Prf.hyp0
  have d1 : C ⊢[PRAAx] dvd p one := (congrAp2 remF hc.wk.wk.eqSymm (.eqRefl p)).eqTrans (gcd_greatest' ppos dA dB)
  have h21 : C ⊢[PRAAx] le two one := le_congr (.eqRefl _) (eq_one_of_dvd_one ppos d1) hp2
  exact lt_zero_absurd _ ((succ_monus_succ one zero).eqSymm.eqTrans h21)

/-- `v_p(lcm(m, N)) = max(v_p(m), v_p(N))` for a prime `p` and `m, N ≥ 1`. -/
theorem val_lcm {p m N : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] val p (lcm m N) ≐ val p m + monus (val p N) (val p m) := by
  have gpos := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  have eA := eq_of_dvd' gpos (Prf.andE₁ hgd)
  have eB := eq_of_dvd' gpos (Prf.andE₂ hgd)
  have mp := pos_of_eq_mul hm eA
  have Np := pos_of_eq_mul hN eB
  have v1 := (ValuationMul.val_congr p (lcm_eq hm hN)).eqTrans
    ((ValuationMul.val_mul hp gpos (Combinatorics.Binomial.pos_mul mp Np)).eqTrans
      (congrAdd (.eqRefl _) (ValuationMul.val_mul hp mp Np)))
  have vm := (ValuationMul.val_congr p eA).eqTrans (ValuationMul.val_mul hp gpos mp)
  have vN := (ValuationMul.val_congr p eB).eqTrans (ValuationMul.val_mul hp gpos Np)
  refine .orE (cop_val hp mp Np (coprime_quotients hm)) ?_ ?_
  · have h0 : ((val p (quo m (gcd m N)) ≐ zero) :: Γ) ⊢[PRAAx] val p (quo m (gcd m N)) ≐ zero := Prf.hyp0
    have r := (congrMonus vN.wk (vm.wk.eqTrans ((congrAdd (.eqRefl _) h0).eqTrans (add_zero _)))).eqTrans
      (add_monus' _ _)
    refine v1.wk.eqTrans (.eqTrans ?_ (congrAdd vm.wk.eqSymm r.eqSymm))
    apply deriveNat; ipra_simps; ring
  · have h0 : ((val p (quo N (gcd m N)) ≐ zero) :: Γ) ⊢[PRAAx] val p (quo N (gcd m N)) ≐ zero := Prf.hyp0
    have r := (congrMonus (vN.wk.eqTrans ((congrAdd (.eqRefl _) h0).eqTrans (add_zero _))) vm.wk).eqTrans
      (monus_add _ _)
    refine v1.wk.eqTrans (.eqTrans ?_ (congrAdd vm.wk.eqSymm r.eqSymm))
    have z := natEq h0
    apply deriveNat; ipra_simps; linear_combination z

/-! ## `lcm(1, …, N)` -/

/-- The step `lcm(acc, y + 1)`, over `0 = y`, `1 = acc`, `2 = x`. -/
def lcmStep : PTm 3 := quo (var 1 * succ (var 0)) (gcd (var 1) (succ (var 0)))
abbrev lcmuF : PR 2 := rec2 (succ zero) lcmStep

/-- `lcmu N = lcm(1, …, N)`, with `lcmu 0 = 1`. -/
abbrev lcmu (N : PTm n) : PTm n := ap2 lcmuF N zero

theorem lcmu_zero : Γ ⊢[PRAAx] lcmu (zero : PTm n) ≐ one := by
  have h := rec2_zero (Γ := Γ) (succ zero) lcmStep (zero : PTm n)
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem lcmu_succ (N : PTm n) : Γ ⊢[PRAAx] lcmu (succ N) ≐ lcm (lcmu N) (succ N) := by
  have h := rec2_succ (Γ := Γ) (succ zero) lcmStep N zero
  have e : Syn.subst ![N, ap2 lcmuF N zero, zero] lcmStep = lcm (lcmu N) (succ N) := by
    simp only [lcmStep, lcm, lcmu, subst_ap2, PTm.subst_mul, subst_ex2, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rw [e] at h; exact h

theorem pos_of_lt_zero {X : PTm n} (h : Γ ⊢[PRAAx] lt zero X) : Γ ⊢[PRAAx] X ≐ succ (pred X) :=
  Primes.eq_succ_pred ((eq_add_of_le h).eqTrans
    (by apply deriveNat; ipra_simps; ring : Γ ⊢[PRAAx] one + monus X one ≐ succ (monus X one)))

theorem lt_zero_of_pos {X : PTm n} (h : Γ ⊢[PRAAx] X ≐ succ (pred X)) : Γ ⊢[PRAAx] lt zero X :=
  le_of_eq_add (d := pred X) (h.eqTrans (by apply deriveNat; ipra_simps; ring))

/-- `lcm(m, N) ≥ 1` for `m, N ≥ 1`. -/
theorem lcm_pos {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] lcm m N ≐ succ (pred (lcm m N)) := by
  have gpos := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  have mp := pos_of_eq_mul hm (eq_of_dvd' gpos (Prf.andE₁ hgd))
  have Np := pos_of_eq_mul hN (eq_of_dvd' gpos (Prf.andE₂ hgd))
  exact Primes.eq_succ_pred ((lcm_eq hm hN).eqTrans
    ((Combinatorics.Binomial.pos_mul gpos (Combinatorics.Binomial.pos_mul mp Np))))

private abbrev posF : Fm PTm 1 := lt zero (lcmu (var 0))

private theorem pos₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] posF := by
  refine ind _ trivial ?_ ?_
  · simp only [posF, subst_lt, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero]
    exact le_of_eq_add (d := zero) (lcmu_zero.eqTrans (add_zero _).eqSymm)
  · simp only [posF, subst_lt, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact lt_zero_of_pos ((lcmu_succ _).eqTrans ((lcm_pos (pos_of_lt_zero Prf.hyp0)
      (congrSucc (pred_succ _).eqSymm)).eqTrans (congrSucc (congrPred (lcmu_succ _).eqSymm))))

theorem lcmu_pos (N : PTm n) : Γ ⊢[PRAAx] lcmu N ≐ succ (pred (lcmu N)) := by
  have i := inst (Γ := Γ) pos₀ (![N] : Fin 1 → PTm n)
  simp only [posF, subst_lt, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero] at i
  exact pos_of_lt_zero i

/-! ## The valuation step -/

/-- `e = v_p(lcmu N)` is the largest exponent with `p^e ≤ N`: `sg(e) p^e ≤ N < p^{e+1}`. -/
abbrev Inv (p N : PTm n) : Fm PTm n :=
  le (sg (val p (lcmu N)) * pw p (val p (lcmu N))) N ⋏ lt N (pw p (succ (val p (lcmu N))))

theorem inv_zero {p : PTm n} (hp : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] Inv p zero := by
  have e0 : Γ ⊢[PRAAx] val p (lcmu zero) ≐ zero := (congrVal (.eqRefl _) lcmu_zero).eqTrans (ValuationMul.val_one hp)
  refine .andI ?_ ?_
  · exact le_congr (zero_mul_l ((congrSg e0).eqTrans sg_zero) _).eqSymm (.eqRefl _) (le_refl _)
  · have pp : Γ ⊢[PRAAx] pw p (succ (val p (lcmu zero))) ≐ p := (congrPw (.eqRefl _) (congrSucc e0)).eqTrans (pw_one p)
    exact le_congr (.eqRefl _) pp.eqSymm (le_trans (le_succ_self one) hp)

/-- One step: from `Inv p N`, `v_p(lcmu (N+1)) = v_p(lcmu N) + [N + 1 is a positive power of p]` and
`Inv p (N + 1)`. -/
theorem inv_step {p N : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hI : Γ ⊢[PRAAx] Inv p N) :
    Γ ⊢[PRAAx] (val p (lcmu (succ N)) ≐ val p (lcmu N) + ppI p (succ N)) ⋏ Inv p (succ N) := by
  have hp2 := prime_two hp
  have ppos := ValuationMul.p_pos hp2
  have sN : Γ ⊢[PRAAx] succ N ≐ succ (pred (succ N)) := congrSucc (pred_succ _).eqSymm
  have I1 := Prf.andE₁ hI
  have I2 := Prf.andE₂ hI
  have ve : Γ ⊢[PRAAx] val p (lcmu (succ N)) ≐ val p (lcmu N) + monus (val p (succ N)) (val p (lcmu N)) :=
    (congrVal (.eqRefl _) (lcmu_succ N)).eqTrans (val_lcm hp (lcmu_pos N) sN)
  refine .orE (lt_or_le (val p (lcmu N)) (val p (succ N))) ?_ ?_
  · -- a new prime power: `N + 1 = p^w` with `w = e + 1`
    let C : List (Fm PTm n) := lt (val p (lcmu N)) (val p (succ N)) :: Γ
    have h : C ⊢[PRAAx] lt (val p (lcmu N)) (val p (succ N)) := Prf.hyp0
    have ee : C ⊢[PRAAx] val p (lcmu (succ N)) ≐ val p (succ N) := ve.wk.eqTrans (eq_add_of_le (le_of_lt h)).eqSymm
    have wpos : C ⊢[PRAAx] val p (succ N) ≐ succ (pred (val p (succ N))) :=
      Primes.eq_succ_pred ((eq_add_of_le h).eqTrans (by apply deriveNat; ipra_simps; ring :
        C ⊢[PRAAx] succ (val p (lcmu N)) + monus (val p (succ N)) (succ (val p (lcmu N))) ≐
          succ (val p (lcmu N) + monus (val p (succ N)) (succ (val p (lcmu N))))))
    have l1 : C ⊢[PRAAx] le (pw p (val p (succ N))) (succ N) :=
      dvd_le' (Valuation.pw_pos' ppos.wk _) Valuation.val_dvd sN.wk
    have l2 : C ⊢[PRAAx] le (pw p (succ (val p (lcmu N)))) (pw p (val p (succ N))) :=
      PowerCleared.pw_le_exp ppos.wk h
    have eqN : C ⊢[PRAAx] succ N ≐ pw p (val p (succ N)) := le_antisymm (le_trans I2.wk l2) l1
    have eqP : C ⊢[PRAAx] pw p (succ (val p (lcmu N))) ≐ pw p (val p (succ N)) :=
      le_antisymm l2 (le_trans l1 I2.wk) |>.eqSymm |>.eqSymm
    have ew : C ⊢[PRAAx] succ (val p (lcmu N)) ≐ val p (succ N) := WeightedMangoldt.pw_inj_exp hp2.wk eqP
    have sw : C ⊢[PRAAx] sg (val p (succ N)) ≐ one := (congrSg wpos).eqTrans (sg_succ _)
    have pp1 : C ⊢[PRAAx] ppI p (succ N) ≐ one :=
      (congrMul sw (eqb_of_eq eqN.eqSymm)).eqTrans (by apply deriveNat; ipra_simps; ring)
    refine .andI ?_ (.andI ?_ ?_)
    · refine ee.eqTrans (ew.eqSymm.eqTrans ?_)
      refine .eqTrans ?_ (congrAdd (.eqRefl _) pp1.eqSymm)
      apply deriveNat; ipra_simps; ring
    · have s1 : C ⊢[PRAAx] sg (val p (lcmu (succ N))) * pw p (val p (lcmu (succ N))) ≐ pw p (val p (succ N)) :=
        (congrMul ((congrSg ee).eqTrans sw) (congrPw (.eqRefl _) ee)).eqTrans (one_mul _)
      exact le_congr s1.eqSymm (.eqRefl _) l1
    · have l3 : C ⊢[PRAAx] lt (pw p (val p (succ N))) (pw p (succ (val p (succ N)))) :=
        WeightedMangoldt.pw_lt_exp hp2.wk (le_refl _)
      exact lt_congr eqN.eqSymm (congrPw (.eqRefl _) (congrSucc ee.eqSymm)) l3
  · -- no new prime power: `w ≤ e`
    let C : List (Fm PTm n) := le (val p (succ N)) (val p (lcmu N)) :: Γ
    have h : C ⊢[PRAAx] le (val p (succ N)) (val p (lcmu N)) := Prf.hyp0
    have ee : C ⊢[PRAAx] val p (lcmu (succ N)) ≐ val p (lcmu N) :=
      ve.wk.eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _))
    have pp0 : C ⊢[PRAAx] ppI p (succ N) ≐ zero := by
      refine .orE (zero_or_succ (val p (succ N))) ?_ ?_
      · exact zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
      · let D : List (Fm PTm n) := (val p (succ N) ≐ succ (pred (val p (succ N)))) :: C
        have epos : D ⊢[PRAAx] val p (lcmu N) ≐ succ (pred (val p (lcmu N))) :=
          Primes.eq_succ_pred ((eq_add_of_le h.wk).eqTrans ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans
            (by apply deriveNat; ipra_simps; ring : D ⊢[PRAAx] succ (pred (val p (succ N))) +
              monus (val p (lcmu N)) (val p (succ N)) ≐
                succ (pred (val p (succ N)) + monus (val p (lcmu N)) (val p (succ N))))))
        have se : D ⊢[PRAAx] sg (val p (lcmu N)) ≐ one := (congrSg epos).eqTrans (sg_succ _)
        have peN : D ⊢[PRAAx] le (pw p (val p (lcmu N))) N :=
          le_congr ((congrMul se (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) I1.wk.wk
        have pwN : D ⊢[PRAAx] lt (pw p (val p (succ N))) (succ N) :=
          (succ_monus_succ _ _).eqTrans (le_trans (PowerCleared.pw_le_exp ppos.wk.wk h.wk) peN)
        have ne : D ⊢[PRAAx] neg (pw p (val p (succ N)) ≐ succ N) :=
          .impI (lt_irrefl _ _ (lt_congr Prf.hyp0 (.eqRefl _) pwN.wk))
        exact (congrMul (.eqRefl _) (eqb_of_ne ne)).eqTrans (mul_zero _)
    refine .andI ((ee.eqTrans (add_zero _).eqSymm).eqTrans (congrAdd (.eqRefl _) pp0.eqSymm)) (.andI ?_ ?_)
    · exact le_congr (congrMul (congrSg ee.eqSymm) (congrPw (.eqRefl _) ee.eqSymm)) (.eqRefl _)
        (le_trans I1.wk (le_succ_self N))
    · refine lt_congr (.eqRefl _) (congrPw (.eqRefl _) (congrSucc ee.eqSymm)) ?_
      refine .orE (lt_or_eq_of_le I2.wk) Prf.hyp0 ?_
      have v1 : ((succ N ≐ pw p (succ (val p (lcmu N)))) :: C) ⊢[PRAAx] val p (succ N) ≐ succ (val p (lcmu N)) :=
        (congrVal (.eqRefl _) Prf.hyp0).eqTrans (WeightedMangoldt.val_pw _ hp2.wk.wk)
      exact not_succ_le_self _ _ (le_congr v1 (.eqRefl _) h.wk)

/-! ## `lem:lcm-valuation` for every `N` -/

/-- Variables: `0 = N`, `1 = p`. -/
private abbrev lvF : Fm PTm 2 := isP (var 1) ≐ one ⟶ Inv (var 1) (var 0)

theorem subst_Inv {m : ℕ} (σ : Fin n → PTm m) (p N : PTm n) :
    (Inv p N).subst σ = Inv (Syn.subst σ p) (Syn.subst σ N) := by
  simp [Inv, FactorVector.subst_val]

private theorem lv₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] lvF := by
  refine ind _ ⟨trivial, trivial, trivial⟩ ?_ ?_
  · simp only [lvF, Fm.subst_imp, Fm.subst_eq, subst_Inv, FactorVector.subst_isP, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (inv_zero (prime_two (Valuation.prime_of_isP Prf.hyp0)))
  · simp only [lvF, Fm.subst_imp, Fm.subst_eq, subst_Inv, FactorVector.subst_isP, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    exact Prf.andE₂ (inv_step (Valuation.prime_of_isP Prf.hyp0) (Prf.impE Prf.hyp1 Prf.hyp0))

/-- `lem:lcm-valuation`: for a prime `p`, `e = v_p(lcm(1, …, N))` satisfies `sg(e) p^e ≤ N < p^{e+1}`,
i.e. `e = max {a : p^a ≤ N}`. -/
theorem lcm_valuation {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) : Γ ⊢[PRAAx] Inv p N := by
  have i := inst (Γ := Γ) lv₀ (![N, p] : Fin 2 → PTm n)
  simp only [lvF, Fm.subst_imp, Fm.subst_eq, subst_Inv, FactorVector.subst_isP, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact Prf.impE i (Valuation.isP_of_prime hp)

/-- `thm:lcm-quotient`, valuation form: `v_p(lcm(1, …, N+1)) = v_p(lcm(1, …, N)) + [N + 1 is a positive
power of p]` for a prime `p`. -/
theorem val_lcmu_succ {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] val p (lcmu (succ N)) ≐ val p (lcmu N) + ppI p (succ N) :=
  Prf.andE₁ (inv_step hp (lcm_valuation hp N))

/-- `lcm(1, …, N) ∣ lcm(1, …, N+1)` and `N + 1 ∣ lcm(1, …, N+1)`. -/
theorem lcmu_dvd (N : PTm n) :
    Γ ⊢[PRAAx] dvd (lcmu N) (lcmu (succ N)) ⋏ dvd (succ N) (lcmu (succ N)) := by
  have hm := lcmu_pos (Γ := Γ) N
  have hN : Γ ⊢[PRAAx] succ N ≐ succ (pred (succ N)) := congrSucc (pred_succ _).eqSymm
  have gpos := gcd_pos (B := succ N) hm
  have hgd := gcd_dvd' (b := succ N) hm
  have e₁ := natEq (eq_of_dvd' gpos (Prf.andE₁ hgd))
  have e₂ := natEq (eq_of_dvd' gpos (Prf.andE₂ hgd))
  have l := natEq ((lcmu_succ (Γ := Γ) N).eqTrans (lcm_eq hm hN))
  refine .andI (DiophantineNumberTheory.Coprime.dvd_of_eq' hm (w := quo (succ N) (gcd (lcmu N) (succ N))) ?_)
    (DiophantineNumberTheory.Coprime.dvd_of_eq' hN (w := quo (lcmu N) (gcd (lcmu N) (succ N))) ?_)
  · apply deriveNat; ipra_simps; linear_combination l - 𝔞 (quo (succ N) (gcd (lcmu N) (succ N))) * e₁
  · apply deriveNat; ipra_simps; linear_combination l - 𝔞 (quo (lcmu N) (gcd (lcmu N) (succ N))) * e₂

/-! ## The weighted Chebyshev sum -/

section Psi

variable (w : PTm 2)

open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (lamB ellB Lam Lw inst2_lam inst2_ell congrPpI)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2 congrLw lam_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos val_big)

/-- `thm:lcm-quotient`, `L_w` form: `L_w(lcm(1, …, N+1)) = L_w(lcm(1, …, N)) + Λ_w(N + 1)`. -/
theorem lw_lcmu_succ (N y : PTm n) :
    Γ ⊢[PRAAx] Lw w (lcmu (succ N)) y ≐ Lw w (lcmu N) y + Lam w (succ N) y := by
  have dv := lcmu_dvd (Γ := Γ) N
  have L1 := lcmu_pos (Γ := Γ) (succ N)
  have le1 : Γ ⊢[PRAAx] le (succ (lcmu N)) (succ (lcmu (succ N))) :=
    (succ_monus_succ _ _).eqTrans (dvd_le' (lcmu_pos N) (Prf.andE₁ dv) L1)
  have le2 : Γ ⊢[PRAAx] le (succ (succ N)) (succ (lcmu (succ N))) :=
    (succ_monus_succ _ _).eqTrans (dvd_le' (congrSucc (pred_succ _).eqSymm) (Prf.andE₂ dv) L1)
  have hs1 : Syn.shift (lcmu (succ N)) = lcmu (succ (Syn.shift N)) := by simp [Syn.shift]
  have hs2 : Syn.shift (lcmu N) = lcmu (Syn.shift N) := by simp [Syn.shift]
  have hs3 : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have hL : Γ.map Fm.shift ⊢[PRAAx] lcmu (Syn.shift N) ≐ succ (pred (lcmu (Syn.shift N))) := lcmu_pos _
  have hS : Γ.map Fm.shift ⊢[PRAAx] succ (Syn.shift N) ≐ succ (pred (succ (Syn.shift N))) :=
    congrSucc (pred_succ _).eqSymm
  have a := sum_add2 (Γ := Γ) (ellB w) (lamB w) (ellB w) (K := succ (lcmu (succ N))) (x := pairT (lcmu N) y)
    (x' := pairT (succ N) y) (z := pairT (lcmu (succ N)) y) (.allI (.impI (by
      simp only [shift_pairT]
      rw [inst2_ell, inst2_ell, inst2_lam, hs1, hs2, hs3]
      refine (congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _))).eqTrans
        (.eqTrans ?_ (congrAdd
          (congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _)))
          (congrMul (congrMul (.eqRefl _) (congrPpI (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _)))).eqSymm)
      refine .orE (Valuation.isP_01 (var 0)) ?_ ?_
      · exact (zero_mul_l (zero_mul_l Prf.hyp0 _) _).eqTrans ((congrAdd (zero_mul_l (zero_mul_l Prf.hyp0 _) _)
          (zero_mul_l (zero_mul_l Prf.hyp0 _) _)).eqTrans (add_zero _)).eqSymm
      · refine (congrMul (congrMul (.eqRefl _) (val_lcmu_succ (Valuation.prime_of_isP Prf.hyp0) _)) (.eqRefl _)).eqTrans ?_
        apply deriveNat; ipra_simps; ring)))
  have c1 : Γ ⊢[PRAAx] ap2 (sumF (ellB w)) (succ (lcmu (succ N))) (pairT (lcmu N) y) ≐ Lw w (lcmu N) y := by
    refine sum_ext (ellB w) (fun Δ q hs hl => ?_) le1
    rw [shift_pairT, inst2_ell, hs2]
    rw [hs2] at hl
    refine (congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _))) (.eqRefl _)).eqTrans ?_
    exact zero_mul_l ((congrMul (.eqRefl _) (val_big (hL.weaken hs) hl)).eqTrans (mul_zero _)) _
  have c2 : Γ ⊢[PRAAx] ap2 (sumF (lamB w)) (succ (lcmu (succ N))) (pairT (succ N) y) ≐ Lam w (succ N) y := by
    refine sum_ext (lamB w) (fun Δ q hs hl => ?_) le2
    rw [shift_pairT, inst2_lam, hs3]
    rw [hs3] at hl
    refine (congrMul (congrMul (.eqRefl _) (congrPpI (.eqRefl _) (fst_pair _ _))) (.eqRefl _)).eqTrans ?_
    exact zero_mul_l ((congrMul (.eqRefl _) (zero_mul_l ((congrSg (val_big (hS.weaken hs) hl)).eqTrans sg_zero) _)).eqTrans
      (mul_zero _)) _
  exact a.eqTrans (congrAdd c1 c2)

/-- `Λ_w(n)`, over `0 = n`, `1 = y`. -/
abbrev LamB : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (var 1))

/-- The weighted Chebyshev sum `Ψ_w(N) = ∑_{n ≤ N} Λ_w(n) = ∑_{p^a ≤ N} w(p)`. -/
abbrev Psi (N y : PTm n) : PTm n := ap2 (sumF (LamB w)) (succ N) y

theorem inst2_LamB (m y : PTm n) : inst2 (LamB w) m y = Lam w m y := by simp [inst2]

/-- Variables: `0 = N`, `1 = y`. -/
private abbrev psiF : Fm PTm 2 := Psi w (var 0) (var 1) ≐ Lw w (lcmu (var 0)) (var 1)

private theorem psi₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] psiF w := by
  refine ind _ trivial ?_ ?_
  · simp only [psiF, Psi, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine ((sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _))).eqTrans ?_
    rw [inst2_LamB]
    exact (lam_zero w _).eqTrans ((congrLw w _ lcmu_zero).eqTrans (MuLambda.lw_one w _)).eqSymm
  · simp only [psiF, Psi, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine (sum_succ' _ _ _).eqTrans ?_
    rw [inst2_LamB]
    exact (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (lw_lcmu_succ w _ _).eqSymm

/-- `thm:psi-lcm`: `Ψ_w(N) = ∑_{n ≤ N} Λ_w(n) = L_w(lcm(1, …, N))` for every weight `w` and every `N`
(for `w = log`, `ψ(N) = log lcm(1, …, N)`). -/
theorem psi_lcm (N y : PTm n) : Γ ⊢[PRAAx] Psi w N y ≐ Lw w (lcmu N) y := by
  have i := inst (Γ := Γ) (psi₀ w) (![N, y] : Fin 2 → PTm n)
  simpa using i

end Psi

end LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto
