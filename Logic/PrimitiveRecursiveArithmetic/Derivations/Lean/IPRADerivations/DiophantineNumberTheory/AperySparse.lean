import IPRADerivations.DiophantineNumberTheory.AperyLcmCount
import IPRADerivations.AnalyticNumberTheory.ChebyshevBounds

/-!
# The sparse lcm bound of the Apéry packet

Packet: `diophantine-number-theory/apery_ipra`, Proposition `prop:sparse` ("Sparse lcm bound"): for every
`k ≥ 0`, `d_{42^k}^3 ≤ 28^{42^k}`, with `d_N = lcm(1, …, N)`.

"Lemmas `lem:lcm-div` and `lem:multibound` give `d_{42m} ≤ d_m A^m`. If `d_m^3 ≤ 28^m`, then
`d_{42m}^3 ≤ d_m^3 A^{3m} ≤ 28^m (28^{41})^m = 28^{42m}`. Start at `m = 1`, where `d_1^3 = 1 ≤ 28`, and induct
on `k`. The induction formula is itself quantifier-free."

* `lcm_step`: `d_{42m} ≤ d_m A^m` (`AperyLcmCount.lcm_div`, `Coprime.dvd_le'`, `AperyMultinomial.multibound`);
* `sparse_step`: `d_m^3 ≤ 28^m` gives `d_{42m}^3 ≤ 28^{42m}` (with `AperyMultibound.cube_lt`, `A^3 < 28^41`);
* `sparse`: `d_{42^k}^3 ≤ 28^{42^k}`, by quantifier-free induction on `k`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperySparse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (Aval cube_lt mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultinomial (Mm multibound)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyLcmCount (lcm_div Mm_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily (one_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le')
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu lcmuF lcmu_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (lcmu_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `d_{42m} ≤ d_m A^m`. -/
theorem lcm_step (m : PTm k) : Γ ⊢[PRAAx] le (lcmu (num 42 * m)) (lcmu m * pw (num Aval) m) := by
  have h1 := dvd_le' (lcmu_pos _) (lcm_div (Γ := Γ) m) (pos_mul (lcmu_pos m) (Mm_pos m))
  have h2 := multibound (Γ := Γ) m
  exact le_trans h1 (by ipra_le 𝔞 (lcmu m) * sl h2)

/-- `d_m^3 ≤ 28^m` gives `d_{42m}^3 ≤ 28^{42m}`. -/
theorem sparse_step {m : PTm k} (h : Γ ⊢[PRAAx] le (pw (lcmu m) (num 3)) (pw (num 28) m)) :
    Γ ⊢[PRAAx] le (pw (lcmu (num 42 * m)) (num 3)) (pw (num 28) (num 42 * m)) := by
  have a1 := pw_le_pw (num 3) (lcm_step (Γ := Γ) m)
  have a2 := mul_pw (Γ := Γ) (lcmu m) (pw (num Aval) m) (num 3)
  have a3 : Γ ⊢[PRAAx] pw (pw (num Aval) m) (num 3) ≐ pw (pw (num Aval) (num 3)) m :=
    (pw_mul _ _ _).eqTrans ((congrPw (.eqRefl _) (by apply deriveNat; ipra_simps; ring)).eqTrans
      (pw_mul _ _ _).eqSymm)
  have a4 := pw_le_pw m (le_of_lt (cube_lt (Γ := Γ)))
  have a5 := pw_mul (Γ := Γ) (num 28) (num 41) m
  have a6 : Γ ⊢[PRAAx] pw (num 28) (num 42 * m) ≐ pw (num 28) m * pw (num 28) (num 41 * m) :=
    (congrPw (.eqRefl _) (by apply deriveNat; ipra_simps; ring)).eqTrans (pw_add _ _ _)
  have hP : Γ ⊢[PRAAx] le (pw (pw (num Aval) m) (num 3)) (pw (num 28) (num 41 * m)) := le_congr a3.eqSymm a5 a4
  have hm : Γ ⊢[PRAAx] le (pw (lcmu m) (num 3) * pw (pw (num Aval) m) (num 3))
      (pw (num 28) m * pw (num 28) (num 41 * m)) := by
    ipra_le 𝔞 (pw (lcmu m) (num 3)) * sl hP + 𝔞 (pw (num 28) (num 41 * m)) * sl h
  exact le_trans (le_congr (.eqRefl _) a2 a1) (le_congr (.eqRefl _) a6.eqSymm hm)

/-- The base case `d_1^3 ≤ 28^1`. -/
theorem sparse_zero : Γ ⊢[PRAAx] le (pw (lcmu (pw (num 42) zero)) (num 3)) (pw (num 28) (pw (num 42) zero)) := by
  have e1 : Γ ⊢[PRAAx] pw (lcmu (pw (num 42) zero)) (num 3) ≐ one :=
    (congrPw ((congrAp2 lcmuF (pw_zero _) (.eqRefl zero)).eqTrans lcmu_one) (.eqRefl _)).eqTrans (one_pw _)
  have hpos := pw_pos' (Γ := Γ) (p := num 28)
    (show Γ ⊢[PRAAx] succ (num 27) ≐ succ (pred (succ (num 27))) from congrSucc (pred_succ _).eqSymm) (pw (num 42) zero)
  exact le_congr e1.eqSymm hpos.eqSymm (by ipra_le 𝔞 (pred (pw (num 28) (pw (num 42) zero))))

/-- `prop:sparse`: `d_{42^k}^3 ≤ 28^{42^k}`. -/
theorem sparse (K : PTm k) :
    Γ ⊢[PRAAx] le (pw (lcmu (pw (num 42) K)) (num 3)) (pw (num 28) (pw (num 42) K)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pw (lcmu (pw (num 42) (var 0 : PTm (k + 1)))) (num 3))
      (pw (num 28) (pw (num 42) (var 0)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, PTm.subst_num] using (sparse_zero (Γ := Γ))
    · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num]
      have ih := sparse_step (Prf.hyp0 : (le (pw (lcmu (pw (num 42) (var 0))) (num 3))
        (pw (num 28) (pw (num 42) (var 0))) :: Γ.map Fm.shift) ⊢[PRAAx] _)
      have e : (le (pw (lcmu (pw (num 42) (var 0))) (num 3)) (pw (num 28) (pw (num 42) (var 0))) ::
          Γ.map Fm.shift) ⊢[PRAAx] pw (num 42) (succ (var 0)) ≐ num 42 * pw (num 42) (var 0) :=
        (pw_succ _ _).eqTrans (mul_comm _ _)
      exact le_congr (congrPw (congrAp2 lcmuF e (.eqRefl zero)) (.eqRefl _)).eqSymm (congrPw (.eqRefl _) e).eqSymm ih
  have h2 := Prf.allE K hall
  simpa only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, PTm.subst_num] using h2

end LeanProofs.IPRA.DiophantineNumberTheory.AperySparse
