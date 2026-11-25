import IPRADerivations.AnalyticNumberTheory.RobinGammaWidth
import IPRADerivations.AnalyticNumberTheory.RobinExpWidth
import IPRADerivations.AnalyticNumberTheory.LcmBridgeDPsi
import IPRADerivations.Core.LinearCombination

/-!
# The numerical side of `(n + 12)2^{−r} ≤ 2^{−k}` (`robin_ipra_research_2026-11-19`, §"Composing the double logarithm")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: "This last inequality follows from
`n < 2^{ℓ(n)}` and the spare factor `2^{16}`." With `r = k + e(n) + 17` (`RobinThreePos.rr`), `P = 2^k`, `R = 2^r`, the
exponential precision `K_e = 32 + 2r` and the Euler-constant parameters `t = 2^{4+r} − 1`, `K_γ = 2r + 2`:

* `fact_ge`: `2^K ≤ (K + 1)!`;
* `n_one`: `16 n P ≤ (K_e + 1)!`; `n_two`: `216 t n P ≤ Z_{K_γ} = 4(2K_γ + 1)3^{2K_γ+1}`;
  `n_three`: `2 n P ≤ (1 + t)²`; `n_four`: `30 P ≤ R`;
* `num_alg`: these give `n(2/(K_e+1)! + 3(9t/Z + 1/(12(1+t)²)))·R·P + 15P ≤ R`, the budget of `RobinWidthCompose`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinWidthNum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinExpName (Fv F_zero F_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGammaWidth (Zg)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb eb_spec c3)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinThreePos (rr tg Kg)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeDPsi (pw_mono_exp four pw2_4 pw_two_eight)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Factorials -/

abbrev FG (K : PTm n) : Fm PTm n := le (pw two K) (Fv (succ K))

theorem fact_ge (K : PTm n) : Γ ⊢[PRAAx] FG K := by
  have hall : Γ ⊢[PRAAx] Fm.all (FG (var 0 : PTm (n + 1))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.inst_zero]
      have e0 := natEq (pw_zero (Γ := Γ) (two : PTm n))
      have f1 := natEq (F_succ (Γ := Γ) (zero : PTm n))
      have f0 := natEq (F_zero (Γ := Γ) (n := n))
      ipra_le 0 with -e0 + f1 + f0
    · simp only [subst_le, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.repl_zero]
      let Δ : List (Fm PTm (n + 1)) := FG (var 0 : PTm (n + 1)) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] FG (var 0 : PTm (n + 1)) := Prf.hyp0
      have e1 := natEq (pw_succ (Γ := Δ) (two : PTm (n + 1)) (var 0))
      have f := natEq (F_succ (Γ := Δ) (succ (var 0 : PTm (n + 1))))
      ipra_le 2 * sl ih + 𝔞 ((var 0 : PTm (n + 1)) * Fv (succ (var 0 : PTm (n + 1)))) with -e1 + f
  have r := Prf.allE K hall
  simpa using r

/-! ## Powers of two -/

theorem pw2_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (pw two a) (pw two b) :=
  pw_mono_exp (by ipra_le 1) h

theorem n_le {N : PTm n} (hN1 : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le N (pw two (succ (eb N one))) := by
  have s := Prf.andE₂ (eb_spec (le_refl one) hN1)
  ipra_le sl s + 1

theorem pw2_five : Γ ⊢[PRAAx] pw two (succ (four : PTm n)) ≐ (num 32 : PTm n) :=
  (pw_succ _ _).eqTrans ((congrMul pw2_4 (.eqRefl _)).eqTrans (by ipra_ring))

/-- `30·2^k ≤ 2^r`. -/
theorem n_four (N k : PTm n) : Γ ⊢[PRAAx] le (num 30 * pw two k) (pw two (rr N k)) := by
  have h := pw2_le (Γ := Γ) (by ipra_le 𝔞 (eb N one) + 12 : Γ ⊢[PRAAx] le (k + succ four) (rr N k))
  have ea := natEq (pw_add (Γ := Γ) (two : PTm n) k (succ four))
  have e5 := natEq (pw2_five (Γ := Γ))
  ipra_le sl h + 2 * 𝔞 (pw two k) with ea + 𝔞 (pw two k) * e5

/-- `16 n 2^k ≤ (K_e + 1)!` for `K_e = 32 + 2r = succ (31 + 2r)`. -/
theorem n_one {N : PTm n} (hN1 : Γ ⊢[PRAAx] le one N) (k : PTm n) :
    Γ ⊢[PRAAx] le (num 16 * N * pw two k) (Fv (succ (succ (num 31 + two * rr N k)))) := by
  have hN := n_le hN1
  have f := fact_ge (Γ := Γ) (succ (num 31 + two * rr N k))
  have h := pw2_le (Γ := Γ) (by ipra_le 𝔞 k + 𝔞 (eb N one) + 61 :
    Γ ⊢[PRAAx] le (four + succ (eb N one) + k) (succ (num 31 + two * rr N k)))
  have ea := natEq (pw_add (Γ := Γ) (two : PTm n) (four + succ (eb N one)) k)
  have eb' := natEq (pw_add (Γ := Γ) (two : PTm n) four (succ (eb N one)))
  have e4 := natEq (pw2_4 (Γ := Γ))
  have m := le_mul_mono hN (le_refl (pw two k))
  ipra_le 16 * sl m + sl h + sl f with ea + 𝔞 (pw two k) * eb' + 𝔞 (pw two (succ (eb N one))) * 𝔞 (pw two k) * e4

theorem tg_le (N k : PTm n) : Γ ⊢[PRAAx] le (tg N k) (pw two (num 4 + rr N k)) := by
  have p := natEq (pw_pos' (Γ := Γ) two_pos' (num 4 + rr N k))
  ipra_le 1 with p

theorem one_tg (N k : PTm n) : Γ ⊢[PRAAx] one + tg N k ≐ pw two (num 4 + rr N k) := by
  ipra_lc -natEq (pw_pos' (Γ := Γ) two_pos' (num 4 + rr N k))

/-- `216 t n 2^k ≤ Z_{K_γ}`. -/
theorem n_two {N : PTm n} (hN1 : Γ ⊢[PRAAx] le one N) (k : PTm n) :
    Γ ⊢[PRAAx] le (num 216 * tg N k * N * pw two k) (Zg (Kg N k)) := by
  have hN := n_le hN1
  have ht := tg_le (Γ := Γ) N k
  have m := le_mul_mono (le_mul_mono ht hN) (le_refl (pw two k))
  have h := pw2_le (Γ := Γ) (by ipra_le 2 * 𝔞 k + 2 * 𝔞 (eb N one) + 43 :
    Γ ⊢[PRAAx] le (four + four + (num 4 + rr N k) + succ (eb N one) + k) (succ (two * Kg N k)))
  have h23 : Γ ⊢[PRAAx] le (two : PTm n) c3 := by ipra_le 1
  have p3 := pw_le_pw (Γ := Γ) (succ (two * Kg N k)) h23
  have e1 := natEq (pw_add (Γ := Γ) (two : PTm n) (four + four + (num 4 + rr N k) + succ (eb N one)) k)
  have e2 := natEq (pw_add (Γ := Γ) (two : PTm n) (four + four + (num 4 + rr N k)) (succ (eb N one)))
  have e3 := natEq (pw_add (Γ := Γ) (two : PTm n) (four + four) (num 4 + rr N k))
  have e8 := natEq (pw_two_eight (Γ := Γ))
  have hZ : Γ ⊢[PRAAx] le (pw c3 (succ (two * Kg N k))) (Zg (Kg N k)) := by
    ipra_le 𝔞 ((num 3 + num 8 * Kg N k) * pw c3 (succ (two * Kg N k)))
  ipra_le 216 * sl m + 40 * 𝔞 (pw two (num 4 + rr N k) * pw two (succ (eb N one)) * pw two k) + sl h + sl p3 + sl hZ with
    e1 + 𝔞 (pw two k) * e2 + 𝔞 (pw two k) * 𝔞 (pw two (succ (eb N one))) * e3 +
      𝔞 (pw two k) * 𝔞 (pw two (succ (eb N one))) * 𝔞 (pw two (num 4 + rr N k)) * e8

/-- `2 n 2^k ≤ (1 + t)²`. -/
theorem n_three {N : PTm n} (hN1 : Γ ⊢[PRAAx] le one N) (k : PTm n) :
    Γ ⊢[PRAAx] le (two * N * pw two k) ((one + tg N k) * (one + tg N k)) := by
  have hN := n_le hN1
  have m := le_mul_mono hN (le_refl (pw two k))
  have h := pw2_le (Γ := Γ) (by ipra_le 𝔞 k + 𝔞 (eb N one) + 40 :
    Γ ⊢[PRAAx] le (succ (succ (eb N one)) + k) ((num 4 + rr N k) + (num 4 + rr N k)))
  have e1 := natEq (pw_add (Γ := Γ) (two : PTm n) (succ (succ (eb N one))) k)
  have e2 := natEq (pw_succ (Γ := Γ) (two : PTm n) (succ (eb N one)))
  have e3 := natEq (pw_add (Γ := Γ) (two : PTm n) (num 4 + rr N k) (num 4 + rr N k))
  have e4 := natEq (one_tg (Γ := Γ) N k)
  ipra_le 2 * sl m + sl h with e1 + 𝔞 (pw two k) * e2 - e3 +
    (𝔞 (pw two (num 4 + rr N k)) + 1 + 𝔞 (tg N k)) * e4

/-- The budget: `n·X·R·P + 15·Y·P ≤ Y·R` with `X/Y = 2/F' + 3(9t/Z + 2Q·Ad/(qq'))`, `qq' = 24(1+t)²Q·Ad`. -/
theorem num_alg {N P R Fp Z t M Qt Ad : PTm n} (n1 : Γ ⊢[PRAAx] le (num 16 * N * P) Fp)
    (n2 : Γ ⊢[PRAAx] le (num 216 * t * N * P) Z) (n3 : Γ ⊢[PRAAx] le (two * N * P) (M * M))
    (n4 : Γ ⊢[PRAAx] le (num 30 * P) R) :
    Γ ⊢[PRAAx] le (N * (two * (Z * (two * two * succ two * (M * M) * Qt) * (two * Ad)) +
        num 3 * (num 9 * t * (two * two * succ two * (M * M) * Qt) * (two * Ad) + two * Qt * Ad * Z) * Fp) * R * P +
        num 15 * (Fp * Z * (two * two * succ two * (M * M) * Qt) * (two * Ad)) * P)
      ((Fp * Z * (two * two * succ two * (M * M) * Qt) * (two * Ad)) * R) := by
  have c : Γ ⊢[PRAAx] le (succ (succ (succ (succ (succ (succ (succ (succ zero))))))) *
        (N * (two * (Z * (two * two * succ two * (M * M) * Qt) * (two * Ad)) +
          num 3 * (num 9 * t * (two * two * succ two * (M * M) * Qt) * (two * Ad) + two * Qt * Ad * Z) * Fp) * R * P +
          num 15 * (Fp * Z * (two * two * succ two * (M * M) * Qt) * (two * Ad)) * P))
      (succ (succ (succ (succ (succ (succ (succ (succ zero))))))) *
        ((Fp * Z * (two * two * succ two * (M * M) * Qt) * (two * Ad)) * R)) := by
    ipra_le 24 * 𝔞 (M * M * Qt * Ad * Z * R) * sl n1 + 24 * 𝔞 (M * M * Qt * Ad * R * Fp) * sl n2 +
      24 * 𝔞 (Qt * Ad * Fp * Z * R) * sl n3 + 96 * 𝔞 (M * M * Qt * Ad * Fp * Z) * sl n4 +
      24 * 𝔞 (M * M * Qt * Ad * Fp * Z * R)
  exact mul_le_cancel c

end LeanProofs.IPRA.AnalyticNumberTheory.RobinWidthNum
