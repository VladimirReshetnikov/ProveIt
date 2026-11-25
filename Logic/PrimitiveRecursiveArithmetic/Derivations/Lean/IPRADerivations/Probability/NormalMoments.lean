import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Core.CertificateTactics

/-!
# The moment numbers of the standard normal distribution

Packet: `probability/normal_distribution_ipra_2026-11-16` (Section 5, `thm:moment-recurrence` and
`eq:standard-moments`; the constants of `thm:absolute-moments`). The even moments of a standard
normal variable are the odd double factorials, `E Z^{2r} = (2r − 1)!!`, and the absolute odd moments
are `E |Z|^{2r+1} = (2r)!! √(2/π)`. Their arithmetic is finite:

* `df r = (2r − 1)!! = ∏_{j<r} (2j + 1)` and `edf r = (2r)!! = ∏_{j<r} (2j + 2)`;
* `df_succ`, `edf_succ` (`thm:moment-recurrence`, `m_{n+2} = (n + 1) m_n`):
  `(2r + 1)!! = (2r − 1)!! (2r + 1)` and `(2r + 2)!! = (2r)!! (2r + 2)`;
* `df_fact` (`eq:standard-moments`): `(2r − 1)!! · 2^r r! = (2r)!`;
* `edf_eq`: `(2r)!! = 2^r r!`, and `double_fact`: `(2r − 1)!! (2r)!! = (2r)!`;
* `df_cb`: `(2r − 1)!! · 2^r = r! C(2r, r)`;
* `df_pos`, and `moment_quotient`: `(2r − 1)!! = (2r)! / (2^r r!)` with the quotient exact.

The integrals that identify these numbers with moments are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.NormalMoments

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact fact_two_succ)
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_fact)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul quo_of_eq)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Double factorials -/

/-- `j ↦ 2j + 1`. -/
abbrev oddB : PTm 2 := succ (two * var 0)
/-- `j ↦ 2j + 2`. -/
abbrev evenB : PTm 2 := two * succ (var 0)

/-- `(2r − 1)!! = ∏_{j<r} (2j + 1)`, the moment `E Z^{2r}`. -/
abbrev df (r : PTm n) : PTm n := ap2 (prodF oddB) r zero
/-- `(2r)!! = ∏_{j<r} (2j + 2)`. -/
abbrev edf (r : PTm n) : PTm n := ap2 (prodF evenB) r zero

theorem df_zero : Γ ⊢[PRAAx] df (zero : PTm n) ≐ one := prod_zero _ _
theorem edf_zero : Γ ⊢[PRAAx] edf (zero : PTm n) ≐ one := prod_zero _ _

/-- `E Z^{2r+2} = (2r + 1) E Z^{2r}`. -/
theorem df_succ (r : PTm n) : Γ ⊢[PRAAx] df (succ r) ≐ df r * succ (two * r) := by
  have h := prod_succ (Γ := Γ) oddB r zero
  have e : Syn.subst ![r, zero] oddB = succ (two * r) := by simp
  rw [e] at h
  exact h

theorem edf_succ (r : PTm n) : Γ ⊢[PRAAx] edf (succ r) ≐ edf r * (two * succ r) := by
  have h := prod_succ (Γ := Γ) evenB r zero
  have e : Syn.subst ![r, zero] evenB = two * succ r := by simp
  rw [e] at h
  exact h

/-! ## `(2r − 1)!! · 2^r r! = (2r)!` -/

theorem dfact_base :
    Γ ⊢[PRAAx] df (zero : PTm n) * (pw two zero * fact zero) ≐ fact (two * zero) := by
  ipra_lc 𝔞(pw two zero) * 𝔞(fact zero) * natEq (df_zero (Γ := Γ)) +
    𝔞(fact zero) * natEq (pw_zero (Γ := Γ) (two : PTm n)) -
    natEq (congrAp2 (Γ := Γ) factF (mul_zero (two : PTm n)) (.eqRefl zero))

theorem dfact_step {r : PTm n} (ih : Γ ⊢[PRAAx] df r * (pw two r * fact r) ≐ fact (two * r)) :
    Γ ⊢[PRAAx] df (succ r) * (pw two (succ r) * fact (succ r)) ≐ fact (two * succ r) := by
  ipra_lc 𝔞(pw two (succ r)) * 𝔞(fact (succ r)) * natEq (df_succ (Γ := Γ) r) +
    𝔞(df r) * (2 * 𝔞(r) + 1) * 𝔞(fact (succ r)) * natEq (pw_succ (Γ := Γ) two r) +
    𝔞(df r) * (2 * 𝔞(r) + 1) * 2 * 𝔞(pw two r) * natEq (fact_succ (Γ := Γ) r zero) +
    (2 * 𝔞(r) + 1) * (2 * 𝔞(r) + 2) * natEq ih - natEq (fact_two_succ (Γ := Γ) r)

/-- Variables: `0 = r`. -/
private abbrev dfactF : Fm PTm 1 := df (var 0) * (pw two (var 0) * fact (var 0)) ≐ fact (two * var 0)

private theorem dfact₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] dfactF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact dfact_base
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact dfact_step Prf.hyp0

/-- `eq:standard-moments`: `(2r − 1)!! · 2^r r! = (2r)!`. -/
theorem df_fact (r : PTm n) : Γ ⊢[PRAAx] df r * (pw two r * fact r) ≐ fact (two * r) := by
  have h := inst (Γ := Γ) dfact₀ (![r] : Fin 1 → PTm n)
  simpa using h

/-! ## `(2r)!! = 2^r r!` -/

theorem edf_base : Γ ⊢[PRAAx] edf (zero : PTm n) ≐ pw two zero * fact zero := by
  ipra_lc natEq (edf_zero (Γ := Γ)) - 𝔞(fact zero) * natEq (pw_zero (Γ := Γ) (two : PTm n)) -
    natEq (fact_zero (Γ := Γ) (zero : PTm n))

theorem edf_step {r : PTm n} (ih : Γ ⊢[PRAAx] edf r ≐ pw two r * fact r) :
    Γ ⊢[PRAAx] edf (succ r) ≐ pw two (succ r) * fact (succ r) := by
  ipra_lc natEq (edf_succ (Γ := Γ) r) + 2 * (𝔞(r) + 1) * natEq ih -
    𝔞(fact (succ r)) * natEq (pw_succ (Γ := Γ) two r) - 2 * 𝔞(pw two r) * natEq (fact_succ (Γ := Γ) r zero)

/-- Variables: `0 = r`. -/
private abbrev edfF : Fm PTm 1 := edf (var 0) ≐ pw two (var 0) * fact (var 0)

private theorem edf₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] edfF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact edf_base
  · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact edf_step Prf.hyp0

/-- `(2r)!! = 2^r r!`. -/
theorem edf_eq (r : PTm n) : Γ ⊢[PRAAx] edf r ≐ pw two r * fact r := by
  have h := inst (Γ := Γ) edf₀ (![r] : Fin 1 → PTm n)
  simpa using h

/-- `(2r − 1)!! (2r)!! = (2r)!`. -/
theorem double_fact (r : PTm n) : Γ ⊢[PRAAx] df r * edf r ≐ fact (two * r) :=
  (congrMul (.eqRefl _) (edf_eq r)).eqTrans (df_fact r)

/-! ## Central binomial form, positivity and the quotient -/

/-- `(2r − 1)!! · 2^r = r! C(2r, r)`. -/
theorem df_cb (r : PTm n) : Γ ⊢[PRAAx] df r * pw two r ≐ fact r * cb r := by
  refine mul_cancel (D := fact r) (fact_pos r) ?_
  ipra_lc natEq (df_fact (Γ := Γ) r) + natEq (cb_fact (Γ := Γ) r)

/-- `(2r − 1)!! > 0`. -/
theorem df_pos (r : PTm n) : Γ ⊢[PRAAx] df r ≐ succ (pred (df r)) := by
  refine .orE (zero_or_succ (df r)) (.botE _ ?_) Prf.hyp0
  refine succ_ne_zero (a := pred (fact (two * r))) ((fact_pos (two * r)).eqSymm.eqTrans ?_)
  exact (df_fact r).eqSymm.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))

/-- `E Z^{2r} = (2r)! / (2^r r!)`, the quotient being exact. -/
theorem moment_quotient (r : PTm n) : Γ ⊢[PRAAx] quo (fact (two * r)) (pw two r * fact r) ≐ df r :=
  quo_of_eq (pos_mul (pw_pos one r) (fact_pos r)) ((df_fact r).eqSymm.eqTrans (mul_comm _ _))

end LeanProofs.IPRA.Probability.NormalMoments
