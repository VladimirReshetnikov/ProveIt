import IPRADerivations.AnalyticNumberTheory.PrimorialLower
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.CommonLemmas

/-!
# Bertrand's postulate: the bounded search and the valuation bounds

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex` and `proveit/BertrandObject.lean` (the packet's
source-level client, adapted here and compiled against this workspace).

* `prime_power_bound`: every prime power in the central binomial coefficient `C(2x, x)` is at most `2x`;
* `exponent_le_one`: if `p² > 2x`, then `p` occurs at most once in `C(2x, x)`;
* `exponent_zero_above`: a prime `p > 2x` does not occur;
* `body`, `found`, `witness`, `spec`: the bounded search for the least prime in the strict interval
  `x < p < 2x − 2`, with the test `(i ∸ x) · [i prime]` at index `i < 2x − 2`;
* `select_of_found`: a successful search returns a prime `p` with `x < p < 2x − 2`;
* `zero_of_failed`, `exclude_interval_prime`, `before_witness`: a failed search excludes every prime of the
  interval, and no index before the witness passes the test (the witness is the least prime above `x`);
* `bertrand_of_failure_refuted`: the closed sentence `∀ x. 4 ≤ x → x < p(x) ∧ prime p(x) ∧ p(x) < 2x − 2` follows
  from a derivation of `⊥` from `found x = 0` and `4 ≤ x` (`failureObligation`).

The failure obligation itself (the central binomial lower bound against the product of the prime powers, the
primorial bound, the growth inequality and the finite base certificate of the packet) is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandSearch
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu)
open LeanProofs.IPRA.Combinatorics.Catalan (cb)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim ex_least ex_none)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

alias mul_one0 := Common.mul_one_right

/-! ## Bounding the individual prime powers in the central binomial coefficient -/

/-- Every prime power in C(2x,x) is at most 2x for 2x positive. -/
theorem prime_power_bound {p x : PTm k}
    (hp : Γ ⊢[PRAAx] prime p) (hx : Γ ⊢[PRAAx] two * x ≐ succ (pred (two * x))) :
    Γ ⊢[PRAAx] le (pw p (val p (cb x))) (two * x) := by
  have bound : Γ ⊢[PRAAx] le (pw p (val p (lcmu (two * x)))) (two * x) :=
    le_congr (FactorVector.f_one (isP_of_prime hp)) (.eqRefl _) (PrimorialLower.factor_le hx p)
  exact le_trans (PowerCleared.pw_le_exp (ValuationMul.p_pos (Mobius.prime_two hp))
    (BinomialLcm.binom_val_le hp x)) bound

/-- If p² > 2x then p occurs at most once. -/
theorem exponent_le_one {p x : PTm k}
    (hp : Γ ⊢[PRAAx] prime p) (hx : Γ ⊢[PRAAx] two * x ≐ succ (pred (two * x)))
    (hsq : Γ ⊢[PRAAx] lt (two * x) (p * p)) :
    Γ ⊢[PRAAx] le (val p (cb x)) one := by
  have bound := prime_power_bound hp hx
  have pp := ValuationMul.p_pos (Mobius.prime_two hp)
  refine .orE (lt_or_le one (val p (cb x))) ?_ Prf.hyp0
  let D : List (Fm PTm k) := lt one (val p (cb x)) :: Γ
  have h2 : D ⊢[PRAAx] le two (val p (cb x)) := Prf.hyp0
  have pow2 : D ⊢[PRAAx] le (pw p two) (two * x) :=
    le_trans (PowerCleared.pw_le_exp pp.wk h2) bound.wk
  have sq : D ⊢[PRAAx] le (p * p) (two * x) :=
    le_congr ((pw_succ p one).eqTrans (congrMul (pw_one p) (.eqRefl _))) (.eqRefl _) pow2
  exact not_succ_le_self (two * x) _ (le_trans hsq.wk sq)

/-- A prime beyond the row index has zero valuation. -/
theorem exponent_zero_above {p x : PTm k}
    (hp : Γ ⊢[PRAAx] prime p) (hx : Γ ⊢[PRAAx] two * x ≐ succ (pred (two * x)))
    (hlt : Γ ⊢[PRAAx] lt (two * x) p) :
    Γ ⊢[PRAAx] val p (cb x) ≐ zero := by
  have bound := prime_power_bound hp hx
  have pp := ValuationMul.p_pos (Mobius.prime_two hp)
  refine .orE (zero_or_succ (val p (cb x))) Prf.hyp0 ?_
  let D : List (Fm PTm k) := (val p (cb x) ≐ succ (pred (val p (cb x)))) :: Γ
  have h1 : D ⊢[PRAAx] le one (val p (cb x)) := FactorVector.one_le_pos Prf.hyp0
  have leRow : D ⊢[PRAAx] le p (two * x) :=
    le_congr (pw_one p) (.eqRefl _) (le_trans (PowerCleared.pw_le_exp pp.wk h1) bound.wk)
  exact not_succ_le_self (two * x) _ (le_trans hlt.wk leRow)

/-! ## One search term for the strict interval

The nonzero test at index i and parameter x is (i ∸ x) · [i is prime].
The exclusive search bound 2x ∸ 2 supplies the other inequality. A failed
scan returns this bound. The theorem applies for x ≥ 4.
-/

abbrev body : PTm 2 := monus (var 0) (var 1) * isP (var 0)

theorem inst_body (i x : PTm k) :
    inst2 body i x = monus i x * isP i := by simp [body, inst2, FactorVector.subst_isP]

abbrev limit (x : PTm k) : PTm k := monus (two * x) two

abbrev found (x : PTm k) : PTm k := exB body (limit x) x
abbrev witness (x : PTm k) : PTm k := wit body (limit x) x

abbrev spec (x : PTm k) : Fm PTm k :=
  lt x (witness x) ⋏ (prime (witness x) ⋏ lt (witness x) (limit x))

/-- Unpack a nonzero test into the lower bound and object-level primality. -/
theorem decode {i x : PTm k} (h : Γ ⊢[PRAAx] neg (monus i x * isP i ≐ zero)) :
    Γ ⊢[PRAAx] lt x i ⋏ prime i := by
  refine .andI (.orE (lt_or_le x i) Prf.hyp0 ?_) (prime_of_isP ?_)
  · exact .botE _ (.impE h.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))
  · refine .orE (isP_01 i) ?_ Prf.hyp0
    exact .botE _ (.impE h.wk ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

theorem select_of_found {x : PTm k} (h : Γ ⊢[PRAAx] found x ≐ one) :
    Γ ⊢[PRAAx] spec x := by
  have scan := ex_elim body h
  have pass := Prf.andE₂ scan
  rw [inst_body] at pass
  have d := decode pass
  exact .andI (Prf.andE₁ d) (.andI (Prf.andE₂ d) (Prf.andE₁ scan))

/-- A failed scan makes every test in the range zero. -/
theorem zero_of_failed {x i : PTm k} (h : Γ ⊢[PRAAx] found x ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i (limit x)) : Γ ⊢[PRAAx] monus i x * isP i ≐ zero := by
  have t := ex_none body h hi
  rw [inst_body] at t
  exact t

/-- In the failed branch, a prime in the strict interval is contradictory. -/
theorem exclude_interval_prime {x i : PTm k} (h : Γ ⊢[PRAAx] found x ≐ zero)
    (lo : Γ ⊢[PRAAx] lt x i) (hi : Γ ⊢[PRAAx] lt i (limit x))
    (hp : Γ ⊢[PRAAx] prime i) : Γ ⊢[PRAAx] Fm.bot := by
  have z := zero_of_failed h hi
  have b : Γ ⊢[PRAAx] le i x :=
    ((congrMul (.eqRefl (monus i x)) (isP_of_prime hp)).eqTrans (mul_one0 _)).eqSymm.eqTrans z
  exact not_succ_le_self x _ (le_trans lo b)

/-- Every index before the selected index fails the same nonzero test. -/
theorem before_witness {x i : PTm k} (hi : Γ ⊢[PRAAx] lt i (witness x)) :
    Γ ⊢[PRAAx] monus i x * isP i ≐ zero := by
  have t := ex_least body hi
  rw [inst_body] at t
  exact t

abbrev goalBody : Fm PTm 1 := le (two + two) (var 0) ⟶ spec (var 0)
abbrev sentence : Fm PTm 0 := univ 1 goalBody

/-- The remaining mathematical obligation is an open *object sequent*. It
contains exactly the lower bound on n and the failure of the strict-interval
scan. Both hypotheses are quantifier-free equations. -/
abbrev failureObligation : Prop :=
  ([found (var 0) ≐ zero, le (two + two) (var 0)] : List (Fm PTm 1)) ⊢[PRAAx] Fm.bot

/-- Finish the full object theorem when the arithmetic contradiction is supplied. -/
theorem bertrand_of_failure_refuted (h : failureObligation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence := by
  refine closeUniv 1 (.impI ?_)
  refine .orE (ex_cases body (limit (var 0)) (var 0)) ?_ (select_of_found Prf.hyp0)
  exact .botE _ h

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandSearch
