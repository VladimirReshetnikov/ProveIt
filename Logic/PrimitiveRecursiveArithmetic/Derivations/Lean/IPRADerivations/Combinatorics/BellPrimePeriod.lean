import IPRADerivations.Combinatorics.BellTouchardPower
import IPRADerivations.Core.LinearCombination

/-!
# An explicit period of the Bell numbers modulo a prime (`bell_numbers_ipra`, `thm:prime-period`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/04_congruences.tex`, theorem
`thm:prime-period`: "For every prime `p`, let `N_p = 1 + p + ⋯ + p^{p−1} = (p^p − 1)/(p − 1)`.
Then, for all `n ≥ 0`, `B_{n+N_p} ≡ B_n (mod p)`."

Derived here: the period `p^p − 1 = (p − 1) N_p`, a multiple of the packet's `N_p`. Taking
`r = p` in `thm:touchard-power` (`Combinatorics/BellTouchardPower`) gives
`B_{n+p^p} ≡ B_{n+1} + p B_n ≡ B_{n+1}`, so the residues repeat with period `p^p − 1` from
index `1` on; the index `0` is reached by running `thm:touchard` backwards once
(`B_T + B_1 ≡ B_{T+p} ≡ B_p ≡ B_0 + B_1` for `T = p^p − 1`, and `B_1` cancels).

* `cong_drop`: `rem (x + p y) p = rem x p`; `cong_cancel`: `rem (c + a) p = rem (c + b) p` gives
  `rem a p = rem b p`;
* `shift_pp`: `rem B_{M+p^p} p = rem B_{M+1} p`;
* `period_succ`, `period_zero`, `bell_period`: `rem B_{N+(p^p−1)} p = rem B_N p` for every `N`;
* `bell_period_closed`: the same closed over `p` and `N`.

The sharp period `N_p` of the theorem is derived in `Combinatorics/BellPeriodNp`, which uses
`shift_pp` of this module. Not derived: the least period and `thm:all-moduli-period`.
-/

namespace LeanProofs.IPRA.Combinatorics.BellPrimePeriod

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (bell)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell)
open LeanProofs.IPRA.Combinatorics.BellTouchard (touchard divmod_p)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (touchard_power cong_add cong_of_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `rem (x + p y) p = rem x p`. -/
theorem cong_drop {p : PTm n} (x y : PTm n) (hq : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] rem (x + p * y) p ≐ rem x p :=
  Foundations.ChineseRemainder.rem_eq_of_eq hq (k₁ := zero) (k₂ := y)
    (by ipra_ring)

/-- A common summand cancels from a congruence. -/
theorem cong_cancel {p a b c : PTm n} (hq : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (h : Γ ⊢[PRAAx] rem (c + a) p ≐ rem (c + b) p) : Γ ⊢[PRAAx] rem a p ≐ rem b p := by
  refine Foundations.ChineseRemainder.rem_eq_of_eq hq
    (k₁ := quo (c + b) p) (k₂ := quo (c + a) p) ?_
  ipra_lc natEq (divmod_p hq (c + a)) - natEq (divmod_p hq (c + b)) + natEq h

/-- `B_{M+p^p} ≡ B_{M+1} (mod p)`: `thm:touchard-power` at `r = p`. -/
theorem shift_pp {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (M : PTm n) :
    Γ ⊢[PRAAx] rem (bell (M + pw p p)) p ≐ rem (bell (succ M)) p :=
  (touchard_power hp p M).eqTrans (cong_drop _ _ (prime_eq_succ_pred hp))

/-- The period from index `1` on. -/
theorem period_succ {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (M : PTm n) :
    Γ ⊢[PRAAx] rem (bell (succ M + pred (pw p p))) p ≐ rem (bell (succ M)) p := by
  have hq := prime_eq_succ_pred hp
  have e : Γ ⊢[PRAAx] succ M + pred (pw p p) ≐ M + pw p p := by
    ipra_lc -natEq (pw_pos' hq p)
  exact (cong_of_eq (congrBell e)).eqTrans (shift_pp hp M)

/-- The index `0`: `B_{p^p−1} ≡ B_0 (mod p)`. -/
theorem period_zero {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] rem (bell (pred (pw p p))) p ≐ rem (bell zero) p := by
  have hq := prime_eq_succ_pred hp
  have t1 := touchard hp (pred (pw p p))
  have t0 := touchard hp (zero : PTm n)
  have s1 : Γ ⊢[PRAAx] rem (bell (succ (pred (pw p p)))) p ≐ rem (bell (succ zero)) p :=
    (cong_of_eq (congrBell (a := succ (pred (pw p p))) (b := succ zero + pred (pw p p))
      (by ipra_ring))).eqTrans (period_succ hp zero)
  have sp : Γ ⊢[PRAAx] rem (bell (p + pred (pw p p))) p ≐ rem (bell (p + zero)) p := by
    refine (cong_of_eq (congrBell (congrAdd hq (.eqRefl _)))).eqTrans
      ((period_succ hp (pred p)).eqTrans (cong_of_eq (congrBell ?_)))
    have a := natEq hq
    apply deriveNat; ipra_simps
    linear_combination -a
  refine cong_cancel hq (c := bell (succ zero)) ?_
  exact (cong_add hq s1.eqSymm (.eqRefl _)).eqTrans (t1.eqSymm.eqTrans (sp.eqTrans t0))

/-- `thm:prime-period` for the period `p^p − 1`: `B_{N+(p^p−1)} ≡ B_N (mod p)`. -/
theorem bell_period {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] rem (bell (N + pred (pw p p))) p ≐ rem (bell N) p := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have e : ((N ≐ zero) :: Γ) ⊢[PRAAx] N + pred (pw p p) ≐ pred (pw p p) := by
      ipra_lc natEq (Prf.hyp0 (Γ := Γ) (φ := N ≐ zero))
    exact (cong_of_eq (congrBell e)).eqTrans
      ((period_zero hp.wk).eqTrans (cong_of_eq (congrBell (Prf.eqSymm Prf.hyp0))))
  · exact (cong_of_eq (congrBell (congrAdd Prf.hyp0 (.eqRefl _)))).eqTrans
      ((period_succ hp.wk (pred N)).eqTrans (cong_of_eq (congrBell (Prf.eqSymm Prf.hyp0))))

/-- Closed over `p` and `N`. -/
theorem bell_period_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (prime (var 0) ⟶
      (rem (bell (var 1 + pred (pw (var 0) (var 0)))) (var 0) ≐ rem (bell (var 1)) (var 0))) :=
  closeUniv 2 (.impI (bell_period Prf.hyp0 _))

end LeanProofs.IPRA.Combinatorics.BellPrimePeriod
