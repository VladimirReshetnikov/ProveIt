import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates

/-!
# A sum whose term at `0` vanishes

Framework layer (first use: the weight bound and the count of small primes of the Selberg sieve,
`AnalyticNumberTheory/SieveWeightAbs`, `AnalyticNumberTheory/SievePrimesSharp`).

A sum over `i ≤ N` whose terms are bounded by a constant `c` is at most `(N + 1) c`
(`Foundations/AuxiliaryEnvelope.sum_le_const`). When the term at `i = 0` vanishes, as it does for every sum over
"positive `i`" written with an indicator `[i ≥ 1]`, the bound is `N c`:

* `sum_le_pos_const`: `Σ_{i ≤ N} f(i, x) ≤ N c` when `f(0, x) = 0` and `f(i + 1, x) ≤ c` for `i < N`.

The proof splits off the first term with `sum_shift` and bounds the shifted sum.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sum_pos_comb {S S1 T M : PTm n} (E : Γ ⊢[PRAAx] S ≐ S1 + T) (F : Γ ⊢[PRAAx] S1 ≐ zero)
    (hT : Γ ⊢[PRAAx] le T M) : Γ ⊢[PRAAx] le S M :=
  le_congr (E.eqTrans ((congrAdd F (.eqRefl _)).eqTrans (zero_add _))).eqSymm (.eqRefl _) hT

/-- `Σ_{i ≤ N} f(i, x) ≤ N c` when `f(0, x) = 0` and `f(i + 1, x) ≤ c` for `i < N`. -/
theorem sum_le_pos_const (f : PTm 2) {x c N : PTm n} (h0 : Γ ⊢[PRAAx] inst2 f zero x ≐ zero)
    (h : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (inst2 f (succ (var 0)) (Syn.shift x)) (Syn.shift c)) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) (succ N) x) (N * c) := by
  refine sum_pos_comb (sum_shift f N x) h0 (sum_le_const (shiftBody f) (.allI (.impI ?_)))
  rw [inst2_shiftBody]
  exact h

end LeanProofs.IPRA
