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

The proof splits off the first term (`Core/SumSplit.sum_split`) and bounds the shifted sum.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem sum_pos_comb {S S1 T M : PTm n} (E : Γ ⊢[PRAAx] S ≐ S1 + T) (F : Γ ⊢[PRAAx] S1 ≐ zero)
    (hT : Γ ⊢[PRAAx] le T M) : Γ ⊢[PRAAx] le S M := by
  have a := natEq E; have b := natEq F
  ipra_le sl hT with -a - b

/-- `Σ_{i ≤ N} f(i, x) ≤ N c` when `f(0, x) = 0` and `f(i + 1, x) ≤ c` for `i < N`. -/
theorem sum_le_pos_const (f : PTm 2) {x c N : PTm n} (h0 : Γ ⊢[PRAAx] inst2 f zero x ≐ zero)
    (h : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (inst2 f (succ (var 0)) (Syn.shift x)) (Syn.shift c)) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) (succ N) x) (N * c) := by
  have e : Γ ⊢[PRAAx] succ N ≐ one + N := by ipra_ring
  have E := (congrAp2 (sumF f) e (.eqRefl x)).eqTrans (sum_split f one N x)
  have F : Γ ⊢[PRAAx] ap2 (sumF f) one x ≐ zero :=
    (sum_singleton f x).eqTrans h0
  have T : Γ ⊢[PRAAx] le (ap2 (sumF (offB f)) N (pairT one x)) (N * c) := by
    refine sum_le_const (offB f) (.allI (.impI ?_))
    have s1 : Syn.shift (pairT one x) = pairT one (Syn.shift x) := by simp [Syn.shift]
    rw [s1, inst2_offB]
    refine le_congr (congrInst2 f ?_ (snd_pair _ _)).eqSymm (.eqRefl _) h
    exact (congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans (by ipra_ring)
  exact sum_pos_comb E F T

end LeanProofs.IPRA
