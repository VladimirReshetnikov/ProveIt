import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Analysis.PowerSums

/-!
# The rank of a vector: componentwise order and strict increase

The vector form of the rank lemmas behind the finite stabilization theorems:

* `FINER-iPRA-framework-2026-11-16`, `lem:demand-inflation`: `rank(x^t) ≤ H`, and if `x^t ≠ x^{t+1}` then
  `rank(x^{t+1}) ≥ rank(x^t) + 1`;
* `darc_ipra_framework_2026-11-16`, `lem:rank-increase`: if `d ≤ e` and `d ≠ e`, then `rank(d) < rank(e)`;
* `scope_ipra_framework_2026-11-16`, Lemma "Strict rank increase";
* `ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16`, `lem:demand-rank`.

A vector of length `m` is a body `a(i, x)` giving its `i`-th coordinate, and its rank is
`∑_{i<m} a(i, x)`. For two vectors `a`, `b` with `a_i ≤ b_i` for `i < m` (a bounded hypothesis):

* `rank_mono`: `rank(a) ≤ rank(b)`; with `b` the capacities this is the bound `rank(x) ≤ H`;
* `agree_all`: if moreover `rank(b) ≤ rank(a)`, then `a_i = b_i` for every `i < m`;
* `rank_dichotomy`: either `a_i = b_i` for every `i < m`, or `rank(a) < rank(b)`. This is the
  intuitionistic form of "if the vectors differ, the rank strictly increases": no coordinate is searched
  for, and no contradiction is used.

Proof of `agree_all`: `∑ b = ∑ a + ∑ (b_i ∸ a_i)`, so the sum of the nonnegative differences vanishes, and
then every difference vanishes (`sum_zero_elim`).

Together with an extensionality rule for the coding of states (equal coordinates give equal codes) and
`Foundations/FiniteStabilization`, `rank_dichotomy` supplies the step hypothesis of `stab` for
packed-vector states. That final assembly depends on the chosen coding and is not carried out here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.VectorRank

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The coordinatewise difference `b_i ∸ a_i`. -/
abbrev df (a b : PTm 2) : PTm 2 := monus b a

theorem inst2_df (a b : PTm 2) (i x : PTm n) : inst2 (df a b) i x = monus (inst2 b i x) (inst2 a i x) := by
  simp [inst2]

section Rank

variable {a b : PTm 2} {m x : PTm n}

/-- Componentwise order gives the order of the ranks. -/
theorem rank_mono
    (hle : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF a) m x) (ap2 (sumF b) m x) :=
  sum_le a b x m hle

/-- `∑ b = ∑ a + ∑ (b_i ∸ a_i)` when `a_i ≤ b_i`. -/
theorem sum_diff
    (hle : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF b) m x ≐ ap2 (sumF a) m x + ap2 (sumF (df a b)) m x := by
  have hc := sum_congr_bounded (Γ := Γ) (addBody a (df a b)) b x x m (.allI (.impI (by
    rw [inst2_addBody, inst2_df]
    exact (eq_add_of_le (Prf.impE hle.allOpen.wk Prf.hyp0)).eqSymm)))
  exact hc.eqSymm.eqTrans (sum_add a (df a b) m x)

/-- If the rank does not increase, the sum of the differences is zero. -/
theorem diff_zero
    (hle : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x))))
    (hsum : Γ ⊢[PRAAx] le (ap2 (sumF b) m x) (ap2 (sumF a) m x)) :
    Γ ⊢[PRAAx] ap2 (sumF (df a b)) m x ≐ zero := by
  have e₁ := natEq (sum_diff hle)
  have hz : Γ ⊢[PRAAx] le (ap2 (sumF (df a b)) m x) zero := by
    ipra_le sl hsum with e₁
  exact le_antisymm hz (zero_le _)

/-- If `a ≤ b` componentwise and `rank(b) ≤ rank(a)`, the vectors agree in every coordinate. -/
theorem agree_all
    (hle : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x))))
    (hsum : Γ ⊢[PRAAx] le (ap2 (sumF b) m x) (ap2 (sumF a) m x)) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      (inst2 a (var 0) (Syn.shift x) ≐ inst2 b (var 0) (Syn.shift x))) := by
  have hS := diff_zero hle hsum
  refine .allI (.impI ?_)
  have hS' := hS.shift
  have e : Fm.shift (ap2 (sumF (df a b)) m x ≐ zero) =
      (ap2 (sumF (df a b)) (Syn.shift m) (Syn.shift x) ≐ zero) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at hS'
  have hk : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
  have z := sum_zero_elim (df a b) hS'.wk hk
  rw [inst2_df] at z
  exact le_antisymm (Prf.impE hle.allOpen.wk hk) z

/-- Strict rank increase, in intuitionistic form: equal in every coordinate, or the rank is strictly
larger. -/
theorem rank_dichotomy
    (hle : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
        (inst2 a (var 0) (Syn.shift x) ≐ inst2 b (var 0) (Syn.shift x))) ⋎
      lt (ap2 (sumF a) m x) (ap2 (sumF b) m x) :=
  .orE (lt_or_le (ap2 (sumF a) m x) (ap2 (sumF b) m x)) (.orI₂ Prf.hyp0)
    (.orI₁ (agree_all hle.wk Prf.hyp0))

end Rank

end LeanProofs.IPRA.Foundations.VectorRank
