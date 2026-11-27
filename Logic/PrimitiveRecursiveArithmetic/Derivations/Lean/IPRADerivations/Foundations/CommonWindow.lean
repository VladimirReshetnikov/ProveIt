import IPRADerivations.Foundations.WindowStability
import IPRADerivations.Foundations.ApproximateWitness
import IPRADerivations.Core.Header

/-!
# A common window from additive finite budgets: the two counting steps

Packet: `foundations/ipra_embedding_framework`, `paper/04_stability.tex`, Theorem `thm:common-window`
("A common window from additive finite budgets"): from the finite budgets
`∑_{t<T} |a_j(t + 1) − a_j(t)| ≤ V_j` and `∑_{t<T} E_ℓ(t) ≤ C_ℓ`, "a bounded search among `i = 0, …, K`
finds a successful window". Its proof counts: "if `L` windows are `j`-bad, then `L ε_j < V_j` … There
can therefore be at most `K_j` such windows", and with more candidate windows than the total number of
bad ones, one window passes every test.

* `bad_count`: for a cost `c(i)` of the window `i` (the variation inside it; the costs of disjoint
  windows add up to at most the budget) and a badness bit `β(i)` with `β(i) (ε + 1) ≤ c(i)` (a bad
  window costs more than `ε`): `(ε + 1) ∑_{i<N} β(i) ≤ ∑_{i<N} c(i)`, so the number of bad windows times
  `ε + 1` is at most the budget;
* `good_window`: if the aggregated badness `b(i)` (the number of failed tests of the window `i`) has
  `∑_{i ≤ K} b(i) ≤ K`, then the window `i* = argmin b` (a term, by bounded search) has `i* ≤ K` and
  `b(i*) = 0`: fewer failures than windows leaves a window with none.

The windows themselves (`n_{i+1} = n_i + g(n_i)`), the telescoping of the increments inside a window and
the summation over the components are not derived here; `Foundations/FiniteAvoidance` has the uniform
double count.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CommonWindow

open_ipra
open LeanProofs.IPRA.Probability.FiniteLaws (Mn mn_le)
open LeanProofs.IPRA.Foundations.FrontierSoundness (shift_succ' le_of_lt_succ')
open LeanProofs.IPRA.Foundations.WindowStability (sum_lower)
open LeanProofs.IPRA.Foundations.ApproximateWitness (argmin argmin_spec)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Counting the bad windows -/

section Count

variable (β c : PTm 2)

/-- The invariant at the number `J` of windows. -/
abbrev CInv (ε J x : PTm n) : Fm PTm n :=
  le (ap2 (sumF β) J x * succ ε) (ap2 (sumF c) J x)

theorem count_base (ε x : PTm n) : Γ ⊢[PRAAx] CInv β c ε zero x := by
  have zb := natEq (sum_zero (Γ := Γ) β x)
  have zc := natEq (sum_zero (Γ := Γ) c x)
  ipra_le 0 using linear_combination zc - (𝔟 ε + 1) * zb

theorem count_step {ε J x : PTm n}
    (hp : Γ ⊢[PRAAx] le (inst2 β J x * succ ε) (inst2 c J x))
    (ih : Γ ⊢[PRAAx] CInv β c ε J x) : Γ ⊢[PRAAx] CInv β c ε (succ J) x := by
  have ab := natEq (sum_succ' (Γ := Γ) β J x)
  have ac := natEq (sum_succ' (Γ := Γ) c J x)
  ipra_le sl ih + sl hp using linear_combination ac - (𝔟 ε + 1) * ab

theorem count_guard {ε J N x : PTm n} (hJ : Γ ⊢[PRAAx] le (succ J) N)
    (hp : Γ ⊢[PRAAx] lt J N ⟶ le (inst2 β J x * succ ε) (inst2 c J x))
    (ih : Γ ⊢[PRAAx] le J N ⟶ CInv β c ε J x) : Γ ⊢[PRAAx] CInv β c ε (succ J) x :=
  count_step β c (Prf.impE hp hJ) (Prf.impE ih (le_trans (le_succ_self J) hJ))

/-- `thm:common-window`, the count of bad windows: `(ε + 1) · #bad ≤ ∑ c`. -/
theorem bad_count {ε N x : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 β (var 0) (Syn.shift x) * succ (Syn.shift ε)) (inst2 c (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] CInv β c ε N x := by
  let P := CInv β c (Syn.shift ε) (var 0) (Syn.shift x)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P] using count_base (Γ := Γ) β c ε x
    · simp [P]
      exact .impI (count_step β c (.impE hp.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P] using atBound

end Count

/-! ## A window with no failed test -/

/-- `thm:common-window`, the selection: fewer failures than windows leaves a window with none, and the
bounded search `argmin` finds it. -/
theorem good_window {b : PTm 2} {K x : PTm n}
    (h : Γ ⊢[PRAAx] le (ap2 (sumF b) (succ K) x) K) :
    Γ ⊢[PRAAx] le (argmin b K x) K ⋏ (inst2 b (argmin b K x) x ≐ zero) := by
  have hlow : Γ ⊢[PRAAx] le (succ K * Mn b K x) (ap2 (sumF b) (succ K) x) := by
    refine sum_lower (.allI (.impI ?_))
    have e : Syn.shift (Mn b K x) = Mn b (Syn.shift K) (Syn.shift x) := by simp [Syn.shift]
    rw [e, shift_succ']
    exact mn_le b (le_of_lt_succ' Prf.hyp0)
  have hch : Γ ⊢[PRAAx] le (succ K * Mn b K x) K := le_trans hlow h
  have hM : Γ ⊢[PRAAx] Mn b K x ≐ zero := by
    refine .orE (zero_or_succ (Mn b K x)) Prf.hyp0 ?_
    have hs := natEq (Prf.hyp0 : ((Mn b K x ≐ succ (pred (Mn b K x))) :: Γ) ⊢[PRAAx]
      Mn b K x ≐ succ (pred (Mn b K x)))
    have hch' := hch.wk (ψ := Mn b K x ≐ succ (pred (Mn b K x)))
    have abs : ((Mn b K x ≐ succ (pred (Mn b K x))) :: Γ) ⊢[PRAAx] le (succ K) K := by
      ipra_le sl hch' + (𝔟 K + 1) * 𝔟(pred (Mn b K x)) using linear_combination (𝔟 K + 1) * hs
    exact not_succ_le_self K _ abs
  have sp := argmin_spec (Γ := Γ) b K x
  exact .andI (Prf.andE₁ sp) ((Prf.andE₂ sp).eqTrans hM)

end LeanProofs.IPRA.Foundations.CommonWindow
