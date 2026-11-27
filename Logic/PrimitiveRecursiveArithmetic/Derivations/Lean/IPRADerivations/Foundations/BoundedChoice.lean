import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.Descent

/-!
# The bounded choice schema

Packet: `foundations/scope_ipra_framework_2026-11-16`, `sections/05_bounded_reflection.tex`, Corollary
"Bounded choice schema": "If iPRA proves `∀ x ∃ y < B(x) R(x, y)`, then it proves `∀ x R(x, w(x))` for the
concrete primitive-recursive least witness term `w`"; and, in `sections/08_master_certificates.tex`, the
remark after `thm:finite-strategy`: "For the common shape `∀ x < B ∃ y < C(x) R(x, y)`, a winning strategy
is simply a finite table `σ(x)`", the least valid `y` for each `x`.

The relation is a zero test `f(y, x) = 0` and the witness term is the bounded least search
`w(x) = mu f (B(x)) x` of `Core/Search`.

* `bounded_choice`: from `∀ x ∃ y < B(x). f(y, x) = 0`, `∀ x. w(x) < B(x) ∧ f(w(x), x) = 0`;
* `strategy_table`: from `∀ x < A ∃ y < B(x). f(y, x) = 0`, `∀ x < A. w(x) < B(x) ∧ f(w(x), x) = 0`.

The bound is essential: the witness is found by a search below `B(x)`. This is `lt_of_exists` of
`Foundations/LeastBoundedWitness` under one universal quantifier; no choice principle is used.
-/

namespace LeanProofs.IPRA.Foundations.BoundedChoice

open_ipra exports
open LeanProofs.IPRA.Search (mu)

variable {n : ℕ} {Γ : List (Fm PTm n)} {f : PTm 2} {B : PTm 1}

/-- "Bounded choice schema": the least witness term realizes a bounded existential under `∀`. -/
theorem bounded_choice (h : Γ ⊢[PRAAx] Fm.all (ExW f (inst1 B (var 0)) (var 0))) :
    Γ ⊢[PRAAx] Fm.all (lt (mu f (inst1 B (var 0)) (var 0)) (inst1 B (var 0)) ⋏
      (inst2 f (mu f (inst1 B (var 0)) (var 0)) (var 0) ≐ zero)) :=
  .allI (lt_of_exists h.allOpen)

/-- The strategy table of the shape `∀ x < A ∃ y < B(x)`: the least valid `y` for every `x < A`. -/
theorem strategy_table {A : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift A) ⟶ ExW f (inst1 B (var 0)) (var 0))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift A) ⟶
      (lt (mu f (inst1 B (var 0)) (var 0)) (inst1 B (var 0)) ⋏
        (inst2 f (mu f (inst1 B (var 0)) (var 0)) (var 0) ≐ zero))) :=
  .allI (.impI (lt_of_exists (Prf.impE h.allOpen.wk Prf.hyp0)))

end LeanProofs.IPRA.Foundations.BoundedChoice
