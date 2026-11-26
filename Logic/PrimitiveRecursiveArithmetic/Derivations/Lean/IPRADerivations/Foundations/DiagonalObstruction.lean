import IPRADerivations.Core.Order
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.Header

/-!
# The diagonal obstruction (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "The exact diagonal obstruction",
proposition "No universal PR evaluation on natural codes": "If `U` were PR, then
`d(n) = U(n, n) + 1` would be PR. Let `e` represent `d`. Evaluating at `n = e` gives
`U(e, e) = U(e, e) + 1`, impossible. ... for any fixed proposed `U`, the contradictory instance
is the one fixed PR definition `d`."

The quantification over all primitive recursive `U` is external: one iPRA theorem for each term
`U(n, e)` (variables `0 = n`, the argument, and `1 = e`, the code). For that term the diagonal
`d(n) = U(n, n) + 1` is a term, and:

* `diag_differs`: `U(e, e) ≠ d(e)` for every `e`: the row with code `e` and the diagonal differ
  at the explicit argument `n = e`;
* `no_code`: no `e` satisfies `∀ n, U(n, e) = d(n)`;
* `no_code_in`: the same for codes restricted to any formula `E(e)` ("restricting the valid
  codes does not help");
* `no_code_closed`: `∀ e ¬ ∀ n (U(n, e) = d(n))` as a closed sentence.

This is the limitation of one representation (codes evaluated by one total term), not a claim
that no cartesian closed category is presented in iPRA: `Foundations/FiniteSetClosed` derives
the exponentials of finite sets.
-/

namespace LeanProofs.IPRA.Foundations.DiagonalObstruction

open_ipra

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `a = a + 1` is absurd. -/
theorem self_ne_succ {a : PTm k} (φ : Fm PTm k) (h : Γ ⊢[PRAAx] a ≐ succ a) : Γ ⊢[PRAAx] φ :=
  not_succ_le_self a φ ((congrMonus (.eqRefl (succ a)) h).eqTrans (le_refl (succ a)))

variable (U : PTm 2)

/-- The diagonal `d(n) = U(n, n) + 1`. -/
abbrev diag (n : PTm k) : PTm k := succ (inst2 U n n)

/-- The row with code `e` differs from the diagonal at the argument `e`. -/
theorem diag_differs (e : PTm k) : Γ ⊢[PRAAx] neg (inst2 U e e ≐ diag U e) :=
  .impI (self_ne_succ _ Prf.hyp0)

/-- The statement "`e` is a code of the diagonal": `∀ n, U(n, e) = d(n)`. -/
def Represents (e : PTm k) : Fm PTm k :=
  Fm.all (inst2 U (var 0) (Syn.shift e) ≐ diag U (var 0))

/-- No code represents the diagonal. -/
theorem no_code (e : PTm k) : Γ ⊢[PRAAx] neg (Represents U e) := by
  refine .impI ?_
  have hyp : (Represents U e :: Γ) ⊢[PRAAx] Represents U e := Prf.hyp0
  have h := Prf.allE e hyp
  simp only [Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] at h
  exact self_ne_succ _ h

/-- Restricting the valid codes to a formula `E` does not help. -/
theorem no_code_in (E : Fm PTm k) (e : PTm k) : Γ ⊢[PRAAx] E ⟶ neg (Represents U e) :=
  .impI (no_code U e)

/-- `∀ e ¬ ∀ n (U(n, e) = U(n, n) + 1)`. -/
theorem no_code_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (neg (Represents U (var 0))) :=
  closeUniv 1 (no_code U (var 0))

end LeanProofs.IPRA.Foundations.DiagonalObstruction
