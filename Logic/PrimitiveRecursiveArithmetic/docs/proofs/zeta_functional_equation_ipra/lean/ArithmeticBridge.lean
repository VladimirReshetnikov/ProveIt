import ConciseIPRA.NativeBiInterpretation

/-!
# The object-language target and the existing ConciseIPRA bridge

STATUS: a small interface draft, not the analytic proof. It was not compiled
in the execution environment (no Lean executable is installed).

`check` is to be a *fixed* primitive-recursive definition which decodes its
three natural inputs as (a rational complex point, a box bound, a precision),
returns 1 on malformed/out-of-box inputs, and otherwise checks the desired
finite rational residual inequality. No evaluator for arbitrary PR program
codes is postulated here. The construction of that fixed `check`, and the
object-theory proof of `residualSentence check`, are the main remaining work.

The final theorem below transfers an existing iPRA derivation. It does not
construct the missing derivation or replace it by an ambient Lean theorem.
-/

namespace ZetaIPRA.Blueprint

open LeanProofs.ConciseIPRA

def residualMatrix (check : PR 3) : Fm PTm 3 :=
  Fm.eq (PTm.app check Syn.var) (PTm.succ PTm.zero)

def residualSentence (check : PR 3) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (residualMatrix check)))

theorem residualMatrix_qf (check : PR 3) :
    (residualMatrix check).QF := by
  trivial

theorem native_of_arithmetic {check : PR 3}
    (h : Prf PRAAx [] (residualSentence check)) :
    NPrf [] (NFm.ofPRA (residualSentence check)) := by
  simpa using
    (pra_iff_native (Γ := []) (φ := residualSentence check)).mp h

end ZetaIPRA.Blueprint
