import ConciseIPRA.NativeBiInterpretation

/-!
# The exact existing repository bridge

STATUS: a small generic transfer wrapper, not a Jordan theorem.  It has not
been compiled in this environment.  The inspected repository version is
620f5e3b959c3a4284060ada5efb651812612319 (Lean v4.32.0).

The hard missing input is an object-level iPRA derivation of the arithmetized
Jordan statement.  A theorem about `Nat` or `Real` in Lean does not supply it.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

theorem transferConstructiveJordanSchema
    (statement : Fm PTm 0)
    (derivation : Prf PRAAx [] statement) :
    NPrf [] (NFm.ofPRA statement) := by
  exact (pra_iff_native (Γ := []) (φ := statement)).mp derivation

end LeanProofs.ConciseIPRA
