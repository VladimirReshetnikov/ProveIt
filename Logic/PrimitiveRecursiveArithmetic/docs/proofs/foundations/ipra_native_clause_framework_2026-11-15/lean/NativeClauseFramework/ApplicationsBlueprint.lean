import IPRADerivations.Core.Tactic
import NativeClauseFramework.ProgramBlueprint

/-!
# Application exchange examples -- blueprint

The first checked demo should import an existing `Prf PRAAx` polynomial identity,
compose it with one or more native nodes, and export the terminal formula.
-/

namespace LeanProofs.IPRA.NativeClauseFramework

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

/-- A direct polynomial identity can be imported as a native clause node. -/
def importedNode {n : Nat} {ΓP : List (Fm PTm n)} {φ : Fm PTm n}
    (h : ΓP ⊢[PRAAx] φ) :
    Node n
      ((ΓP.map NFm.ofPRA).map fun X => Cl.asm (NFm.unQ X))
      [] :=
  { out := NFm.unQ (NFm.ofPRA φ)
    local := by
      simpa using importPRA h }

/-- Target smoke test: import, compose, and export one existing theorem. -/
theorem algebraControlRoundTrip : True := by
  sorry

/-- Target fixed-dimension Cayley--Hamilton generator theorem. -/
theorem cayleyHamiltonFixedDimension : True := by
  sorry

end LeanProofs.IPRA.NativeClauseFramework
