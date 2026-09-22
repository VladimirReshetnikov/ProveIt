import Surreal
import Lean.Util.CollectAxioms

/-!
# Axiom audit of the formalization

Check every declaration in the project's `Surreal` namespace, including its
transitive dependencies. Only Lean's standard classical axioms are permitted;
in particular, incomplete proofs and new mathematical axioms fail this target.
This checks proof dependencies, not correspondence with the source documents.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut count : Nat := 0
  let mut used : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`Surreal).isPrefixOf name then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
        unless used.contains axiomName do
          used := used.push axiomName
  if count == 0 then
    throwError "No Surreal declarations found; the audit must import the library"
  logInfo m!"Axiom audit passed for {count} declarations. Axioms used: {used}"

-- The field instance is supplied by mathlib after proving that -1 is not a square.
example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] :
    Field (Surreal.Complexify F) := inferInstance
