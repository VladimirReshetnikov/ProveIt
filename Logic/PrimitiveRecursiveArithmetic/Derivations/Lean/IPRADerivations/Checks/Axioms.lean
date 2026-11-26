import IPRADerivations

/-!
# Axiom audit

Every declaration of the library is checked: each constant declared in a module `IPRADerivations.*`, whatever its
namespace, may depend only on Lean's standard axioms `propext`, `Quot.sound` and `Classical.choice`. In particular
no derivation depends on `sorryAx`, and none on an axiom declared in the library. The axioms of a declaration are
those reported by `#print axioms` (`Lean.collectAxioms`). The check fails the build and names the offending
declarations otherwise. Nothing has to be registered here when a theorem is added.
-/

namespace LeanProofs.IPRA.Checks

open Lean Elab Command

/-- The axioms a declaration of the library may depend on. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- `#ipra_axiom_audit` checks every declaration of the modules `IPRADerivations.*`. -/
elab "#ipra_axiom_audit" : command => do
  let env ← getEnv
  let ours := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc c _ =>
    match env.getModuleIdxFor? c with
    | some i => if (`IPRADerivations).isPrefixOf env.header.moduleNames[i.toNat]! then acc.push c else acc
    | none => acc
  let mut used : NameSet := {}
  let mut offenders : Array Name := #[]
  for c in ours do
    let axs ← collectAxioms c
    used := axs.foldl (·.insert ·) used
    unless axs.all (allowedAxioms.contains ·) do offenders := offenders.push c
  let usedList := used.toArray.qsort Name.lt
  if offenders.isEmpty then
    logInfo m!"axiom audit: {ours.size} declarations of IPRADerivations; axioms used: {usedList}"
  else
    throwError "axiom audit failed: {offenders.size} declarations depend on an axiom other than {allowedAxioms}, \
      among them {(offenders.qsort Name.lt).toList.take 40}; all axioms used: {usedList}"

end LeanProofs.IPRA.Checks

#ipra_axiom_audit
