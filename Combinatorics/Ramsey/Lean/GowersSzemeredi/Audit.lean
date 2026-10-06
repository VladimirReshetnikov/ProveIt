import GowersSzemeredi
import Lean.Util.CollectAxioms

/-!
# Axiom audit for the Gowers development

Check every public theorem in the project's namespace, including conditional
implications. This verifies their axiom boundary, not that the hypotheses of
conditional results have been discharged or that the catalogue matches the
paper. The separate source ledger records the numbered statement coverage.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut complete : Nat := 0
  let mut pending : Nat := 0
  for (name, info) in env.constants do
    if (`LeanProofs.GowersSzemeredi).isPrefixOf name && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      checked := checked + 1
    if (`LeanProofs.GowersSzemeredi).isPrefixOf name && info.isDefinition then
      match name.getString!.splitOn "_" with
      | [kind, sec, idx] =>
        if ["theorem", "lemma", "corollary", "proposition"].contains kind &&
            sec.toNat?.isSome && idx.toNat?.isSome then
          let companion := name.appendAfter "_holds"
          match env.find? companion with
          | some (.thmInfo thm) =>
            if thm.type.isConstOf name then
              complete := complete + 1
            else
              pending := pending + 1
          | _ => pending := pending + 1
      | _ => pure ()
  if checked == 0 then
    throwError "No Gowers theorems found: check the audit imports"
  logInfo m!"Audited {checked} public Gowers theorems: only propext, Classical.choice, Quot.sound."
  if complete + pending != 120 then
    throwError "Expected 120 numbered catalogue definitions, found {complete + pending}"
  logInfo m!"Numbered catalogue: {complete} exact companion proofs, {pending} open statements."
