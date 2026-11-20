import Lean

open Lean Elab Command in
elab "audit_axioms " targets:ident+ : command => do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for target in targets do
    let name := target.getId
    unless (env.find? name).isSome do
      throwErrorAt target "missing audit target {name}"
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwErrorAt target "{name}: forbidden axiom {axiomName}"
