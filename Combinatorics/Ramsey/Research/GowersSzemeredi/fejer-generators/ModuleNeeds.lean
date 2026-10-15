import GowersSzemeredi.Proofs18Final
import Lean.Util.CollectAxioms

/-! For every GowersSzemeredi module in the closure of `Proofs18Final`, the GowersSzemeredi
modules that define a constant used (in a type or a value) by one of its own declarations.
Writes `module_needs.txt`: one line per module, `Module Needed1 Needed2 ...`. -/

open Lean

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isGS (i : Nat) : Bool := (mods[i]!).toString.startsWith "GowersSzemeredi"
  let needs : Std.HashMap Nat (Std.HashSet Nat) :=
    env.constants.map₁.fold (init := {}) fun acc n ci =>
      match env.getModuleIdxFor? n with
      | none => acc
      | some i =>
        let mi := i.toNat
        if !isGS mi then acc else
          let s := ci.getUsedConstantsAsSet.toList.foldl (init := acc.getD mi {}) fun s u =>
            match env.getModuleIdxFor? u with
            | some j => if j.toNat != mi && isGS j.toNat then s.insert j.toNat else s
            | none => s
          acc.insert mi s
  let lines := (List.range mods.size).filterMap fun mi =>
    if !isGS mi then none else
      let ns := ((needs.getD mi {}).toList.map fun j => (mods[j]!).toString)
      some (" ".intercalate ((mods[mi]!).toString :: ns))
  IO.FS.writeFile "module_needs.txt" ("\n".intercalate lines ++ "\n")
  logInfo m!"{lines.length} modules"
