import GowersSzemeredi.Proofs18Final
import Lean.Util.CollectAxioms

/-! For every declaration of a GowersSzemeredi module in the closure of `Proofs18Final`: the
GowersSzemeredi modules defining the constants it uses, and the same-module constants it uses.
Writes `decl_needs2.txt`: `Module Decl | needed modules | same-module constants`. -/

open Lean

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isGS (i : Nat) : Bool := (mods[i]!).toString.startsWith "GowersSzemeredi"
  let lines : Array String := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | none => acc
    | some i =>
      let mi := i.toNat
      if !isGS mi then acc else
        let used := ci.getUsedConstantsAsSet.toList
        let ms := used.filterMap fun u => match env.getModuleIdxFor? u with
          | some j => if j.toNat != mi && isGS j.toNat then some s!"{mods[j.toNat]!}:{u}" else none
          | none => none
        let same := used.filterMap fun u => match env.getModuleIdxFor? u with
          | some j => if j.toNat == mi then some u.toString else none
          | none => none
        acc.push s!"{mods[mi]!} {n} | {" ".intercalate ms.eraseDups} | {" ".intercalate same}"
  IO.FS.writeFile "decl_needs2.txt" ("\n".intercalate lines.toList ++ "\n")
  logInfo m!"{lines.size} declarations"
