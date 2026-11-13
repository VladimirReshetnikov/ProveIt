module
public meta import Lean
public meta section
/-! Read-only elaboration of an existing private proof constant. The generated
alias theorem still has an explicit type checked by Lean's kernel. This helper
neither adds declarations nor changes the environment; it only returns the
recorded existing constant (private numeric name components have no ordinary
identifier syntax). -/
open Lean Elab Term
elab "existingPrivateBound% " mod:str qualified:str : term => do
  let moduleName := (mod.getString.splitOn ".").foldl Name.str (.str .anonymous "_private")
  let privateName := (qualified.getString.splitOn ".").foldl Name.str (.num moduleName 0)
  let info ← getConstInfo privateName
  match info with
  | .thmInfo _ => pure (mkConst privateName (info.levelParams.map Level.param))
  | _ => throwError "Expected an existing theorem constant, not {privateName}"

