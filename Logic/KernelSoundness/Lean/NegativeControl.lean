import Lean
/-! NEGATIVE CONTROL for `leanchecker`.
    Adds a blatantly ill-typed `theorem bogus : False` to the environment with the
    kernel check disabled.  If `leanchecker` is really re-checking, it MUST reject
    this module. -/
open Lean Elab Command

structure Pair where
  fst : Nat
  snd : Bool

set_option debug.skipKernelTC true in
run_cmd do
  let d : Declaration := .thmDecl {
    name := `bogus
    levelParams := []
    type := mkConst ``False
    value := mkApp2 (mkConst ``Pair.mk) (mkNatLit 0) (mkConst ``Bool.true) }
  liftCoreM <| Lean.addDecl d
  logInfo "added `bogus : False` with kernel type-checking disabled"

#print axioms bogus
