import Lean
open Lean
-- Do `»` and `✝` fail for the SAME reason?
#eval (Name.escapePart "a✝", Name.escapePart "a»b", Name.escapePart "a.b")
-- `Name.toString` with escaping forced ON vs its default:
#eval ((Name.mkSimple "a✝").toString (escape := true), (Name.mkSimple "a✝").toString (escape := false))
#eval (Name.isInaccessibleUserName (Name.mkSimple "a✝"))
-- and the sibling-component collateral:
#eval (Name.str (Name.str .anonymous "a.b") "_inaccessible").toString
#eval (Name.str (Name.str .anonymous "a.b") "ok").toString
