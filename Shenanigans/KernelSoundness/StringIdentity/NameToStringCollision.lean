import Lean
open Lean
/-! Two DISTINCT constants, declared from ordinary source with no
    metaprogramming, whose `Name.toString` outputs are identical. -/

def «a.b»._inaccessible : Nat := 111

namespace a.b
def _inaccessible : Nat := 222
end a.b

def N1 : Name := .str (.str .anonymous "a.b") "_inaccessible"
def N2 : Name := .str (.str (.str .anonymous "a") "b") "_inaccessible"

#eval (N1 == N2)                                  -- distinct names?
#eval (N1.toString, N2.toString)                  -- ... printing identically?
#eval (N1.toString == N2.toString)
#eval (N1.toString.toName == N2)                  -- N1's printed form parses to N2
run_cmd do
  let env ← getEnv
  let val (n : Name) : String :=
    match env.find? n with
    | some ci => match ci.value? with
      | some v => toString v
      | none => "<no value>"
    | none => "MISSING"
  logInfo m!"N1 -> {val N1}"
  logInfo m!"N2 -> {val N2}"
