import Lean
open Lean Elab Command

/-! Do the different ways of building the *same* Name agree on identity AND on
    the cached hash?  A Name whose cached hash disagrees with its structure
    would desynchronise `Environment`'s hash-indexed constant map from
    `Name.beq`, letting two constants share a name. -/

def n1 : Name := Name.str Name.anonymous "foo"      -- raw constructor
def n2 : Name := Name.mkStr Name.anonymous "foo"    -- smart constructor (extern)
def n3 : Name := "foo".toName                       -- parsed from a string
def n4 : Name := Name.mkSimple "foo"
#eval (n1 == n2, n2 == n3, n3 == n4)
#eval (n1.hash, n2.hash, n3.hash, n4.hash)
#eval (Name.quickCmp n1 n2, Name.quickCmp n2 n3, Name.quickCmp n3 n4)

/-! `Name.num` vs a `.str` component that prints the same. -/
def m1 : Name := Name.mkNum (Name.mkSimple "foo") 5
def m2 : Name := Name.mkStr (Name.mkSimple "foo") "5"
#eval (m1.toString, m2.toString)
#eval (m1 == m2)
#eval (m1.toString.toName == m1, m2.toString.toName == m2)
#eval (m1.toString.toName == m2.toString.toName)
#eval (m1.hash, m2.hash)

/-! Canonically-equivalent names: does the environment keep them apart? -/
def nfc : String := "café"
def nfd : String := "café"

run_cmd do
  for (s, v) in [(nfc, 1), (nfd, 2)] do
    let d : Declaration := .defnDecl {
      name := Name.mkSimple s, levelParams := [], type := mkConst ``Nat,
      value := mkNatLit v, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.addDecl d
  let env <- getEnv
  let f (s : String) : String :=
    match env.find? (Name.mkSimple s) with
    | some ci => toString (ci.value!.rawNatLit?.getD 0)
    | none => "MISSING"
  logInfo m!"nfc -> {f nfc} , nfd -> {f nfd}  (expect 1 , 2)"
  logInfo m!"toString round-trips: {(Name.mkSimple nfc).toString.toName == Name.mkSimple nfc} {(Name.mkSimple nfd).toString.toName == Name.mkSimple nfd}"
