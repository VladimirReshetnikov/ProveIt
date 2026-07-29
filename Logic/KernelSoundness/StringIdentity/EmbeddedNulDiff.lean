import Lean
/-!
"String equality means different things in different components."

Lean's `String` is logically a `ByteArray` + a proof it is valid UTF-8, and its
API is *specified* by decoding to `List Char`.  At runtime it is a
NUL-terminated buffer (`lean_string_cstr`, and `lean_string_size` counts the
terminating NUL).  `'\0'` is a perfectly valid Unicode scalar value, so a Lean
string may contain an embedded NUL.  Anything in the runtime that reaches for a
C-string view therefore sees a *different string* than the logical model does.

This file differentially tests the KERNEL (which follows the `List Char` model)
against the COMPILER (which follows the byte/C view).  Any disagreement is a
proof of `False`: `rfl` gives one answer, `native_decide` the other.
-/
open Lean Elab Command Meta

private def kernelEval (ty : Expr) (e : Expr) : CommandElabM (Option String) := do
  let env ← getEnv
  match Lean.Kernel.whnf env {} e with
  | .ok r =>
      if r.isConstOf ``Bool.true then return some "true"
      else if r.isConstOf ``Bool.false then return some "false"
      else match r.rawNatLit? with
        | some n => return some (toString n)
        | none => return none
  | .error _ => return none

private def nativeEvalBool (e : Expr) : CommandElabM (Option Bool) := do
  try return some (← liftTermElabM <| unsafe Meta.evalExpr Bool (mkConst ``Bool) e)
  catch _ => return none

private def nativeEvalNat (e : Expr) : CommandElabM (Option Nat) := do
  try return some (← liftTermElabM <| unsafe Meta.evalExpr Nat (mkConst ``Nat) e)
  catch _ => return none

syntax (name := diffB) "#db " term : command
syntax (name := diffN) "#dn " term : command

@[command_elab diffB] def elabDB : CommandElab := fun stx => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm stx[1] (some (mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing; instantiateMVars e
  let k ← kernelEval (mkConst ``Bool) e
  let n ← nativeEvalBool e
  match k, n with
  | some a, some b =>
      let bs := if b then "true" else "false"
      if a != bs then logError m!"*** MISMATCH *** {stx[1]}  kernel={a}  native={bs}"
      else logInfo m!"ok {a}   {stx[1]}"
  | some a, none => logInfo m!"kernel={a} native=<fail>  {stx[1]}"
  | none, some b => logInfo m!"kernel=<stuck> native={b}  {stx[1]}"
  | none, none => logInfo m!"both fail  {stx[1]}"

@[command_elab diffN] def elabDN : CommandElab := fun stx => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm stx[1] (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing; instantiateMVars e
  let k ← kernelEval (mkConst ``Nat) e
  let n ← nativeEvalNat e
  match k, n with
  | some a, some b =>
      if a != toString b then logError m!"*** MISMATCH *** {stx[1]}  kernel={a}  native={b}"
      else logInfo m!"ok {a}   {stx[1]}"
  | some a, none => logInfo m!"kernel={a} native=<fail>  {stx[1]}"
  | none, some b => logInfo m!"kernel=<stuck> native={b}  {stx[1]}"
  | none, none => logInfo m!"both fail  {stx[1]}"

/-- NUL is a perfectly ordinary Unicode scalar value. -/
def nul : Char := Char.ofNat 0

def sA  : String := String.ofList ['a', nul, 'b']
def sB  : String := String.ofList ['a', nul, 'c']
def sC  : String := String.ofList ['a']
def sD  : String := String.ofList ['a', nul]
def sE  : String := String.ofList [nul]
def sF  : String := String.ofList []
def sG  : String := String.ofList ['a', nul, 'b', nul, 'c']

/- ---- equality: does the byte view agree with the model? ---- -/
#db sA == sB
#db sA == sA
#db sA == sC
#db sD == sC
#db sE == sF
#db decide (sA = sB)
#db decide (sD = sC)
#db decide (sE = sF)

/- ---- ordering ---- -/
#db sA < sB
#db sB < sA
#db sC < sD
#db sD < sC
#db sF < sE
#db decide (sA < sB)
#db decide (sC < sD)

/- ---- lengths / sizes ---- -/
#dn sA.length
#dn sA.utf8ByteSize
#dn sD.length
#dn sD.utf8ByteSize
#dn sE.length
#dn sE.utf8ByteSize
#dn sG.length
#dn sG.utf8ByteSize
#dn sA.toList.length
#dn sG.toList.length

/- ---- searching / prefixes ---- -/
#db sC.isPrefixOf sA
#db sD.isPrefixOf sA
#db sA.isPrefixOf sG
#db "".isPrefixOf sA
#dn (sA.posOf 'b').byteIdx
#dn (sG.posOf 'c').byteIdx
#db sA.contains 'b'
#db sG.contains 'c'
#dn sA.toList.length
#dn (sA.splitOn (String.ofList [nul])).length
#dn (sA.replace (String.ofList [nul]) "X").length

/- ---- indexing ---- -/
#dn (sA.get ⟨2⟩).toNat
#dn (sA.get ⟨1⟩).toNat
#dn (sG.get ⟨4⟩).toNat
#dn (sA.drop 1).length
#dn (sA.take 2).length
#dn ((sA ++ sB).length)
#dn ((sA ++ sB).utf8ByteSize)
#dn (sA.push 'z').length

/- ---- hashing (a third notion of string identity) ---- -/
#dn sA.hash.toNat
#dn sB.hash.toNat
#dn sC.hash.toNat
#dn sD.hash.toNat
#db sA.hash == sB.hash
#db sC.hash == sD.hash

/- ---- Name: the identity of every constant ---- -/
#db (Name.mkSimple "a").toString == "a"
#dn (Name.mkSimple (String.ofList ['a', nul, 'b'])).toString.length
#db (Name.mkSimple (String.ofList ['a', nul, 'b'])) == (Name.mkSimple "a")
#db (String.ofList ['a', nul, 'b']).toName == (Name.mkSimple "a")
