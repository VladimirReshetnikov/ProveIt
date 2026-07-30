import Lean
/-!
Differential fuzzer: for closed `Bool`-valued terms, compare
  * the KERNEL's answer   (`Lean.Kernel.whnf`)  -- what `decide`/`rfl` can prove
  * the COMPILER's answer (`Lean.Meta.evalExpr`) -- what `native_decide` proves
Any disagreement is directly a proof of `False`
(`rfl : e = a` together with `native_decide : e = b`).
-/
open Lean Elab Command Meta

private def kernelBool (e : Expr) : CommandElabM (Option Bool) := do
  let env ← getEnv
  match Lean.Kernel.whnf env {} e with
  | .ok r =>
    if r.isConstOf ``Bool.true then return some true
    else if r.isConstOf ``Bool.false then return some false
    else return none
  | .error _ => return none

private def nativeBool (e : Expr) : CommandElabM (Option Bool) := do
  try
    let v ← liftTermElabM <| unsafe Meta.evalExpr Bool (mkConst ``Bool) e
    return some v
  catch _ => return none

syntax (name := diffCheck) "#diff " term : command

@[command_elab diffCheck] def elabDiff : CommandElab := fun stx => do
  let e ← liftTermElabM do
    let e ← Term.elabTerm stx[1] (some (mkConst ``Bool))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let k ← kernelBool e
  let n ← nativeBool e
  match k, n with
  | some a, some b =>
      if a != b then
        logError m!"*** MISMATCH ***  {stx[1]}  kernel={a}  native={b}"
      else
        logInfo m!"ok {a}  {stx[1]}"
  | some a, none => logInfo m!"kernel={a}, native=<fail>  {stx[1]}"
  | none, some b => logInfo m!"kernel=<stuck>, native={b}  {stx[1]}"
  | none, none   => logInfo m!"both fail  {stx[1]}"

/- ---------------- String / Char: UTF-8 model vs `List Char` model ------------- -/
#diff "".length == 0
#diff "abc".length == 3
#diff "日本語".length == 3
#diff "𝕏".length == 1
#diff "𝕏".utf8ByteSize == 4
#diff ("𝕏".get ⟨0⟩) == '𝕏'
#diff ("abc".get ⟨1⟩) == 'b'
#diff ("abc".get ⟨5⟩) == (default : Char)
#diff ("𝕏".get ⟨1⟩) == (default : Char)
#diff ("𝕏".get ⟨2⟩) == (default : Char)
#diff ("abc".set ⟨1⟩ '日') == "a日c"
#diff ("abc".set ⟨7⟩ 'z') == "abc"
#diff ("abc".push '日').length == 4
#diff ("日" ++ "本").length == 2
#diff ("abcdef".extract ⟨1⟩ ⟨3⟩) == "bc"
#diff ("abcdef".extract ⟨3⟩ ⟨1⟩) == ""
#diff ("𝕏𝕏".extract ⟨1⟩ ⟨5⟩) == ""
#diff ("abc".drop 1) == "bc"
#diff ("abc".take 10) == "abc"
#diff "abc".front == 'a'
#diff "".front == (default : Char)
#diff "".back == (default : Char)
#diff ("abc".posOf 'c').byteIdx == 2
#diff ("abc".revPosOf 'z').byteIdx == 0
#diff "aXbXc".splitOn "X" == ["a","b","c"] |>.toString.length > 0
#diff (String.intercalate "," ["a","b"]) == "a,b"
#diff "ABC".toLower == "abc"
#diff "ß".toUpper == "ß"
#diff "abc" < "abd"
#diff ("abc".replace "b" "日") == "a日c"
#diff ("aaa".replace "" "b") == "aaa"
#diff ("abc".isPrefixOf "abcd")
#diff "abc".toList.length == 3
#diff (String.mk ['a','日']).length == 2
#diff (String.mk ['a','日']).utf8ByteSize == 4

/- ---------------- Char ------------- -/
#diff (Char.ofNat 0x110000) == (default : Char)
#diff (Char.ofNat 0xD800) == (default : Char)
#diff (Char.ofNat 0x41) == 'A'
#diff 'A'.toNat == 65
#diff '𝕏'.utf8Size == 4
#diff (Char.ofNat 0x10FFFF).utf8Size == 4
#diff 'a'.isAlpha
#diff (Char.ofNat 0).toNat == 0

/- ---------------- Nat edge cases (kernel GMP accel) ------------- -/
#diff (Nat.gcd 0 0) == 0
#diff (5 / 0 : Nat) == 0
#diff (5 % 0 : Nat) == 5
#diff (Nat.log2 0) == 0
#diff (Nat.log2 1) == 0
#diff (0 ^ 0 : Nat) == 1
#diff (2 ^ 64 - 1 : Nat) == 18446744073709551615
#diff (Nat.shiftRight 1 1000) == 0
#diff (Nat.shiftLeft 1 64) == 18446744073709551616
#diff (Nat.land (2^64) (2^64)) == 18446744073709551616
#diff (Nat.xor (2^63) (2^63)) == 0
#diff ((2^63 : Nat) - (2^63+5)) == 0
#diff (Nat.gcd (2^64) (2^32)) == 4294967296
#diff Nat.decEq (2^64) (2^64) |>.decide
#diff (Nat.nextPowerOfTwo 0) == 1
#diff (Nat.log2 (2^64)) == 64

/- ---------------- Int / UInt / BitVec / Fin ------------- -/
#diff ((-5 : Int) / 2) == -2
#diff ((-5 : Int) % 2) == 1
#diff (Int.emod (-5) 2) == 1
#diff (Int.tdiv (-5) 2) == -2
#diff (Int.fdiv (-5) 2) == -3
#diff ((-5 : Int).natAbs) == 5
#diff (UInt8.ofNat 300) == 44
#diff (UInt32.ofNat (2^32)) == 0
#diff (UInt64.ofNat (2^64 - 1)) == 18446744073709551615
#diff ((0 : UInt8) - 1) == 255
#diff ((1 : UInt8) / 0) == 0
#diff ((1 : UInt8) % 0) == 1
#diff (UInt64.ofNat 5).toNat == 5
#diff (BitVec.ofNat 8 300) == 44#8
#diff ((BitVec.ofNat 8 200) + (BitVec.ofNat 8 100)) == 44#8
#diff ((-1 : Int8)).toInt == -1
#diff ((Fin.ofNat' 7 10)) == (3 : Fin 7)
#diff (USize.ofNat 5).toNat == 5

/- ---------------- List / Array ------------- -/
#diff ([1,2,3] : List Nat).length == 3
#diff (([1,2,3] : List Nat).get? 5).isNone
#diff (#[1,2,3] : Array Nat).size == 3
#diff ((#[1,2,3] : Array Nat)[5]?).isNone
#diff ((#[1,2,3] : Array Nat).extract 2 1).size == 0
#diff (List.range 5).sum == 10
#diff ((#[3,1,2] : Array Nat).qsort (· < ·)) == #[1,2,3]
#diff (([1,2,3] : List Nat).drop 10).isEmpty
