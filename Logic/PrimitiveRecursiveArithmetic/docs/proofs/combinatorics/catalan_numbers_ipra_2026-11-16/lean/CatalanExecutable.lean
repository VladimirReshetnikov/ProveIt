/-!
Executable specification for the Catalan/iPRA packet.

This file is intentionally independent of Mathlib.  It is a finite
transcription checker, not the internal iPRA proof.  No `sorry` or axioms are
used.  The delivery environment had no Lean binary, so this file is supplied
as an uncompiled specification.
-/
import Std

namespace CatalanIPRA.Executable

/-- Pascal-recursive binomial coefficient. -/
def choose : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Division-free Catalan definition used by the report. -/
def catalan (n : Nat) : Nat :=
  choose (2 * n) n - choose (2 * n) (n + 1)

/-- The first `m` Catalan numbers. -/
def catalans (m : Nat) : List Nat :=
  (List.range m).map catalan

/-- Decode a bounded binary word, least-significant position first. -/
def bitWord (len code : Nat) : List Bool :=
  (List.range len).map (fun i => ((code / (2 ^ i)) % 2) == 1)

/-- Check the Dyck prefix condition; `true` is an up-step. -/
def dyckAux : List Bool -> Int -> Bool
  | [], h => h == 0
  | b :: bs, h =>
      let h' := if b then h + 1 else h - 1
      if h' < 0 then false else dyckAux bs h'


def isDyck (w : List Bool) : Bool := dyckAux w 0

/-- Brute-force bounded Dyck count, intended only for small tests. -/
def dyckCount (n : Nat) : Nat :=
  (List.range (2 ^ (2 * n))).foldl
    (fun total code =>
      if isDyck (bitWord (2 * n) code) then total + 1 else total)
    0

#eval catalans 12
#eval (List.range 7).map dyckCount

example : catalan 0 = 1 := by decide
example : catalan 1 = 1 := by decide
example : catalan 2 = 2 := by decide
example : catalan 3 = 5 := by decide
example : catalan 4 = 14 := by decide
example : dyckCount 4 = 14 := by decide

end CatalanIPRA.Executable
