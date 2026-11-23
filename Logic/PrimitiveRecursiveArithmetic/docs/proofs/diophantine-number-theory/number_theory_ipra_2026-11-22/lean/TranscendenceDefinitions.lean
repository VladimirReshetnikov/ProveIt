/- Uncompiled finite definitions and target propositions for the Liouville name.
   Large bounds are mathematical definitions, not intended benchmark inputs. -/
import Mathlib

namespace NumberTheoryIPRA.Transcendence

def normalizeCoefficients (cs : List Int) : List Int :=
  (cs.reverse.dropWhile (fun c => c == 0)).reverse

def degree (cs : List Int) : Nat := (normalizeCoefficients cs).length - 1

def evalRat (cs : List Int) (x : Rat) : Rat :=
  cs.foldr (fun c a => (c : Rat) + x * a) 0

def lipschitzBound (cs : List Int) : Nat :=
  ((List.range cs.length).zip cs).foldl
    (fun a ic => a + ic.1 * ic.2.natAbs) 0

def liouvilleDenominator (n : Nat) : Nat := 10 ^ Nat.factorial n

def liouvillePartial (n : Nat) : Rat :=
  (List.range n).foldl
    (fun a i => a + 1 / ((10 : Rat) ^ Nat.factorial (i + 1))) 0

def startIndex (cs : List Int) : Nat := degree cs + lipschitzBound cs + 1

def separationDenominator (cs : List Int) : Nat :=
  let d := degree cs
  if d = 0 then 1 else 2 * (10 ^ Nat.factorial (startIndex cs + d)) ^ d

def selectedIndex (cs : List Int) : Nat :=
  if degree cs = 0 then 1 else
    let start := startIndex cs
    (((List.range (degree cs + 1)).map (fun i => start + i)).find?
      (fun n => decide (evalRat cs (liouvillePartial n) ≠ 0))).getD start

structure TranscendenceGoals : Prop where
  tail : ∀ m n : Nat, 1 ≤ n → n ≤ m →
    0 ≤ liouvillePartial m - liouvillePartial n ∧
    liouvillePartial m - liouvillePartial n ≤
      2 / ((10 : Rat) ^ Nat.factorial (n + 1))
  polynomialSeparation : ∀ cs : List Int, normalizeCoefficients cs ≠ [] →
    ∀ m : Nat, selectedIndex cs ≤ m →
      1 / (separationDenominator cs : Rat) ≤ abs (evalRat cs (liouvillePartial m))

end NumberTheoryIPRA.Transcendence
