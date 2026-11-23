/- Uncompiled semantic blueprint for chapters/quadratic.tex.
   All proof obligations remain in a record, without an asserted inhabitant. -/
import ElementaryDefinitions

namespace NumberTheoryIPRA.Quadratic
open NumberTheoryIPRA.Elementary

def evalMod (p : Nat) (cs : List Nat) (x : Nat) : Nat :=
  cs.foldr (fun c a => (c + x * a) % p) 0

def rootCount (p : Nat) (cs : List Nat) : Nat :=
  ((List.range p).filter (fun x => evalMod p cs x == 0)).length

def legendre (p a : Nat) : Int :=
  if a % p = 0 then 0
  else if (List.range p).any (fun x => x * x % p == a % p) then 1
  else -1

def primitiveRoot (p : Nat) : Option Nat :=
  if primeB p then
    (List.range p).find? (fun a =>
      decide (0 < a) && orderWitness a p == some (p - 1))
  else none

def folded (p r : Nat) : Nat := Nat.min (r % p) (p - r % p)

def negativeCount (p a : Nat) : Nat :=
  ((List.range ((p - 1) / 2)).filter
    (fun i => decide (p < 2 * (a * (i + 1) % p)))).length

structure Four where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving Repr, DecidableEq

def norm4 (x : Four) : Int := x.a ^ 2 + x.b ^ 2 + x.c ^ 2 + x.d ^ 2

def bilinear4 (x r : Four) : Four :=
  { a := x.a*r.a + x.b*r.b + x.c*r.c + x.d*r.d,
    b := x.a*r.b - x.b*r.a - x.c*r.d + x.d*r.c,
    c := x.a*r.c + x.b*r.d - x.c*r.a - x.d*r.b,
    d := x.a*r.d - x.b*r.c + x.c*r.b - x.d*r.a }

def squareDigit (n code i : Nat) : Nat := code / (n + 1) ^ i % (n + 1)

def squareNormCode (dimension n code : Nat) : Nat :=
  (List.range dimension).foldl (fun a i => a + squareDigit n code i ^ 2) 0

def squareWitnessCode (dimension n : Nat) : Nat :=
  ((List.range ((n + 1) ^ dimension)).find?
    (fun c => squareNormCode dimension n c == n)).getD 0

def fourSquares (n : Nat) : Four :=
  let c := squareWitnessCode 4 n
  { a := squareDigit n c 0, b := squareDigit n c 1,
    c := squareDigit n c 2, d := squareDigit n c 3 }

def twoSquareCondition (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun p =>
    !(primeB p && p % 4 == 3) || valuation p n % 2 == 0)

structure QuadraticGoals : Prop where
  fourProduct : ∀ x r : Four, norm4 (bilinear4 x r) = norm4 x * norm4 r
  fourSquaresCorrect : ∀ n : Nat, norm4 (fourSquares n) = (n : Int)
  twoSquaresCorrect : ∀ n : Nat, 0 < n → twoSquareCondition n = true →
    squareNormCode 2 n (squareWitnessCode 2 n) = n
  quadraticReciprocity : ∀ p q : Nat,
    primeB p = true → primeB q = true → 2 < p → 2 < q → p ≠ q →
    legendre p q * legendre q p = (-1 : Int) ^ (((p - 1) / 2) * ((q - 1) / 2))

end NumberTheoryIPRA.Quadratic
