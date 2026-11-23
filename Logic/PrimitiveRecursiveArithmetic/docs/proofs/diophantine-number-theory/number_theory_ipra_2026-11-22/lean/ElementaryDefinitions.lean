/-
Elementary definitions for the number-theory-in-iPRA report.

STATUS: specification/implementation outline; not compiled in this environment.
There are no admitted theorem declarations. All mathematical proof obligations
are listed in elementary_manifest.json and ElementaryBlueprint.md.

The use of Lean functions, lists, Int, and Mathlib here describes the semantic
layer. An iPRA formalization must additionally quote these fixed primitive
recursive constructions into the selected first-order function language and
construct quantifier-free-induction derivations. A Lean semantic proof alone
would not establish this object-theoretic claim.
-/
import Mathlib

namespace NumberTheoryIPRA.Elementary

/-- Iteration has a total, supplied clock. -/
def iterate {α : Type} (step : α → α) : Nat → α → α
  | 0, s => s
  | k + 1, s => step (iterate step k s)

def dividesB (d n : Nat) : Bool :=
  if d == 0 then n == 0 else n % d == 0

def primeB (n : Nat) : Bool :=
  decide (2 ≤ n) && (List.range (n + 1)).all
    (fun d => !(dividesB d n) || d == 1 || d == n)

structure DivState where
  q : Nat
  r : Nat
  deriving DecidableEq, Repr

def divStep (b : Nat) (s : DivState) : DivState :=
  if s.r + 1 < b then { q := s.q, r := s.r + 1 }
  else { q := s.q + 1, r := 0 }

/-- On b=0 the output is only a totalizing default. -/
def divide (a b : Nat) : DivState :=
  if b = 0 then { q := 0, r := a }
  else iterate (divStep b) a { q := 0, r := 0 }

structure EuclidState where
  x : Nat
  y : Nat
  u : Int
  v : Int
  r : Int
  s : Int
  deriving DecidableEq, Repr

def euclidStep (z : EuclidState) : EuclidState :=
  if z.y = 0 then z else
    let qr := divide z.x z.y
    { x := z.y, y := qr.r,
      u := z.r, v := z.s,
      r := z.u - (qr.q : Int) * z.r,
      s := z.v - (qr.q : Int) * z.s }

def extendedEuclid (a b : Nat) : EuclidState :=
  iterate euclidStep (a + b + 1)
    { x := a, y := b, u := 1, v := 0, r := 0, s := 1 }

def gcdPR (a b : Nat) : Nat := (extendedEuclid a b).x

def coprimeB (a b : Nat) : Bool := gcdPR a b == 1

def leastFactor (n : Nat) : Nat :=
  (((List.range (n + 1)).filter
      (fun d => decide (2 ≤ d) && dividesB d n)).headD n)

structure FactorState where
  remainder : Nat
  factors : List Nat
  deriving DecidableEq, Repr

def factorStep (s : FactorState) : FactorState :=
  if s.remainder ≤ 1 then s else
    let p := leastFactor s.remainder
    { remainder := s.remainder / p, factors := s.factors ++ [p] }

def factors (n : Nat) : List Nat :=
  (iterate factorStep n { remainder := n, factors := [] }).factors

/-- Used mathematically only for p prime and n positive. -/
def valuation (p n : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun e => dividesB (p ^ e) n)).foldl Nat.max 0

def congruentB (m : Nat) (a b : Int) : Bool :=
  decide (0 < m) && (a % (m : Int) == b % (m : Int))

def phi (n : Nat) : Nat :=
  (List.range n).foldl
    (fun total i => if coprimeB (i + 1) n then total + 1 else total) 0

def sigmaPow (r n : Nat) : Nat :=
  (List.range (n + 1)).foldl
    (fun total d =>
      if decide (0 < d) && dividesB d n then total + d ^ r else total) 0

def tau (n : Nat) : Nat := sigmaPow 0 n

def sigma (n : Nat) : Nat := sigmaPow 1 n

def mobius (n : Nat) : Int :=
  if (List.range (n + 1)).any (fun p => primeB p && dividesB (p * p) n)
  then 0
  else if (factors n).length % 2 = 0 then 1 else -1

/-- For the semantic schema f and g are fixed PR function definitions.
    For one first-order theorem, replace them with coded finite-table access. -/
def convolution (f g : Nat → Int) (n : Nat) : Int :=
  (List.range (n + 1)).foldl
    (fun total d =>
      if decide (0 < d) && dividesB d n then total + f d * g (n / d)
      else total) 0

def epsilon (n : Nat) : Int := if n = 1 then 1 else 0

def nthFlag (flags : List Bool) (i : Nat) : Bool := (flags[i]?).getD false

def sieveStep (N d : Nat) (flags : List Bool) : List Bool :=
  if nthFlag flags d then
    (List.range (N + 1)).map (fun n =>
      nthFlag flags n && !(decide (d * d ≤ n) && dividesB d n))
  else flags

def sieve (N : Nat) : List Bool :=
  (List.range (N + 1)).foldl
    (fun flags d =>
      if 2 ≤ d ∧ d * d ≤ N then sieveStep N d flags else flags)
    ((List.range (N + 1)).map (fun n => decide (2 ≤ n)))

/-- A finite CRT specification; all moduli are checked positive. -/
def crtCheckB (moduli residues : List Nat) (x : Nat) : Bool :=
  moduli.length == residues.length &&
    (moduli.zip residues).all
      (fun ma => decide (0 < ma.1) && x % ma.1 == ma.2 % ma.1)

/-- Deliberately simple bounded witness; faster merging is proved in the text.
    The first successful representative is below the lcm when the system works. -/
def crtWitness (moduli residues : List Nat) : Option Nat :=
  (List.range (moduli.foldl (fun a b => a * b) 1)).find?
    (crtCheckB moduli residues)

/-- Least positive order, returning none on invalid/nonunit inputs. -/
def orderWitness (a n : Nat) : Option Nat :=
  if 1 < n ∧ gcdPR a n = 1 then
    ((List.range (phi n)).map (fun i => i + 1)).find?
      (fun k => a ^ k % n == 1)
  else none

/-- Digits least significant first; after the quotient is zero the list is padded.
    The supplied finite clock avoids an unbounded termination claim. -/
def digitsStateStep (base : Nat) (s : Nat × List Nat) : Nat × List Nat :=
  (s.1 / base, s.2 ++ [s.1 % base])

def paddedDigits (base n clock : Nat) : List Nat :=
  (iterate (digitsStateStep base) clock (n, [])).2

/-- Binomial coefficients may be implemented by the Pascal recurrence.
    Nat.choose is its convenient semantic presentation. -/
def choose (n k : Nat) : Nat := Nat.choose n k

/-- This returns the digit-product residue, used only when p is prime. -/
def lucasValue (p n k : Nat) : Nat :=
  let nd := paddedDigits p n (n + k + 1)
  let kd := paddedDigits p k (n + k + 1)
  (nd.zip kd).foldl (fun acc ij => (acc * choose ij.1 ij.2) % p) 1

def liouville (n : Nat) : Int :=
  if (factors n).length % 2 = 0 then 1 else -1

def squarefreeB (n : Nat) : Bool :=
  !((List.range (n + 1)).any (fun p => primeB p && dividesB (p * p) n))

def squarefreePart (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc p =>
    if primeB p then acc * p ^ (valuation p n % 2) else acc) 1

def squarePartRoot (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc p =>
    if primeB p then acc * p ^ (valuation p n / 2) else acc) 1

def digitSum (base n : Nat) : Nat :=
  (paddedDigits base n (n + 1)).foldl (fun a b => a + b) 0

structure CarryState where
  a : Nat
  b : Nat
  carry : Nat
  count : Nat
  deriving DecidableEq, Repr

def carryStep (p : Nat) (s : CarryState) : CarryState :=
  let next := (s.a % p + s.b % p + s.carry) / p
  { a := s.a / p, b := s.b / p, carry := next, count := s.count + next }

def carryCount (p a b : Nat) : Nat :=
  (iterate (carryStep p) (a + b + 2)
    { a := a, b := b, carry := 0, count := 0 }).count

end NumberTheoryIPRA.Elementary
