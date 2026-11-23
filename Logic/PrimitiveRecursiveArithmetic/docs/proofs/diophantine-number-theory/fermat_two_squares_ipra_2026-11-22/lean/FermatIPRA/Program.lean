import Std

/-!
# Executable specification: Fermat's two-square theorem

STATUS: This file is a Lean 4 implementation outline. No Lean compiler was
available in the preparation environment, so it has not been elaborated here.
The companion README records this limitation and the exact verification steps.

Every loop below recurses on an explicitly supplied natural-number bound.
There is no unbounded search, well-founded recursion, or classical choice.
The finite higher-order helpers are specialized to the displayed predicates
when translated to the first-order language of iPRA.
-/

namespace FermatIPRA

/-- Conjunction over `0 <= k < n`, evaluated by primitive recursion. -/
def allBelow (test : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow test n && test n

/-- First successful index below the given bound, or `none`. -/
def firstHit (test : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
      match firstHit test n with
      | some i => some i
      | none => if test n then some n else none

/-- A decidable, bounded definition of primality. -/
def primeB (p : Nat) : Bool :=
  decide (2 ≤ p) &&
    allBelow (fun d => decide (d < 2) || decide (p % d ≠ 0)) p

def Prime (p : Nat) : Prop := primeB p = true

/-- `n! mod p`, keeping intermediate values reduced modulo `p`. -/
def factorialMod (p : Nat) : Nat → Nat
  | 0 => 1 % p
  | n + 1 => ((n + 1) * factorialMod p n) % p

/-- Wilson's explicit square root of `-1` when `p` is prime, `p % 4 = 1`. -/
def root (p : Nat) : Nat := factorialMod p ((p - 1) / 2)

/--
Integer square root by primitive recursion, matching ProveIt's `isqrtF`.
The invariant is `floorSqrt n ^ 2 <= n < (floorSqrt n + 1) ^ 2`.
-/
def floorSqrt : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let h := floorSqrt n
      if (h + 1) * (h + 1) = n + 1 then h + 1 else h

def side (p : Nat) : Nat := floorSqrt p + 1

def gridX (p i : Nat) : Nat := i % side p

def gridY (p i : Nat) : Nat := i / side p

/-- The grid is enumerated by its first `p+1` row-major indices. -/
def label (p t i : Nat) : Nat := (gridX p i + t * gridY p i) % p

/-- Checked collision condition; its variables are all natural numbers. -/
def Collision (p t i j : Nat) : Prop :=
  i < j ∧ j ≤ p ∧ label p t i = label p t j

def collisionB (p t code : Nat) : Bool :=
  let width := p + 1
  let i := code / width
  let j := code % width
  decide (Collision p t i j)

/--
Search all ordered pairs of indices at most `p`. The default is harmless on
inputs outside the theorem's hypotheses: it produces the zero difference.
-/
def collisionIndices (p t : Nat) : Nat × Nat :=
  let width := p + 1
  let code := (firstHit (collisionB p t) (width * width)).getD 0
  (code / width, code % width)

/-- Absolute difference, expressed entirely with natural-number operations. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

def differencePair (p i j : Nat) : Nat × Nat :=
  (absDiff (gridX p j) (gridX p i),
   absDiff (gridY p j) (gridY p i))

def differenceNorm (p i j : Nat) : Nat :=
  let ab := differencePair p i j
  ab.1 * ab.1 + ab.2 * ab.2

def gridWitness (p : Nat) : Nat × Nat :=
  let ij := collisionIndices p (root p)
  differencePair p ij.1 ij.2

/-- Total primitive-recursive candidate. Correctness is a separate theorem. -/
def witness (p : Nat) : Nat × Nat :=
  if p = 2 then (1, 1) else gridWitness p

def Represents (p a b : Nat) : Prop := a * a + b * b = p

def representsB (p a b : Nat) : Bool := decide (Represents p a b)

/--
A proof-carrying output checker. Producing `some` certifies that particular
answer; it does not prove that a successful answer exists on every prime input.
-/
def certify (p : Nat) : Option {ab : Nat × Nat // Represents p ab.1 ab.2} :=
  let ab := witness p
  if h : Represents p ab.1 ab.2 then some ⟨ab, h⟩ else none

def SquareBounds (p : Nat) : Prop :=
  floorSqrt p * floorSqrt p < p ∧ p < side p * side p

end FermatIPRA
