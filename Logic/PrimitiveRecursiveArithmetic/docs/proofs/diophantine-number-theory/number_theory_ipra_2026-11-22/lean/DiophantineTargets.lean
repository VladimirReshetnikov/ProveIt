import Mathlib

/-!
# Diophantine chapter: definition and target outline

This is an uncompiled Lean outline. It contains definitions and statements
encoded as propositions, not completed theorem proofs. It does not contain
theorem axioms or admitted proofs. It is not an iPRA derivation.

The final formalization must prove both these ordinary specifications and
their derivability inside the chosen object-language iPRA calculus.
-/

namespace NumberTheoryIPRA.DiophantineOutline

open scoped BigOperators

structure RatCode where
  num : Int
  den : Nat
deriving DecidableEq, Repr

def RatCode.Valid (r : RatCode) : Prop := 0 < r.den
def RatCode.Reduced (r : RatCode) : Prop :=
  r.Valid ∧ Nat.Coprime r.num.natAbs r.den
def RatCode.Equivalent (r s : RatCode) : Prop :=
  r.num * (s.den : Int) = s.num * (r.den : Int)
def RatCode.LE (r s : RatCode) : Prop :=
  r.num * (s.den : Int) ≤ s.num * (r.den : Int)

def RatCode.normalize (r : RatCode) : RatCode :=
  if r.den = 0 then ⟨0, 1⟩ else
    let g := Nat.gcd r.num.natAbs r.den
    ⟨r.num / (g : Int), r.den / g⟩

def RatCode.add (r s : RatCode) : RatCode :=
  RatCode.normalize
    ⟨r.num * (s.den : Int) + s.num * (r.den : Int), r.den * s.den⟩
def RatCode.mul (r s : RatCode) : RatCode :=
  RatCode.normalize ⟨r.num * s.num, r.den * s.den⟩
def RatCode.inv (r : RatCode) : RatCode :=
  if r.num = 0 then ⟨0, 1⟩
  else if r.num < 0 then ⟨-(r.den : Int), r.num.natAbs⟩
  else ⟨(r.den : Int), r.num.natAbs⟩

def isqrt (n : Nat) : Nat :=
  (List.range (n + 1)).foldl
    (fun current j => if j * j ≤ n then j else current) 0
def IsSquare (n : Nat) : Prop := isqrt n * isqrt n = n

def RationalRootSpec (coeffs : List Int) (r : RatCode) : Prop :=
  let d := coeffs.length - 1
  coeffs.length ≥ 2 ∧ coeffs.getD d 0 ≠ 0 ∧ r.Reduced →
    (∑ i ∈ Finset.range (d + 1),
      coeffs.getD i 0 * r.num ^ i * (r.den : Int) ^ (d - i)) = 0 →
    (r.den : Int) ∣ coeffs.getD d 0

def RightTriangle (a b c : Nat) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a * a + b * b = c * c
def PythagoreanParameters (a b c m n : Nat) : Prop :=
  n > 0 ∧ m > n ∧ Nat.Coprime m n ∧ m % 2 ≠ n % 2 ∧
  a + n * n = m * m ∧ b = 2 * m * n ∧ c = m * m + n * n
def SquareAreaCounterexample (a b c t : Nat) : Prop :=
  RightTriangle a b c ∧ 0 < t ∧ a * b = 2 * t * t
def QuarticCounterexample (x y z : Nat) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 4 + y ^ 4 = z ^ 2

structure CFState where
  pOlder : Nat
  pPrevious : Nat
  qOlder : Nat
  qPrevious : Nat
deriving DecidableEq, Repr
def cfInitial : CFState := ⟨0, 1, 1, 0⟩
def cfStep (s : CFState) (a : Nat) : CFState :=
  ⟨s.pPrevious, a * s.pPrevious + s.pOlder,
   s.qPrevious, a * s.qPrevious + s.qOlder⟩
def continuants (coeffs : List Nat) : CFState :=
  coeffs.foldl cfStep cfInitial
def ValidCF (coeffs : List Nat) : Prop :=
  coeffs ≠ [] ∧ ∀ a ∈ coeffs.drop 1, 0 < a
def CanonicalCF (coeffs : List Nat) : Prop :=
  ValidCF coeffs ∧ (coeffs.length = 1 ∨ 2 ≤ coeffs.getLastD 0)
def cfDeterminant (s : CFState) : Int :=
  (s.pPrevious : Int) * s.qOlder - (s.pOlder : Int) * s.qPrevious

def rationalIntegerPart (r : RatCode) (j : Nat) : Int :=
  ((j : Int) * r.num) / (r.den : Int)
def rationalBox (r : RatCode) (N j : Nat) : Nat :=
  N * (((j : Int) * r.num) % (r.den : Int)).natAbs / r.den
def vectorBoxCode (rs : List RatCode) (N j : Nat) : Nat :=
  (rs.map (fun r => rationalBox r N j)).foldl
    (fun code digit => code * N + digit) 0
def firstCollision (codes : List Nat) : Option (Nat × Nat) :=
  let pairs := (List.range codes.length).flatMap
    (fun i => (List.range codes.length).map (fun j => (i, j)))
  pairs.find? (fun ij =>
    decide (ij.1 < ij.2) &&
    (codes.getD ij.1 0 == codes.getD ij.2 0))

def DirichletWitness (r : RatCode) (Q : Nat) (p : Int) (q : Nat) : Prop :=
  r.Valid ∧ 1 ≤ q ∧ q ≤ Q ∧
    (((q : Int) * r.num - p * (r.den : Int)).natAbs * Q < r.den)
def SimultaneousWitness
    (rs : List RatCode) (N : Nat) (ps : List Int) (q : Nat) : Prop :=
  ps.length = rs.length ∧ 1 ≤ q ∧ q ≤ N ^ rs.length ∧
  ∀ i < rs.length,
    let r := rs.getD i ⟨0, 1⟩
    r.Valid ∧
      (((q : Int) * r.num -
        ps.getD i 0 * (r.den : Int)).natAbs * N < r.den)

structure PellPair where
  x : Int
  y : Int
deriving DecidableEq, Repr
def pellNorm (D : Nat) (a : PellPair) : Int :=
  a.x * a.x - (D : Int) * a.y * a.y
def pellMul (D : Nat) (a b : PellPair) : PellPair :=
  ⟨a.x * b.x + (D : Int) * a.y * b.y, a.x * b.y + a.y * b.x⟩
def pellConjugate (a : PellPair) : PellPair := ⟨a.x, -a.y⟩
def pellPow (D : Nat) (a : PellPair) : Nat → PellPair
  | 0 => ⟨1, 0⟩
  | n + 1 => pellMul D (pellPow D a n) a

def pellC (D : Nat) : Nat := 4 * D + 2
def pellB (D : Nat) : Nat := 4 * (D + 1)
def pellK (D : Nat) : Nat := 2 * pellC D ^ 3
def pellU (D : Nat) : Nat := (pellB D + 1) ^ (pellK D + 1)
def pellH (D : Nat) : Nat := 4 * (D + 1) ^ 2 * (pellU D + 1) ^ 2
def pellStageBound (D : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pellB D * (pellStageBound D n + 1)

def BoundedNormPair (D Y p q : Nat) : Prop :=
  0 < p ∧ Y < q ∧ q ≤ pellB D * (Y + 1) ∧
  p ≤ D * (pellB D * (Y + 1)) + 1 ∧
  let m : Int := (p : Int) ^ 2 - (D : Int) * (q : Int) ^ 2
  m ≠ 0 ∧ m.natAbs < pellC D
def PellBoundSpec (D : Nat) : Prop :=
  2 ≤ D → ¬ IsSquare D →
    ∃ x ≤ pellH D, ∃ y ≤ pellH D,
      2 ≤ x ∧ 1 ≤ y ∧ x * x = 1 + D * y * y
def findPell (D : Nat) : Option (Nat × Nat) :=
  let candidates := (List.range (pellH D + 1)).flatMap
    (fun x => (List.range (pellH D + 1)).map (fun y => (x, y)))
  candidates.find? (fun xy =>
    decide (2 ≤ xy.1) && decide (1 ≤ xy.2) &&
    (xy.1 * xy.1 == 1 + D * xy.2 * xy.2))
def FundamentalPell (D : Nat) (u : PellPair) : Prop :=
  1 < u.x ∧ 0 < u.y ∧ pellNorm D u = 1 ∧
  ∀ a : PellPair, 0 < a.x → 0 < a.y → pellNorm D a = 1 → u.y ≤ a.y
def PellClassificationSpec (D : Nat) (u a : PellPair) : Prop :=
  FundamentalPell D u → 0 < a.x → 0 ≤ a.y → pellNorm D a = 1 →
    ∃ n ≤ a.y.natAbs, pellPow D u n = a

/- Required proofs, in dependency order:
  1. isqrt_spec and rational normalization/exact arithmetic.
  2. Pythagorean parameter recovery and the two bounded descent steps.
  3. cfStep determinant/growth invariants, rational tails and error formula.
  4. firstCollision correctness from finite Boolean pigeonhole.
  5. rationalBox inequalities; Dirichlet and simultaneous witness extraction.
  6. boundedNormPair_exists, including the essential strict lower bound q > Y.
  7. same_norm_residue_quotient_integral, quotient_norm_one,
     quotient_positive (positive and negative common norm separately).
  8. PellBoundSpec, findPell correctness, fundamental bounded search.
  9. pellNorm_mul, pellPow growth, quotient descent, classification.
 10. For each algorithm, a PR code and object-level iPRA derivation of the
     finite loop invariant. General Lean induction does not establish this
     object-language derivability proof.
-/

end NumberTheoryIPRA.DiophantineOutline
