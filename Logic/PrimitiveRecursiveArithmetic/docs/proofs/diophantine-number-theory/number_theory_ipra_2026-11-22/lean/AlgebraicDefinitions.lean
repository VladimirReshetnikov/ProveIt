/-
Numerical interfaces for the quadratic ring, finite Hensel lifting, and
partitions. STATUS: uncompiled blueprint. All goals are explicit propositions;
no theorem of this report is asserted without a proof term.
-/
import ElementaryDefinitions

namespace NumberTheoryIPRA.Algebraic
open NumberTheoryIPRA.Elementary

structure QuadraticPair where
  re : Int
  im : Int
  deriving DecidableEq, Repr

def quadraticMul (x y : QuadraticPair) : QuadraticPair :=
  { re := x.re * y.re - 5 * x.im * y.im,
    im := x.re * y.im + x.im * y.re }

def quadraticNorm (x : QuadraticPair) : Int := x.re ^ 2 + 5 * x.im ^ 2

def truncatedValuation (p k : Nat) (a : Int) : Nat :=
  ((List.range (k + 1)).filter
    (fun j => a % ((p ^ j : Nat) : Int) == 0)).foldl Nat.max 0

/-- Coefficients are in increasing order of degree. -/
def polynomialValue (cs : List Int) (x : Int) : Int :=
  cs.foldr (fun c a => c + x * a) 0

def derivativeCoefficients (cs : List Int) : List Int :=
  (cs.drop 1).zipWith (fun c i => c * ((i + 1 : Nat) : Int))
    (List.range (cs.length - 1))

def derivativeValue (cs : List Int) (x : Int) : Int :=
  polynomialValue (derivativeCoefficients cs) x

/-- One bounded digit scan. Failure returns the previous residue. -/
def henselStep (cs : List Int) (p k a : Nat) : Nat :=
  let digit := (List.range p).find? (fun t =>
    polynomialValue cs ((a + t * p ^ k : Nat) : Int) %
      ((p ^ (k + 1) : Nat) : Int) == 0)
  a + digit.getD 0 * p ^ k

/-- State stores its current precision and residue. -/
def henselStateStep (cs : List Int) (p : Nat) (s : Nat × Nat) : Nat × Nat :=
  (s.1 + 1, henselStep cs p s.1 s.2)

def henselName (cs : List Int) (p a firstAdditionalSteps : Nat) : Nat :=
  (iterate (henselStateStep cs p) firstAdditionalSteps (1, a % p)).2

def digitAt (base code i : Nat) : Nat := code / base ^ i % base

def partitionWeight (n code : Nat) : Nat :=
  (List.range n).foldl
    (fun a i => a + (i + 1) * digitAt (n + 1) code i) 0

def partitionCount (n : Nat) : Nat :=
  ((List.range ((n + 1) ^ n)).filter
    (fun c => partitionWeight n c == n)).length

def oddPartitionB (n c : Nat) : Bool :=
  (partitionWeight n c == n) && (List.range n).all
    (fun i => (i + 1) % 2 == 1 || digitAt (n + 1) c i == 0)

def distinctPartitionB (n c : Nat) : Bool :=
  (partitionWeight n c == n) && (List.range n).all
    (fun i => decide (digitAt (n + 1) c i ≤ 1))

def oddPartitionCount (n : Nat) : Nat :=
  ((List.range ((n + 1) ^ n)).filter (oddPartitionB n)).length

def distinctPartitionCount (n : Nat) : Nat :=
  ((List.range ((n + 1) ^ n)).filter (distinctPartitionB n)).length

structure AlgebraicGoals : Prop where
  normMultiplicative : ∀ x y : QuadraticPair,
    quadraticNorm (quadraticMul x y) = quadraticNorm x * quadraticNorm y
  hensel : ∀ (cs : List Int) (p k a : Nat), primeB p = true → 1 ≤ k →
    a < p ^ k → polynomialValue cs (a : Int) % ((p ^ k : Nat) : Int) = 0 →
    derivativeValue cs (a : Int) % (p : Int) ≠ 0 →
    let b := henselStep cs p k a
    b < p ^ (k + 1) ∧ b % p ^ k = a ∧
      polynomialValue cs (b : Int) % ((p ^ (k + 1) : Nat) : Int) = 0
  oddDistinct : ∀ n : Nat, oddPartitionCount n = distinctPartitionCount n

end NumberTheoryIPRA.Algebraic
