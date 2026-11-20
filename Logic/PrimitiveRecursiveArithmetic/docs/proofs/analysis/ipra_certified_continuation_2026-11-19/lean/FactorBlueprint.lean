import Mathlib

/-!
# Finite rational factor-transport blueprint

UNCOMPILED host reference. All algorithms are explicit finite definitions.
The Prop-valued obligations at the end are NOT asserted or instantiated.
This file supplies neither a new axiom nor an embedded-iPRA proof.

The coefficient list [c0,c1,...] represents c0+c1*X+... . Trailing zero
coefficients are permitted; equality is coefficient equality, not list identity.
This file covers the rational case of the report. A Gaussian-rational port
uses the same list programs and the rational l1 norm on each coefficient.
-/

namespace FactorBlueprint

abbrev Polynomial := List ℚ
abbrev Matrix := List (List ℚ)

def coeff : Polynomial → Nat → ℚ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: p, n+1 => coeff p n

def matrixRow : Matrix → Nat → List ℚ
  | [], _ => []
  | a :: _, 0 => a
  | _ :: A, n+1 => matrixRow A n

def matrixEntry (A : Matrix) (i j : Nat) : ℚ := coeff (matrixRow A i) j

def tabulate (n : Nat) (f : Nat → ℚ) : List ℚ := (List.range n).map f

def add (p q : Polynomial) : Polynomial :=
  tabulate (max p.length q.length) (fun i => coeff p i + coeff q i)

def sub (p q : Polynomial) : Polynomial :=
  tabulate (max p.length q.length) (fun i => coeff p i - coeff q i)

def multiply (p q : Polynomial) : Polynomial :=
  if p.isEmpty || q.isEmpty then [] else
    tabulate (p.length+q.length-1) (fun k =>
      ((List.range (k+1)).map (fun i => coeff p i * coeff q (k-i))).sum)

def eval (p : Polynomial) (x : ℚ) : ℚ :=
  ((List.range p.length).map (fun i => coeff p i * x^i)).sum

def norm1 (p : Polynomial) : ℚ := (p.map abs).sum

def coefficientEq (p q : Polynomial) : Prop := ∀ i, coeff p i = coeff q i

def coefficientEqBit (p q : Polynomial) : Bool :=
  (List.range (max p.length q.length)).all (fun i => decide (coeff p i = coeff q i))

def matrixShape (A : Matrix) (d : Nat) : Bool :=
  decide (A.length = d) && A.all (fun row => decide (row.length = d))

def matrixProduct (d : Nat) (A B : Matrix) : Matrix :=
  (List.range d).map (fun i => tabulate d (fun j =>
    ((List.range d).map (fun k => matrixEntry A i k * matrixEntry B k j)).sum))

def matrixVector (d : Nat) (A : Matrix) (x : List ℚ) : List ℚ :=
  tabulate d (fun i =>
    ((List.range d).map (fun j => matrixEntry A i j * coeff x j)).sum)

def identity (d : Nat) : Matrix :=
  (List.range d).map (fun i => tabulate d (fun j => if i = j then 1 else 0))

def matrixEqBit (d : Nat) (A B : Matrix) : Bool :=
  (List.range d).all (fun i => (List.range d).all (fun j =>
    decide (matrixEntry A i j = matrixEntry B i j)))

def columnNorm (d : Nat) (A : Matrix) : ℚ :=
  ((List.range d).map (fun j =>
    ((List.range d).map (fun i => |matrixEntry A i j|)).sum)).foldl max 0

def monicBit (degree : Nat) (p : Polynomial) : Bool :=
  decide (p.length = degree+1) && decide (coeff p degree = 1)

/-- Matrix of (u,v) ↦ h0*u+g0*v, with deg u<r and deg v<s. -/
def sylvester (r s : Nat) (g0 h0 : Polynomial) : Matrix :=
  (List.range (r+s)).map (fun i => tabulate (r+s) (fun j =>
    if j < r then
      if j ≤ i then coeff h0 (i-j) else 0
    else
      let t := j-r
      if t ≤ i then coeff g0 (i-t) else 0))

structure Input where
  r : Nat
  s : Nat
  g0 : Polynomial
  h0 : Polynomial
  target : Polynomial
  S : Matrix
  radius : ℚ

def dimension (c : Input) : Nat := c.r+c.s

def linearMap (c : Input) : Matrix := sylvester c.r c.s c.g0 c.h0

def amplification (c : Input) : ℚ := max 1 (columnNorm (dimension c) c.S)

def forwardAmplification (c : Input) : ℚ := columnNorm (dimension c) (linearMap c)

def fullError (c : Input) : Polynomial := sub c.target (multiply c.g0 c.h0)

def errorSize (c : Input) : ℚ := norm1 (fullError c)

def errorVector (c : Input) : List ℚ :=
  tabulate (dimension c) (fun i => coeff (fullError c) i)

def firstCorrection (c : Input) (z : List ℚ) : Polynomial :=
  tabulate c.r (fun i => coeff z i)

def secondCorrection (c : Input) (z : List ℚ) : Polynomial :=
  tabulate c.s (fun i => coeff z (c.r+i))

def update (c : Input) (z : List ℚ) : List ℚ :=
  matrixVector (dimension c) c.S
    (sub (errorVector c) (multiply (firstCorrection c z) (secondCorrection c z)))

def iterate (c : Input) : Nat → List ℚ
  | 0 => tabulate (dimension c) (fun _ => 0)
  | n+1 => update c (iterate c n)

def factorsAt (c : Input) (n : Nat) : Polynomial × Polynomial :=
  (add c.g0 (firstCorrection c (iterate c n)),
   add c.h0 (secondCorrection c (iterate c n)))

def residual (c : Input) (n : Nat) : Polynomial :=
  let gh := factorsAt c n
  sub c.target (multiply gh.1 gh.2)

def certificateBit (c : Input) : Bool :=
  decide (0 < c.r) && decide (0 < c.s) && decide (0 < c.radius) &&
  monicBit c.r c.g0 && monicBit c.s c.h0 && monicBit (dimension c) c.target &&
  matrixShape c.S (dimension c) &&
  matrixEqBit (dimension c) (matrixProduct (dimension c) c.S (linearMap c))
    (identity (dimension c)) &&
  matrixEqBit (dimension c) (matrixProduct (dimension c) (linearMap c) c.S)
    (identity (dimension c)) &&
  decide (amplification c * c.radius ≤ (1/4 : ℚ)) &&
  decide (amplification c * errorSize c ≤ c.radius/2)

def Accepted (c : Input) : Prop := certificateBit c = true

def suggestedRadius (c : Input) : ℚ := 1/(4*amplification c)

def dyadicShift (q : ℚ) : Nat :=
  let J := max 1 (Int.toNat ⌈q⌉)
  ((List.range (J+1)).find? (fun k => decide (q ≤ (2 : ℚ)^k))).getD J

def nameClock (c : Input) (p : Nat) : Nat :=
  p + dyadicShift (max 1 (max
    (2*amplification c*errorSize c)
    (forwardAmplification c*amplification c*errorSize c))) + 2

def factorNames (c : Input) (p : Nat) : Polynomial × Polynomial :=
  factorsAt c (nameClock c p)

/-! ## Proof statements: explicitly uninhabited obligations -/

def ConvolutionCorrect : Prop :=
  ∀ (p q : Polynomial) (x : ℚ), eval (multiply p q) x = eval p x * eval q x

def ProductNormCorrect : Prop :=
  ∀ p q : Polynomial, norm1 (multiply p q) ≤ norm1 p * norm1 q

def CoefficientCheckCorrect : Prop :=
  ∀ p q : Polynomial, coefficientEqBit p q = true ↔ coefficientEq p q

def MatrixNormCorrect : Prop :=
  ∀ (d : Nat) (A : Matrix) (x : List ℚ), matrixShape A d = true → x.length = d →
    norm1 (matrixVector d A x) ≤ columnNorm d A * norm1 x

def SylvesterCorrect : Prop :=
  ∀ (c : Input) (z : List ℚ),
    monicBit c.r c.g0 = true → monicBit c.s c.h0 = true → z.length = dimension c →
    coefficientEq (matrixVector (dimension c) (linearMap c) z)
      (add (multiply c.h0 (firstCorrection c z)) (multiply c.g0 (secondCorrection c z)))

def DomainCorrect : Prop :=
  ∀ (c : Input), Accepted c → ∀ z : List ℚ, z.length = dimension c → norm1 z ≤ c.radius →
    (update c z).length = dimension c ∧ norm1 (update c z) ≤ 3*c.radius/4

def GainCorrect : Prop :=
  ∀ (c : Input), Accepted c → ∀ z w : List ℚ,
    z.length = dimension c → w.length = dimension c → norm1 z ≤ c.radius → norm1 w ≤ c.radius →
    norm1 (sub (update c z) (update c w)) ≤ (1/4 : ℚ) * norm1 (sub z w)

def ResidualIdentityCorrect : Prop :=
  ∀ (c : Input), Accepted c → ∀ n,
    coefficientEq (residual c n)
      (matrixVector (dimension c) (linearMap c) (sub (iterate c (n+1)) (iterate c n)))

def FiniteBounds (c : Input) : Prop :=
  (∀ n, (iterate c n).length = dimension c ∧ norm1 (iterate c n) ≤ c.radius) ∧
  (∀ n, norm1 (sub (iterate c (n+1)) (iterate c n)) ≤
    amplification c * errorSize c * (1/2 : ℚ)^n) ∧
  (∀ n j, norm1 (sub (iterate c (n+j)) (iterate c n)) ≤
    2*amplification c*errorSize c * (1/2 : ℚ)^n) ∧
  (∀ n, norm1 (residual c n) ≤
    forwardAmplification c*amplification c*errorSize c * (1/2 : ℚ)^n)

def FiniteBoundsCorrect : Prop := ∀ c : Input, Accepted c → FiniteBounds c

def NameCorrect : Prop :=
  ∀ (c : Input), Accepted c →
    (∀ p q, p ≤ q →
      norm1 (sub (factorNames c p).1 (factorNames c q).1) +
      norm1 (sub (factorNames c p).2 (factorNames c q).2) ≤ (1/2 : ℚ)^(p+2)) ∧
    (∀ p, norm1 (sub c.target (multiply (factorNames c p).1 (factorNames c p).2)) ≤
      (1/2 : ℚ)^(p+2))

def TargetStabilityCorrect : Prop :=
  ∀ (c : Input) (f : Polynomial),
    Accepted c → Accepted { c with target := f } → ∀ n,
    norm1 (sub (iterate c n) (iterate { c with target := f } n)) ≤
      2*amplification c * norm1 (sub c.target f)

structure ProofObligations : Prop where
  convolution : ConvolutionCorrect
  product_norm : ProductNormCorrect
  coefficient_check : CoefficientCheckCorrect
  matrix_norm : MatrixNormCorrect
  sylvester : SylvesterCorrect
  domain : DomainCorrect
  gain : GainCorrect
  residual_identity : ResidualIdentityCorrect
  finite_bounds : FiniteBoundsCorrect
  name : NameCorrect
  target_stability : TargetStabilityCorrect

/-- Report example: X^2(X-2)^2+1/100, near factors X^2 and (X-2)^2. -/
def exampleInput : Input where
  r := 2
  s := 2
  g0 := [0,0,1]
  h0 := [4,-4,1]
  target := [1/100,0,4,-4,1]
  S := [[1/4,0,0,0], [1/4,1/4,0,0], [3/4,1,1,0], [-1/4,-1/4,0,1]]
  radius := 1/6

-- Expected values: true and the first corrections displayed in the report.
#eval certificateBit exampleInput
#eval iterate exampleInput 1

end FactorBlueprint
