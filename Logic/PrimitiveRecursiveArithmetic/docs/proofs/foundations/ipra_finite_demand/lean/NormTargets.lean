import Std

/-!
# Norm certificates: executable definitions and UNPROVED named targets

This file specifies exact rational coefficient-list arithmetic and a finite
determinant constructor. A definition `...Target : Prop` neither assumes nor
proves its proposition. There are no custom axioms or admitted proofs here.
The report supplies full human arguments and the dependency-ordered path to
native Lean proofs and then to embedded `Prf PRAAx` derivations.

Rat is used as a native specification carrier. The object-iPRA translation
must use explicit signed numerator/positive denominator codes and their
arithmetic proofs, not unrestricted host-Lean rational structures.
-/

namespace FiniteDemand.NormTargets

abbrev Polynomial := List Rat
abbrev Matrix := List (List Polynomial)
abbrev Point := Rat × Rat

def normalize : Polynomial → Polynomial
  | [] => []
  | a :: p =>
    let q := normalize p
    if q.isEmpty && a == 0 then [] else a :: q

def coeff (p : Polynomial) (i : Nat) : Rat := p[i]?.getD 0

def degree (p : Polynomial) : Nat := (normalize p).length - 1

def evaluate (p : Polynomial) (x : Rat) : Rat :=
  p.foldr (fun a b => a + x * b) 0

def add (p q : Polynomial) : Polynomial :=
  normalize ((List.range (max p.length q.length)).map
    (fun i => coeff p i + coeff q i))

def scale (c : Rat) (p : Polynomial) : Polynomial :=
  normalize (p.map (c * ·))

def multiply (p q : Polynomial) : Polynomial :=
  if p.isEmpty || q.isEmpty then []
  else normalize ((List.range (p.length + q.length - 1)).map fun k =>
    (List.range (k + 1)).foldl
      (fun s i => s + coeff p i * coeff q (k - i)) 0)

def power (p : Polynomial) : Nat → Polynomial
  | 0 => [1]
  | n + 1 => multiply (power p n) p

/-- All words of the displayed length over the finite alphabet. -/
def words (alphabet : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (words alphabet n).flatMap fun w =>
      (List.range alphabet).map fun a => a :: w

def isPermutation (n : Nat) (p : List Nat) : Bool :=
  p.length == n && p.eraseDups.length == n && p.all (fun i => i < n)

def inversions (p : List Nat) : Nat :=
  (List.range p.length).foldl (fun s i =>
    s + (List.range p.length).foldl (fun t j =>
      if i < j && p[i]?.getD 0 > p[j]?.getD 0 then t + 1 else t) 0) 0

def matrixEntry (M : Matrix) (r j : Nat) : Polynomial :=
  (M[r]?.getD [])[j]?.getD []

def determinantTerm (n : Nat) (M : Matrix) (p : List Nat) : Polynomial :=
  let product := (List.range n).foldl
    (fun v j => multiply v (matrixEntry M (p[j]?.getD 0) j)) [1]
  scale (if inversions p % 2 == 0 then 1 else -1) product

/-- A deliberately bounded determinant algorithm, with at most n^n candidates. -/
def determinant (n : Nat) (M : Matrix) : Polynomial :=
  ((words n n).filter (isPermutation n)).foldl
    (fun s p => add s (determinantTerm n M p)) []

structure Data where
  m : Nat
  f : Polynomial
  A : List Polynomial
  deriving Repr

def valid (c : Data) : Bool :=
  decide (2 ≤ c.m) && normalize c.f == c.f &&
  decide (1 ≤ degree c.f) && Nat.gcd c.m (degree c.f) == 1 &&
  c.A.length == c.m && c.A.all (fun p => normalize p == p) &&
  c.A.any (fun p => !p.isEmpty)

def weightedDegree (c : Data) : Nat :=
  c.A.zipIdx.foldl (fun w (p, i) =>
    if p.isEmpty then w else max w (c.m * degree p + degree c.f * i)) 0

/-- Columns represent multiplication by G in K[X,Y]/(Y^m-f). -/
def normMatrix (c : Data) : Matrix :=
  (List.range c.m).map fun r => (List.range c.m).map fun j =>
    let i := (r + c.m - j) % c.m
    multiply (c.A[i]?.getD []) (power c.f ((i + j) / c.m))

def normPolynomial (c : Data) : Polynomial :=
  determinant c.m (normMatrix c)

def evaluateG (c : Data) (x y : Rat) : Rat :=
  c.A.foldr (fun a b => evaluate a x + y * b) 0

def commonZero (c : Data) (p : Point) : Bool :=
  p.2 ^ c.m == evaluate c.f p.1 && evaluateG c p.1 p.2 == 0

def distinctPoints (points : List Point) : Bool :=
  points.eraseDups.length == points.length

def NormDegreeTarget : Prop :=
  ∀ c : Data, valid c = true →
    normPolynomial c ≠ [] ∧ degree (normPolynomial c) = weightedDegree c

def EvaluationRowTarget : Prop :=
  ∀ c : Data, valid c = true → ∀ x y : Rat,
    y ^ c.m = evaluate c.f x → ∀ j, j < c.m →
      (List.range c.m).foldl (fun s r =>
        s + y ^ r * evaluate (matrixEntry (normMatrix c) r j) x) 0 =
      evaluateG c x y * y ^ j

def FiberMultiplicityTarget : Prop :=
  ∀ c : Data, valid c = true → ∀ a : Rat, ∀ ys : List Rat,
    ys.eraseDups.length = ys.length →
    ys.all (fun b => commonZero c (a, b)) = true →
    ∃ q : Polynomial,
      normPolynomial c = multiply (power [-a, 1] ys.length) q

def FiniteZeroCountTarget : Prop :=
  ∀ c : Data, valid c = true → ∀ points : List Point,
    distinctPoints points = true → points.all (commonZero c) = true →
    points.length ≤ weightedDegree c

/-! ## General monic plane equations

`F` lists the m lower coefficients of Y^m + sum F_i(X)Y^i.
`G` lists the m coefficients of the already reduced function G.
The companion matrix implements multiplication by Y with the relation
Y^m = -sum F_i(X)Y^i; its powers thus implement monic Y reduction.
-/

structure PlaneData where
  m : Nat
  F : List Polynomial
  G : List Polynomial
  deriving Repr

def validPlane (c : PlaneData) : Bool :=
  decide (1 ≤ c.m) && c.F.length == c.m && c.G.length == c.m &&
  c.F.all (fun p => normalize p == p) &&
  c.G.all (fun p => normalize p == p)

def evaluateYList (ps : List Polynomial) (x y : Rat) : Rat :=
  ps.foldr (fun a b => evaluate a x + y * b) 0

def planeEquation (c : PlaneData) (x y : Rat) : Rat :=
  y ^ c.m + evaluateYList c.F x y

def companionMatrix (c : PlaneData) : Matrix :=
  (List.range c.m).map fun r => (List.range c.m).map fun j =>
    if j + 1 < c.m then (if r == j + 1 then [1] else [])
    else scale (-1) (c.F[r]?.getD [])

def zeroMatrix (n : Nat) : Matrix :=
  List.replicate n (List.replicate n [])

def identityMatrix (n : Nat) : Matrix :=
  (List.range n).map fun r => (List.range n).map fun j =>
    if r == j then [1] else []

def addMatrix (n : Nat) (M N : Matrix) : Matrix :=
  (List.range n).map fun r => (List.range n).map fun j =>
    add (matrixEntry M r j) (matrixEntry N r j)

def scaleMatrix (n : Nat) (p : Polynomial) (M : Matrix) : Matrix :=
  (List.range n).map fun r => (List.range n).map fun j =>
    multiply p (matrixEntry M r j)

def multiplyMatrix (n : Nat) (M N : Matrix) : Matrix :=
  (List.range n).map fun r => (List.range n).map fun j =>
    (List.range n).foldl (fun s k =>
      add s (multiply (matrixEntry M r k) (matrixEntry N k j))) []

def matrixPower (n : Nat) (M : Matrix) : Nat → Matrix
  | 0 => identityMatrix n
  | k + 1 => multiplyMatrix n (matrixPower n M k) M

/-- Reduce an arbitrary finite Y-coefficient list by the monic equation.
The first column of T^i represents Y^i modulo that equation. -/
def monicRemainder (c : PlaneData) (H : List Polynomial) : List Polynomial :=
  (List.range c.m).map fun r => H.zipIdx.foldl (fun s (a, i) =>
    add s (multiply a
      (matrixEntry (matrixPower c.m (companionMatrix c) i) r 0))) []

def MonicRemainderEvaluationTarget : Prop :=
  ∀ c : PlaneData, validPlane c = true → ∀ H : List Polynomial,
  ∀ x y : Rat, planeEquation c x y = 0 →
    evaluateYList (monicRemainder c H) x y = evaluateYList H x y

def planeNormMatrix (c : PlaneData) : Matrix :=
  (List.range c.m).foldl (fun s i =>
    addMatrix c.m s
      (scaleMatrix c.m (c.G[i]?.getD [])
        (matrixPower c.m (companionMatrix c) i))) (zeroMatrix c.m)

def planeNormPolynomial (c : PlaneData) : Polynomial :=
  determinant c.m (planeNormMatrix c)

def planeCommonZero (c : PlaneData) (p : Point) : Bool :=
  planeEquation c p.1 p.2 == 0 && evaluateYList c.G p.1 p.2 == 0

def PlaneEvaluationRowTarget : Prop :=
  ∀ c : PlaneData, validPlane c = true → ∀ x y : Rat,
    planeEquation c x y = 0 → ∀ j, j < c.m →
      (List.range c.m).foldl (fun s r =>
        s + y ^ r * evaluate (matrixEntry (planeNormMatrix c) r j) x) 0 =
      evaluateYList c.G x y * y ^ j

def PlaneFiberMultiplicityTarget : Prop :=
  ∀ c : PlaneData, validPlane c = true → ∀ a : Rat, ∀ ys : List Rat,
    ys.eraseDups.length = ys.length →
    ys.all (fun b => planeCommonZero c (a, b)) = true →
    ∃ q : Polynomial,
      planeNormPolynomial c = multiply (power [-a, 1] ys.length) q

/-- Main general theorem: nonvanishing is an explicit essential hypothesis. -/
def GeneralMonicZeroCountTarget : Prop :=
  ∀ c : PlaneData, validPlane c = true → planeNormPolynomial c ≠ [] →
  ∀ points : List Point,
    distinctPoints points = true → points.all (planeCommonZero c) = true →
    points.length ≤ degree (planeNormPolynomial c)

def maxCoefficientDegree (ps : List Polynomial) : Nat :=
  ps.foldl (fun d p => max d (degree p)) 0

def planeDegreeBound (c : PlaneData) : Nat :=
  c.m * (maxCoefficientDegree c.G + (c.m - 1) * maxCoefficientDegree c.F)

def GeneralNormDegreeBoundTarget : Prop :=
  ∀ c : PlaneData, validPlane c = true → planeNormPolynomial c ≠ [] →
    degree (planeNormPolynomial c) ≤ planeDegreeBound c

def asPlane (c : Data) : PlaneData :=
  {m := c.m, F := scale (-1) c.f :: List.replicate (c.m - 1) [], G := c.A}

def SuperellipticCompanionTarget : Prop :=
  ∀ c : Data, valid c = true →
    planeNormMatrix (asPlane c) = normMatrix c

/-! ## Proper-subspace fibers with finite annihilator and span certificates

These definitions use only lists, exact rational operations, and finite
checks. A nonzero annihilator is the certificate of properness. For each
point an explicit coefficient row certifies membership in the supplied span.
Producing these certificates by Gaussian elimination remains a separate
construction obligation in the report's formalization plan.
-/

structure CurveData where
  m : Nat
  f : Polynomial
  deriving Repr

def validCurve (c : CurveData) : Bool :=
  decide (2 ≤ c.m) && normalize c.f == c.f &&
  decide (1 ≤ degree c.f) && Nat.gcd c.m (degree c.f) == 1

/-- Pairs are (Y exponent, X exponent), ordered by the bounded loops. -/
def monomialBasis (c : CurveData) (L : Nat) : List (Nat × Nat) :=
  (List.range c.m).flatMap fun i =>
    ((List.range (L + 1)).filter (fun j => c.m * j + degree c.f * i ≤ L)).map
      (fun j => (i, j))

def evaluationVector (c : CurveData) (L : Nat) (p : Point) : List Rat :=
  (monomialBasis c L).map fun (i, j) => p.1 ^ j * p.2 ^ i

def dot (u v : List Rat) : Rat :=
  (List.range u.length).foldl
    (fun s i => s + (u[i]?.getD 0) * (v[i]?.getD 0)) 0

def rowCombination (n : Nat) (rows : List (List Rat))
    (coefficients : List Rat) : List Rat :=
  (List.range n).map fun j => (List.range rows.length).foldl (fun s i =>
    s + (coefficients[i]?.getD 0) * ((rows[i]?.getD [])[j]?.getD 0)) 0

def validAnnihilator (n : Nat) (rows : List (List Rat)) (a : List Rat) : Bool :=
  a.length == n && a.any (fun v => v != 0) &&
  rows.all (fun row => row.length == n && dot row a == 0)

def spanWitnesses (c : CurveData) (L : Nat) (rows : List (List Rat))
    (points : List Point) (witnesses : List (List Rat)) : Bool :=
  witnesses.length == points.length && points.zipIdx.all (fun (p, i) =>
    let coefficients := witnesses[i]?.getD []
    coefficients.length == rows.length &&
    rowCombination (monomialBasis c L).length rows coefficients ==
      evaluationVector c L p)

def SubspaceFiberTarget : Prop :=
  ∀ c : CurveData, validCurve c = true → ∀ L : Nat,
  ∀ (rows : List (List Rat)) (a : List Rat),
    validAnnihilator (monomialBasis c L).length rows a = true →
  ∀ (points : List Point) (witnesses : List (List Rat)),
    distinctPoints points = true →
    points.all (fun p => p.2 ^ c.m == evaluate c.f p.1) = true →
    spanWitnesses c L rows points witnesses = true → points.length ≤ L

/-- The sharp m=3, d=4 example with four common rational points. -/
def sharpExample : Data :=
  {m := 3, f := [1, -8, 14, -7, 1], A := [[-1], [1], []]}

#eval valid sharpExample
#eval normPolynomial sharpExample
#eval weightedDegree sharpExample
#eval [(0, 1), (1, 1), (2, 1), (4, 1)].all (commonZero sharpExample)

/-- F=Y(Y-1)(Y-2)-X and G=X: three common points in the same fiber. -/
def planeExample : PlaneData :=
  {m := 3, F := [[0, -1], [2], [-3]], G := [[0, 1], [], []]}

#eval validPlane planeExample
#eval planeNormPolynomial planeExample
#eval [(0, 0), (0, 1), (0, 2)].all (planeCommonZero planeExample)
#eval monicRemainder planeExample [[], [], [], [1]]

def sharpCurve : CurveData := {m := 3, f := sharpExample.f}
def sharpRows : List (List Rat) := [[1, 0, 1], [0, 1, 0]]
def sharpPoints : List Point := [(0, 1), (1, 1), (2, 1), (4, 1)]

#eval monomialBasis sharpCurve 4
#eval validAnnihilator 3 sharpRows [-1, 0, 1]
#eval spanWitnesses sharpCurve 4 sharpRows sharpPoints [[1, 0], [1, 1], [1, 2], [1, 4]]

end FiniteDemand.NormTargets
