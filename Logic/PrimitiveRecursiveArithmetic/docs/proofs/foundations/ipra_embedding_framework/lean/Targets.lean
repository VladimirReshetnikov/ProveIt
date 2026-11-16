import Std

/-!
# Concrete definitions and unproved targets

This file is compiler-checked, but its `...Target` declarations are definitions
of propositions, not proofs of those propositions. No `axiom` or `sorry` is
used to turn a mathematical obligation into an asserted theorem.
Rationals here are native Lean rationals. The object-theory phase must replace
them by natural codes and construct `Prf PRAAx` derivations.
-/

namespace IPRAEmbedding.Targets

abbrev QPoly := List Rat

def qabs (x : Rat) : Rat := if x < 0 then -x else x
def dyadic (k : Nat) : Rat := 1 / (2 : Rat) ^ k
def coeff (p : QPoly) (i : Nat) : Rat := p[i]?.getD 0
def nonzero (p : QPoly) : Bool := p.any (fun c => c != 0)

/-- Actual degree for nonzero polynomials, and zero for the zero polynomial. -/
def degree (p : QPoly) : Nat :=
  p.zipIdx.foldl (fun d ci => if ci.1 == 0 then d else max d ci.2) 0

def eval (p : QPoly) (x : Rat) : Rat := p.foldr (fun c v => c + x * v) 0

def add (p q : QPoly) : QPoly :=
  (List.range (max p.length q.length)).map (fun i => coeff p i + coeff q i)

def neg (p : QPoly) : QPoly := p.map (- ·)
def sub (p q : QPoly) : QPoly := add p (neg q)

def mul (p q : QPoly) : QPoly :=
  (List.range (p.length + q.length)).map fun k =>
    ((List.range (k + 1)).map (fun i => coeff p i * coeff q (k - i))).foldl (· + ·) 0

def pow (p : QPoly) : Nat → QPoly
  | 0 => [1]
  | n + 1 => mul (pow p n) p

def weightedNorm (r : Rat) (p : QPoly) : Rat :=
  (p.zipIdx.map (fun ci => qabs ci.1 * r ^ ci.2)).foldl (· + ·) 0

abbrev QPoint := Rat × Rat

def distinctPoints (points : List QPoint) : Bool := decide points.Nodup

def curveZeros (f A B : QPoly) (points : List QPoint) : Bool :=
  points.all fun p =>
    (p.2 * p.2 == eval f p.1) && (eval A p.1 + eval B p.1 * p.2 == 0)

def normPolynomial (f A B : QPoly) : QPoly := sub (mul A A) (mul f (mul B B))

def HyperellipticFiberTarget : Prop :=
  ∀ f A B points,
    nonzero f = true → degree f % 2 = 1 →
    (nonzero A || nonzero B) = true →
    distinctPoints points = true → curveZeros f A B points = true →
    points.length ≤ degree (normPolynomial f A B)

/-- One finite term c X^i Z^j. The list may contain repeated monomials. -/
structure BiTerm where
  c : Rat
  xDegree : Nat
  zDegree : Nat

abbrev BiPoly := List BiTerm

def biCoeff (q : BiPoly) (i j : Nat) : Rat :=
  (q.map (fun t => if t.xDegree == i && t.zDegree == j then t.c else 0)).foldl (· + ·) 0

def substitute (q : BiPoly) (u : QPoly) : QPoly :=
  q.foldl (fun acc t => add acc
    (List.replicate t.xDegree 0 ++ (pow u t.zDegree).map (fun c => t.c * c))) []

/-- All iterations take place in the finite ring Q[X]/(X^(K+1)). -/
def truncatedIter (q : BiPoly) (K : Nat) : Nat → QPoly
  | 0 => []
  | n + 1 => (substitute q (truncatedIter q K n)).take (K + 1)

def coefficient (q : BiPoly) (k : Nat) : Rat := coeff (truncatedIter q k k) k

def ImplicitCoefficientStabilityTarget : Prop :=
  ∀ q K n j,
    biCoeff q 0 0 = 0 → biCoeff q 0 1 = 0 →
    K ≤ n → j ≤ K →
    coeff (truncatedIter q K n) j = coefficient q j

abbrev QName := Nat → Rat

/-- This is a semantic unbounded contract, never an induction predicate. -/
def Regular (a : QName) : Prop :=
  ∀ p q, qabs (a p - a q) ≤ dyadic p + dyadic q

def finiteRegular (a : QName) (N : Nat) : Bool :=
  (List.range (N + 1)).all fun p =>
    (List.range (N + 1)).all fun q =>
      decide (qabs (a p - a q) ≤ dyadic p + dyadic q)

def variation (a : QName) (T : Nat) : Rat :=
  ((List.range T).map (fun t => qabs (a (t + 1) - a t))).foldl (· + ·) 0

def stableWindow (a : QName) (start width : Nat) (eps : Rat) : Bool :=
  (List.range (width + 1)).all fun i =>
    (List.range (width + 1)).all fun j =>
      decide (qabs (a (start + i) - a (start + j)) ≤ eps)

def endpoint (g : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | i + 1 => endpoint g start i + g (endpoint g start i) + 1

/-- A single-component specialization of the paper's simultaneous theorem. -/
def FiniteVariationTarget : Prop :=
  ∀ (a : QName) (g : Nat → Nat) (start budget : Nat) (eps : Rat),
    0 < eps →
    variation a (endpoint g start (budget + 1)) < ((budget + 1 : Nat) : Rat) * eps →
    ∃ i, i ≤ budget ∧ stableWindow a (endpoint g start i)
      (g (endpoint g start i)) eps = true

def biAdd (p q : BiPoly) : BiPoly := p ++ q
def biScale (c : Rat) (p : BiPoly) : BiPoly := p.map (fun t => { t with c := c * t.c })
def biMul (p q : BiPoly) : BiPoly :=
  p.flatMap fun a => q.map fun b =>
    ⟨a.c * b.c, a.xDegree + b.xDegree, a.zDegree + b.zDegree⟩

def biEqual (p q : BiPoly) : Bool :=
  let both := p ++ q
  let dx := both.foldl (fun n t => max n t.xDegree) 0
  let dy := both.foldl (fun n t => max n t.zDegree) 0
  (List.range (dx + 1)).all fun i =>
    (List.range (dy + 1)).all fun j => biCoeff p i j == biCoeff q i j

def biEval (p : BiPoly) (x y : Rat) : Rat :=
  (p.map (fun t => t.c * x ^ t.xDegree * y ^ t.zDegree)).foldl (· + ·) 0

def biCombination (cs : List Rat) (basis : List BiPoly) : BiPoly :=
  (List.range basis.length).foldl
    (fun acc i => biAdd acc (biScale (cs[i]?.getD 0) (basis[i]?.getD []))) []

def idealCombination (us equations : List BiPoly) : BiPoly :=
  (List.range equations.length).foldl
    (fun acc i => biAdd acc (biMul (us[i]?.getD []) (equations[i]?.getD []))) []

/-- Two-variable instance; all fields are finite data, with no proof assumptions. -/
structure BiSpanningCertificate where
  basis : List BiPoly
  rowsX : List (List Rat)
  rowsY : List (List Rat)
  witnessesX : List (List BiPoly)
  witnessesY : List (List BiPoly)

def checkBorders (coordinate : BiPoly) (equations basis : List BiPoly)
    (rows : List (List Rat)) (witnesses : List (List BiPoly)) : Bool :=
  let d := basis.length
  (rows.length == d) && (witnesses.length == d) &&
  rows.all (fun row => row.length == d) &&
  witnesses.all (fun us => us.length == equations.length) &&
  (List.range d).all fun j =>
    biEqual (biMul coordinate (basis[j]?.getD []))
      (biAdd (biCombination (rows[j]?.getD []) basis)
        (idealCombination (witnesses[j]?.getD []) equations))

def checkSpanning (equations : List BiPoly) (c : BiSpanningCertificate) : Bool :=
  (c.basis.length > 0) && biEqual (c.basis[0]?.getD []) [⟨1, 0, 0⟩] &&
  checkBorders [⟨1, 1, 0⟩] equations c.basis c.rowsX c.witnessesX &&
  checkBorders [⟨1, 0, 1⟩] equations c.basis c.rowsY c.witnessesY

def commonBiZeros (equations : List BiPoly) (points : List QPoint) : Bool :=
  points.all (fun p => equations.all (fun f => biEval f p.1 p.2 == 0))

def FiniteAlgebraTarget : Prop :=
  ∀ equations c points,
    checkSpanning equations c = true →
    distinctPoints points = true → commonBiZeros equations points = true →
    points.length ≤ c.basis.length

end IPRAEmbedding.Targets
