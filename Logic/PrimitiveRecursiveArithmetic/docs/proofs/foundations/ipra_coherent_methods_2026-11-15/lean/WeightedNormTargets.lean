import Std

/-!
# Exact rational polynomial programs and weighted-norm targets

Coefficients are low-degree-first finite lists.  A bivariate polynomial is a
list of X-polynomials, indexed by Y-degree.  All goals below are fully defined
propositions; no theorem or axiom is asserted for an uncompleted proof.
-/

namespace IPRAFramework.WeightedNorm

abbrev QPoly := List Rat
abbrev BPoly := List QPoly

def coeff (p : QPoly) (i : Nat) : Rat := p.getD i 0
def normalize (p : QPoly) : QPoly := (p.reverse.dropWhile fun a => a == 0).reverse
def nonzero (p : QPoly) : Bool := p.any fun a => a != 0

def polyAdd (p q : QPoly) : QPoly :=
  normalize ((List.range (max p.length q.length)).map fun i => coeff p i + coeff q i)

def polyNeg (p : QPoly) : QPoly := normalize (p.map Neg.neg)
def polySub (p q : QPoly) : QPoly := polyAdd p (polyNeg q)

def polyMul (p q : QPoly) : QPoly :=
  normalize ((List.range (p.length + q.length - 1)).map fun k =>
    ((List.range (k + 1)).map fun i => coeff p i * coeff q (k - i)).foldl (· + ·) 0)

def polyPower (p : QPoly) : Nat → QPoly
  | 0 => [1]
  | n + 1 => polyMul (polyPower p n) p

def mono (a : Rat) (n : Nat) : QPoly := normalize (List.replicate n 0 ++ [a])

def evaluate (p : QPoly) (x : Rat) : Rat := p.foldr (fun a rest => a + x * rest) 0

def polyEq (p q : QPoly) : Prop :=
  ∀ i, i < max p.length q.length → coeff p i = coeff q i

def degree (p : QPoly) : Nat :=
  (List.range p.length).foldl (fun best i => if coeff p i = 0 then best else max best i) 0

def divides (p q : QPoly) : Prop := ∃ r : QPoly, polyEq q (polyMul p r)

def row (p : BPoly) (j : Nat) : QPoly := p.getD j []

def bivariateEvaluate (p : BPoly) (x y : Rat) : Rat :=
  p.foldr (fun a rest => evaluate a x + y * rest) 0

def bivariateAdd (p q : BPoly) : BPoly :=
  (List.range (max p.length q.length)).map fun j => polyAdd (row p j) (row q j)

def shiftY (n : Nat) (p : BPoly) : BPoly := List.replicate n [] ++ p

def yDegree (p : BPoly) : Nat :=
  (List.range p.length).foldl (fun best j => if nonzero (row p j) then max best j else best) 0

def bivariateNonzero (p : BPoly) : Bool := p.any nonzero

structure Curve where
  m : Nat
  d : Nat
  c : Rat
  lower : BPoly

def Curve.assumptions (f : Curve) : Prop :=
  2 ≤ f.m ∧ 0 < f.d ∧ Nat.gcd f.m f.d = 1 ∧ f.c ≠ 0 ∧
  f.lower.length ≤ f.m ∧
    ∀ j, j < f.lower.length → ∀ i, i < (row f.lower j).length →
      coeff (row f.lower j) i ≠ 0 → f.m * i + f.d * j < f.m * f.d

def Curve.evaluate (f : Curve) (x y : Rat) : Rat :=
  y ^ f.m - f.c * x ^ f.d + bivariateEvaluate f.lower x y

/-- The explicit replacement for Y^m. -/
def Curve.relation (f : Curve) : BPoly :=
  (List.range f.m).map fun j =>
    if j = 0 then polySub (mono f.c f.d) (row f.lower 0)
    else polyNeg (row f.lower j)

/-- One removal of the highest Y coefficient, using monic division. -/
def reductionStep (f : Curve) (p : BPoly) : BPoly :=
  let j := yDegree p
  if f.m ≤ j && bivariateNonzero p then
    let a := row p j
    bivariateAdd (p.take j) (shiftY (j - f.m) (f.relation.map fun b => polyMul a b))
  else p

def reduceFuel (f : Curve) (p : BPoly) : Nat → BPoly
  | 0 => p
  | n + 1 => reductionStep f (reduceFuel f p n)

/-- `p.length` stages suffice under Curve.assumptions. -/
def reduce (f : Curve) (p : BPoly) : BPoly := reduceFuel f p p.length

def reduced (f : Curve) (g : BPoly) : Prop := g.length ≤ f.m

/-- Matrix rows are indexed by output coefficients; column j is rem(GY^j). -/
def multiplicationMatrix (f : Curve) (g : BPoly) : List (List QPoly) :=
  (List.range f.m).map fun i =>
    (List.range f.m).map fun j => row (reduce f (shiftY j g)) i

def matrixEntry (a : List (List QPoly)) (i j : Nat) : QPoly :=
  (a.getD i []).getD j []

/-- Division-free finite Laplace determinant, total on every list input. -/
def determinant : Nat → List (List QPoly) → QPoly
  | 0, _ => [1]
  | n + 1, a =>
      ((List.range (n + 1)).map fun j =>
        let t := polyMul (matrixEntry a 0 j)
          (determinant n (a.tail.map fun r => r.eraseIdx j))
        if j % 2 = 0 then t else polyNeg t).foldl polyAdd []

def norm (f : Curve) (g : BPoly) : QPoly :=
  determinant f.m (multiplicationMatrix f g)

def weight (f : Curve) (g : BPoly) : Nat :=
  (List.range g.length).foldl (fun best j =>
    (List.range (row g j).length).foldl (fun w i =>
      if coeff (row g j) i = 0 then w else max w (f.m * i + f.d * j)) best) 0

def leadingWitness (f : Curve) (g : BPoly) (i j : Nat) : Prop :=
  j < g.length ∧ i < (row g j).length ∧ coeff (row g j) i ≠ 0 ∧
    f.m * i + f.d * j = weight f g

def NormDegreeGoal : Prop :=
  ∀ f : Curve, f.assumptions → ∀ g : BPoly, reduced f g → bivariateNonzero g = true →
    nonzero (norm f g) = true ∧ degree (norm f g) = weight f g ∧
      ∀ i j, leadingWitness f g i j →
        coeff (norm f g) (weight f g) =
          (coeff (row g j) i) ^ f.m *
            (((if (f.m - 1) % 2 = 0 then (1 : Rat) else -1) * f.c) ^ j)

def FiberPowerGoal : Prop :=
  ∀ f : Curve, f.assumptions → ∀ g : BPoly, reduced f g →
    ∀ (u : Rat) (vs : List Rat), vs.Pairwise (· ≠ ·) →
      (∀ v, v ∈ vs → f.evaluate u v = 0 ∧ bivariateEvaluate g u v = 0) →
      divides (polyPower [-u, 1] vs.length) (norm f g)

def CommonZerosGoal : Prop :=
  ∀ f : Curve, f.assumptions → ∀ g : BPoly, reduced f g → bivariateNonzero g = true →
    ∀ ps : List (Rat × Rat), ps.Pairwise (· ≠ ·) →
      (∀ p, p ∈ ps → f.evaluate p.1 p.2 = 0 ∧ bivariateEvaluate g p.1 p.2 = 0) →
      ps.length ≤ weight f g

def weightedBasis (m d L : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun j =>
    ((List.range (L + 1)).filter fun i => m * i + d * j ≤ L).map fun i => (i, j)

def dimensionCount (m d L : Nat) : Nat :=
  ((List.range m).map fun j => if d * j ≤ L then 1 + (L - d * j) / m else 0).foldl (· + ·) 0

def WeightedBasisCountGoal : Prop :=
  ∀ m d L, 0 < m → (weightedBasis m d L).length = dimensionCount m d L

def EventualDimensionGoal : Prop :=
  ∀ m d L, 2 ≤ m → 0 < d → Nat.gcd m d = 1 → m * d - m - d ≤ L →
    dimensionCount m d L = L + 1 - ((m - 1) * (d - 1) / 2)

end IPRAFramework.WeightedNorm
