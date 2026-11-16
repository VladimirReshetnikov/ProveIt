import RationalRoots

/-!
# Concrete plane-elimination programs and unproved correctness targets

All definitions below are executable finite data operations. The declarations
whose names end in `Target` are **propositions awaiting proofs**, not theorems,
axioms, or trusted kernel assumptions. This module contains no `sorry`.

The intended arithmetic implementation uses natural-number codes for these
lists and normalized rationals. Native Lean termination is not itself a proof
of primitive recursiveness or an object-iPRA derivation. The article supplies
the human arguments and the explicit finite bounds needed for that next step.

The `A : QPoint → Bool` argument in the envelope construction represents one
fixed predicate with a separately supplied PR program; no universal evaluator
for arbitrary semantic Lean functions is intended.
-/

namespace IPRAFramework.Elimination

open IPRAFramework.RationalRoots

abbrev Poly1 := QPoly
abbrev Poly2 := PlanePoly
abbrev Point := QPoint
abbrev eval1 := IPRAFramework.RationalRoots.eval
abbrev eval2 := IPRAFramework.RationalRoots.evalPlane

def coeff1 (p : Poly1) (i : Nat) : Rat := p.getD i 0
def coeff2 (p : Poly2) (i j : Nat) : Rat := coeff1 (p.getD i []) j

def nonzero1 (p : Poly1) : Bool := p.any (fun a => a != 0)
def nonzero2 (p : Poly2) : Bool := p.any nonzero1

def totalDegree (p : Poly2) : Nat :=
  p.zipIdx.foldl (fun bound row =>
    row.1.zipIdx.foldl (fun bound' cell =>
      if cell.1 == 0 then bound' else max bound' (row.2 + cell.2)) bound) 0

def positivePlane (p : Poly2) : Bool := nonzero2 p && totalDegree p > 0
def constantNonzero (p : Poly2) : Bool := nonzero2 p && totalDegree p == 0

def coeffEq1 (p q : Poly1) : Prop := ∀ i, coeff1 p i = coeff1 q i
def coeffEq2 (p q : Poly2) : Prop := ∀ i j, coeff2 p i j = coeff2 q i j

def add1 (p q : Poly1) : Poly1 :=
  (List.range (max p.length q.length)).map (fun i => coeff1 p i + coeff1 q i)

def scale1 (a : Rat) (p : Poly1) : Poly1 := p.map (fun b => a * b)

def mul1 (p q : Poly1) : Poly1 :=
  (List.range (p.length + q.length)).map (fun k =>
    (List.range p.length).foldl (fun total i =>
      if i ≤ k then total + coeff1 p i * coeff1 q (k - i) else total) 0)

def pow1 (p : Poly1) : Nat → Poly1
  | 0 => [1]
  | n + 1 => mul1 p (pow1 p n)

/-- Pascal recursion, included so every finite formula is concrete. -/
def choose : Nat → Nat → Nat
  | 0, k => if k == 0 then 1 else 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Coefficient of U^a V^b in F(U-cV,V), by the binomial formula. -/
def shearCoeff (F : Poly2) (c a b : Nat) : Rat :=
  F.zipIdx.foldl (fun total row =>
    row.1.zipIdx.foldl (fun subtotal cell =>
      if a ≤ row.2 ∧ b = cell.2 + (row.2 - a) then
        subtotal + cell.1 * (choose row.2 a : Rat) * (-(c : Rat)) ^ (row.2 - a)
      else subtotal) total) 0

def shear (F : Poly2) (c : Nat) : Poly2 :=
  let bound := totalDegree F + 1
  (List.range bound).map (fun a =>
    (List.range bound).map (fun b => shearCoeff F c a b))

def goodShear (F G : Poly2) (c : Nat) : Bool :=
  coeff2 (shear F c) 0 (totalDegree F) != 0 &&
  coeff2 (shear G c) 0 (totalDegree G) != 0

def canonicalShear (F G : Poly2) : Nat :=
  ((List.range (totalDegree F + totalDegree G + 1)).find? (goodShear F G)).getD 0

/-- The coefficient of V^j, as a polynomial in U. -/
def vCoefficient (F : Poly2) (j : Nat) : Poly1 :=
  F.map (fun row => coeff1 row j)

abbrev PolyMatrix := List (List Poly1)

/-- Rows are F,VF,...,V^(e-1)F followed by G,VG,...,V^(d-1)G;
columns are coefficients of V^0,...,V^(d+e-1). -/
def sylvester (F G : Poly2) (c : Nat) : PolyMatrix :=
  let d := totalDegree F
  let e := totalDegree G
  let Fc := shear F c
  let Gc := shear G c
  let rowOf := fun (p : Poly2) (shift : Nat) =>
    (List.range (d + e)).map (fun column =>
      if shift ≤ column then vCoefficient p (column - shift) else [])
  (List.range e).map (rowOf Fc) ++ (List.range d).map (rowOf Gc)

/-- All length-n vectors over a supplied finite alphabet. -/
def vectors {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun a => (vectors alphabet n).map (a :: ·))

/-- A bounded N^N scan, followed by a distinctness test. -/
def permutations (n : Nat) : List (List Nat) :=
  (vectors (List.range n) n).filter (fun xs => xs.eraseDups.length == n)

def inversionCount (xs : List Nat) : Nat :=
  xs.zipIdx.foldl (fun total left =>
    xs.zipIdx.foldl (fun subtotal right =>
      if left.2 < right.2 ∧ right.1 < left.1 then subtotal + 1 else subtotal) total) 0

def permutationSign (xs : List Nat) : Rat :=
  if inversionCount xs % 2 == 0 then 1 else -1

def matrixEntry (M : PolyMatrix) (i j : Nat) : Poly1 :=
  (M.getD i []).getD j []

def determinantTerm (M : PolyMatrix) (p : List Nat) : Poly1 :=
  scale1 (permutationSign p)
    ((List.range M.length).foldl (fun product i =>
      mul1 product (matrixEntry M i (p.getD i 0))) [1])

def determinant (M : PolyMatrix) : Poly1 :=
  (permutations M.length).foldl (fun total p => add1 total (determinantTerm M p)) []

def resultantAt (F G : Poly2) (c : Nat) : Poly1 := determinant (sylvester F G c)
def elimination (F G : Poly2) : Poly1 := resultantAt F G (canonicalShear F G)

/-- Strict positive-degree guard. Constant inputs are handled separately by
`intersect`, and are not silently included in this predicate. -/
def good (F G : Poly2) : Bool :=
  positivePlane F && positivePlane G && nonzero1 (elimination F G)

def Good (F G : Poly2) : Prop := good F G = true

def ySupportBound (F : Poly2) : Nat := F.foldl (fun bound row => max bound row.length) 0

def specializeU (F : Poly2) (u : Rat) : Poly1 :=
  (List.range (ySupportBound F)).map (fun j => eval1 (vCoefficient F j) u)

def common (F G : Poly2) (p : Point) : Prop :=
  eval2 F p.1 p.2 = 0 ∧ eval2 G p.1 p.2 = 0

/-- `none` denotes unsupported, not a proved empty solution set. The
nonzero-constant branch legitimately returns `some []`. -/
def intersect (F G : Poly2) : Option (List Point) :=
  if constantNonzero F || constantNonzero G then some []
  else if good F G then
    let c := canonicalShear F G
    let Fc := shear F c
    let Gc := shear G c
    let rootsU := (rationalRoots (elimination F G)).getD []
    let points := rootsU.flatMap (fun u =>
      ((rationalRoots (specializeU Fc u)).getD []).filterMap (fun v =>
        if eval2 Gc u v == 0 then some (u - (c : Rat) * v, v) else none))
    some points.eraseDups
  else none

def pointHeight (p : Point) : Nat := max (rationalHeight p.1) (rationalHeight p.2)
def pointListHeight (points : List Point) : Nat :=
  points.foldl (fun bound p => max bound (pointHeight p)) 0

/-- Positions of total degree at most e, ordered first by X degree. -/
def monomials (e : Nat) : List (Nat × Nat) :=
  (List.range (e + 1)).flatMap (fun i =>
    ((List.range (e + 1)).filter (fun j => i + j ≤ e)).map (fun j => (i, j)))

def vectorCoefficient (positions : List (Nat × Nat)) (values : List Rat)
    (i j : Nat) : Rat :=
  (positions.zip values).foldl (fun total entry =>
    if entry.1 == (i, j) then total + entry.2 else total) 0

def polynomialOfVector (e : Nat) (values : List Rat) : Poly2 :=
  let positions := monomials e
  (List.range (e + 1)).map (fun i =>
    (List.range (e + 1)).map (fun j => vectorCoefficient positions values i j))

/-- Raw candidates may contain duplicates, which only improve the upper
bound. Positive-degree candidates alone are relevant for the main theorem. -/
def auxiliaryBox (e H : Nat) : List Poly2 :=
  ((vectors (candidateBox H H) (monomials e).length).map
    (polynomialOfVector e)).filter positivePlane

def coefficientEnvelope (G : Poly2) (e H : Nat) : Prop :=
  totalDegree G ≤ e ∧ ∀ i j,
    (coeff2 G i j).num.natAbs ≤ H ∧ (coeff2 G i j).den ≤ H

def pointPredicate (F : Poly2) (A : Point → Bool) (p : Point) : Prop :=
  eval2 F p.1 p.2 = 0 ∧ A p = true

def pointwiseBoundedAux (F : Poly2) (A : Point → Bool) (e H : Nat) : Prop :=
  ∀ p, pointPredicate F A p →
    ∃ G, G ∈ auxiliaryBox e H ∧ Good F G ∧ eval2 G p.1 p.2 = 0

def envelopeList (F : Poly2) (A : Point → Bool) (e H : Nat) : List Point :=
  (((auxiliaryBox e H).filter (fun G => good F G)).flatMap
    (fun G => (intersect F G).getD [])).filter A |>.eraseDups

/-! ## Unproved targets: these are definitions of propositions only. -/

def ShearEvalTarget : Prop :=
  ∀ F c u v, eval2 (shear F c) u v = eval2 F (u - (c : Rat) * v) v

def CanonicalShearTarget : Prop :=
  ∀ F G, positivePlane F = true → positivePlane G = true →
    canonicalShear F G ≤ totalDegree F + totalDegree G ∧
    goodShear F G (canonicalShear F G) = true

def ResultantDegreeTarget : Prop :=
  ∀ F G c, positivePlane F = true → positivePlane G = true →
    goodShear F G c = true →
    degree (resultantAt F G c) ≤ totalDegree F * totalDegree G

def CommonGivesRootTarget : Prop :=
  ∀ F G p, Good F G → common F G p →
    eval1 (elimination F G) (p.1 + (canonicalShear F G : Rat) * p.2) = 0

def FibreDivisibilityTarget : Prop :=
  ∀ F G u (ordinates : List Rat), Good F G → ordinates.Nodup →
    (∀ v, v ∈ ordinates →
      eval2 (shear F (canonicalShear F G)) u v = 0 ∧
      eval2 (shear G (canonicalShear F G)) u v = 0) →
    ∃ quotient, coeffEq1
      (mul1 (pow1 [-u, 1] ordinates.length) quotient) (elimination F G)

def IntersectCompleteTarget : Prop :=
  ∀ F G, Good F G → ∃ points, intersect F G = some points ∧ points.Nodup ∧
    (∀ p, p ∈ points ↔ common F G p)

def IntersectCardinalityTarget : Prop :=
  ∀ F G points, Good F G → intersect F G = some points →
    points.length ≤ totalDegree F * totalDegree G

def IntersectHeightTarget : Prop :=
  ∀ F G points, Good F G → intersect F G = some points →
    ∀ p, common F G p → pointHeight p ≤ pointListHeight points

def MonomialCountTarget : Prop :=
  ∀ e, (monomials e).length = (e + 1) * (e + 2) / 2

def AuxiliaryBoxCountTarget : Prop :=
  ∀ e H, (auxiliaryBox e H).length ≤
    ((2 * H + 1) * H) ^ ((e + 1) * (e + 2) / 2)

def AuxiliaryBoxCoverageTarget : Prop :=
  ∀ e H G, 1 ≤ H → positivePlane G = true → coefficientEnvelope G e H →
    ∃ G', G' ∈ auxiliaryBox e H ∧ coeffEq2 G' G

def EnvelopeCompleteTarget : Prop :=
  ∀ F A e H, positivePlane F = true → pointwiseBoundedAux F A e H →
    (envelopeList F A e H).Nodup ∧
    (∀ p, p ∈ envelopeList F A e H ↔ pointPredicate F A p)

def EnvelopeCardinalityTarget : Prop :=
  ∀ F A e H, positivePlane F = true →
    (envelopeList F A e H).length ≤ totalDegree F * e *
      ((2 * H + 1) * H) ^ ((e + 1) * (e + 2) / 2)

def EnvelopeHeightTarget : Prop :=
  ∀ F A e H, positivePlane F = true → pointwiseBoundedAux F A e H →
    ∀ p, pointPredicate F A p → pointHeight p ≤ pointListHeight (envelopeList F A e H)

end IPRAFramework.Elimination
