import Std

/-!
# Rational sphere and finite antipodal obstruction: blueprint

Definitions match S01--S08 of the human report.  The small completed proofs
below concern finite sign products and an integer coefficient contradiction.
The sphere, cylinder, subdivision, and approximate-zero theorems are explicit
Target propositions or documented obligations.  They are not axioms and are
not presented as completed Lean theorems.

The ambient function types must be replaced by bounded natural-number table
codes, and fixed PR evaluators must receive their coding proofs, for an actual
object-language iPRA formalization.
-/

namespace GeneralTopologyIPRA.Sphere

abbrev QPoint (d : Nat) := Fin d → Rat

def qabs (x : Rat) : Rat := if x < 0 then -x else x
def qmax (x y : Rat) : Rat := if x ≤ y then y else x

def l1Norm {d : Nat} (x : QPoint d) : Rat :=
  (List.ofFn (fun i => qabs (x i))).foldl (· + ·) 0

def supNorm {d : Nat} (x : QPoint d) : Rat :=
  (List.ofFn (fun i => qabs (x i))).foldl qmax 0

def supDist {d : Nat} (x y : QPoint d) : Rat :=
  supNorm (fun i => x i - y i)

def dot {d : Nat} (x y : QPoint d) : Rat :=
  (List.ofFn (fun i => x i * y i)).foldl (· + ·) 0

def onSphere (n : Nat) (x : QPoint (n + 1)) : Prop := l1Norm x = 1
def antipodalPoint {d : Nat} (x : QPoint d) : QPoint d := fun i => -x i

structure SignedVertex (d : Nat) where
  coordinate : Fin d
  negative : Bool
  deriving DecidableEq

def antipodalVertex {d : Nat} (v : SignedVertex d) : SignedVertex d :=
  { coordinate := v.coordinate, negative := !v.negative }

def vertexPoint {d : Nat} (v : SignedVertex d) : QPoint d :=
  fun i => if i = v.coordinate then (if v.negative then -1 else 1) else 0

/--
Basis simplices are in increasing coordinate order and contain no opposite
pair.  Other orientations are represented by an integer sign; repetitions are
sent to zero in the boundary and simplicial-map implementation still required.
-/
structure CrossFace (d k : Nat) where
  vertices : Fin (k + 1) → SignedVertex d
  coordinateOrder : ∀ i j, i.val < j.val →
    (vertices i).coordinate.val < (vertices j).coordinate.val

abbrev CrossChain (d k : Nat) := CrossFace d k → Int
abbrev FacetSigns (d : Nat) := Fin d → Bool

def signProduct : List Bool → Int
  | [] => 1
  | b :: bs => if b then -signProduct bs else signProduct bs

def paritySign : Nat → Int
  | 0 => 1
  | n + 1 => -paritySign n

def fundamentalCoefficient {d : Nat} (signs : FacetSigns d) : Int :=
  signProduct (List.ofFn signs)

/-- Checked coefficient form of the antipodal factor in S01. -/
theorem signProduct_flip (bs : List Bool) :
    signProduct (bs.map Bool.not) = paritySign bs.length * signProduct bs := by
  induction bs with
  | nil => simp [signProduct, paritySign]
  | cons b bs ih =>
    cases b <;> simp [signProduct, paritySign, ih, Int.neg_mul, Int.mul_neg]

theorem signProduct_positive (d : Nat) :
    signProduct (List.replicate d false) = 1 := by
  induction d with
  | zero => rfl
  | succ d ih => simpa [List.replicate_succ, signProduct] using ih

theorem signProduct_negative (d : Nat) :
    signProduct (List.replicate d true) = paritySign d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, signProduct, paritySign, ih]

theorem paritySign_add_two (d : Nat) : paritySign (d + 2) = paritySign d := by
  simp [paritySign]

theorem paritySign_even (k : Nat) : paritySign (2 * k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h, paritySign_add_two, ih]

theorem paritySign_odd (k : Nat) : paritySign (2 * k + 1) = -1 := by
  simp [paritySign, paritySign_even]

theorem negative_facet_odd_dimension (k : Nat) :
    signProduct (List.replicate (2 * k + 1) true) = -1 := by
  rw [signProduct_negative, paritySign_odd]

/--
Checked final coefficient obstruction for S04.  The hard geometric work is
to obtain equality of the two chains; that work is not assumed completed.
-/
theorem no_antipodal_chain_equality {Basis : Type} (z : Basis → Int)
    (positiveFacet : Basis) (coefficientOne : z positiveFacet = 1) :
    (fun s => -z s) ≠ z := by
  intro equality
  have h := congrFun equality positiveFacet
  change -z positiveFacet = z positiveFacet at h
  rw [coefficientOne] at h
  omega

structure RationalTangentField (n : Nat) where
  evaluate : QPoint (n + 1) → QPoint (n + 1)
  lipschitz : Rat
  bound : Rat
  lipschitz_ge_one : 1 ≤ lipschitz
  bound_ge_one : 1 ≤ bound
  tangent : ∀ x, onSphere n x → dot x (evaluate x) = 0
  bounded : ∀ x, onSphere n x → supNorm (evaluate x) ≤ bound
  uniform : ∀ x y, onSphere n x → onSphere n y →
    supDist (evaluate x) (evaluate y) ≤ lipschitz * supDist x y

def dyadic (k : Nat) : Rat := 1 / (2 : Rat) ^ k

def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

def subdivisionCount (n k : Nat) : Nat := n * (k + 1)

def vertexOccurrenceBound (n k : Nat) : Nat :=
  2 ^ (n + 1) * (n + 1) * factorial (n + 1) ^ subdivisionCount n k

structure SubdivisionNet (n k : Nat) where
  vertices : List (QPoint (n + 1))
  valid : ∀ v, v ∈ vertices → onSphere n v
  covers : ∀ x, onSphere n x →
    ∃ v, v ∈ vertices ∧ supDist x v ≤ dyadic k
  lengthBound : vertices.length ≤ vertexOccurrenceBound n k

/-- The mesh/net part of S02, with an explicit finite-output bound. -/
def SubdivisionNetTarget : Prop :=
  ∀ n k, 1 ≤ n → Nonempty (SubdivisionNet n k)

structure RationalAntipodalHomotopy (n : Nat) where
  evaluate : QPoint (n + 1) → Rat → QPoint (n + 1)
  lipschitz : Rat
  nonnegative : 0 ≤ lipschitz
  image : ∀ x t, onSphere n x → 0 ≤ t → t ≤ 1 →
    onSphere n (evaluate x t)
  bottom : ∀ x, onSphere n x → evaluate x 0 = x
  top : ∀ x, onSphere n x → evaluate x 1 = antipodalPoint x
  uniform : ∀ x y t s,
    onSphere n x → onSphere n y → 0 ≤ t → t ≤ 1 → 0 ≤ s → s ≤ 1 →
    supDist (evaluate x t) (evaluate y s) ≤
      lipschitz * qmax (supDist x y) (qabs (t - s))

/-- S05: an uncompleted main theorem, named as a proposition definition. -/
def NoAntipodalHomotopyTarget : Prop :=
  ∀ n, 2 ≤ n → n % 2 = 0 → ¬ Nonempty (RationalAntipodalHomotopy n)

/-- S06: the rational-input approximate-zero conclusion. -/
def ApproximateHairyBallTarget : Prop :=
  ∀ n, n % 2 = 0 → ∀ F : RationalTangentField n,
    ∀ epsilon : Rat, 0 < epsilon →
      ∃ x : QPoint (n + 1), onSphere n x ∧ supNorm (F.evaluate x) ≤ epsilon

/--
Positive bounded-net version of S06.  Its proof supplies the terminating
first-success scan once vertex enumeration and rational comparison are coded.
-/
def BoundedApproximateZeroTarget : Prop :=
  ∀ n k, 2 ≤ n → n % 2 = 0 → ∀ F : RationalTangentField n,
    ∀ epsilon : Rat, 0 < epsilon →
      dyadic k ≤ epsilon / (4 * F.lipschitz) →
      ∀ net : SubdivisionNet n k,
        ∃ x, x ∈ net.vertices ∧ supNorm (F.evaluate x) ≤ epsilon

def auxiliaryVector {n : Nat} (F : RationalTangentField n)
    (x : QPoint (n + 1)) (t : Rat) : QPoint (n + 1) :=
  fun i => (1 - 2 * t) * x i + t * (1 - t) * F.evaluate x i

def normalizeL1 {d : Nat} (x : QPoint d) : QPoint d :=
  fun i => x i / l1Norm x

/-!
Remaining proof obligations, matching the report:

1. Encode finite oriented chains; prove the cross-polytope boundary pairing
   and the sign action (S01).  signProduct_flip is only its coefficient core.
2. Construct face flags and their rational barycenters; prove covering by
   sorting barycentric coordinates, the cone chain identity, and mesh
   contraction n/(n+1), then the explicit refinement count (S02).
3. Instantiate the simplex-carrier lemma from AlgebraicBlueprint/human A20
   for subdivision followed by a carried simplicial map (S03).
4. Implement a globally ordered cylinder triangulation and its prism boundary
   equation.  Obtain top=bottom after pushforward because the target has no
   (n+1)-simplices.  Combine S01 and S03, then use the checked coefficient
   obstruction above to complete S04.
5. At each finitely many cylinder vertices choose the first maximal absolute
   coordinate of H.  The bound 1/(n+1) and a mesh with K*rho<1/(2*(n+1))
   prevent opposite labels.  Preserve antipodal tie breaking at the endpoints
   and use the carried-bottom property to prove S05.
6. Given failure on a net with L*h≤epsilon/4, infer |F(x)|_infinity>
   3*epsilon/4 at every rational sphere point.  Set delta=epsilon/2 and
   lambda=min(1/(2*(n+1)),delta/8).  Tangency proves the squared-norm
   identity for auxiliaryVector, hence its l1 norm is at least lambda.
7. normalizeL1(auxiliaryVector F x t) then has Lipschitz constant at most
   ((n+2)*(3+L+M))/lambda and forbidden antipodal endpoints.  Eliminate the
   failed finite scan, obtaining BoundedApproximateZeroTarget.  Handle n=0
   directly from tangency at x=1.  No exact-zero or compact-subsequence
   theorem is part of this target.
8. For S07 prove pairwise cancellation for Jx and preservation of sum of
   squares.  For S08 implement determinant identities and bounded rational
   elimination for an odd-dimensional skew matrix, then l1-normalize a
   nonzero kernel vector.
9. Real-valued names require the separate interval-label robustness argument
   and extension/transport construction described in the report.  They are
   not included in the exact-rational targets above.
-/


end GeneralTopologyIPRA.Sphere

-- Complete theorem axiom audit for this standalone file.
#print axioms GeneralTopologyIPRA.Sphere.signProduct_flip
#print axioms GeneralTopologyIPRA.Sphere.signProduct_positive
#print axioms GeneralTopologyIPRA.Sphere.signProduct_negative
#print axioms GeneralTopologyIPRA.Sphere.paritySign_add_two
#print axioms GeneralTopologyIPRA.Sphere.paritySign_even
#print axioms GeneralTopologyIPRA.Sphere.paritySign_odd
#print axioms GeneralTopologyIPRA.Sphere.negative_facet_odd_dimension
#print axioms GeneralTopologyIPRA.Sphere.no_antipodal_chain_equality
