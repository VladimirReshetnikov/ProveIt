import Std

/-!
# Finite dimension obstruction: exact interfaces

This file supplies definitions and explicit proof obligations for D01--D06.
It asserts no completed dimension theorem.  In particular every declaration
ending in `Target` is a definition of a proposition, NOT an axiom or theorem.

Ambient function types represent finite tables.  The object-iPRA translation
must replace these functions by natural-number codes and supply the primitive
recursive enumeration, floor-arithmetic, and parity proof described in the
human chapter.  There is no quantification over a universal PR evaluator here.
-/

namespace GeneralTopologyIPRA.Dimension

abbrev Grid (d N : Nat) := Fin d → Fin (N + 1)
abbrev QPoint (m : Nat) := Fin m → Rat
abbrev QTable (d m N : Nat) := Grid d N → QPoint m

def qabs (x : Rat) : Rat := if x < 0 then -x else x
def qmax (x y : Rat) : Rat := if x ≤ y then y else x

/-- Sup distance is exactly zero in dimension zero. -/
def supDist {m : Nat} (x y : QPoint m) : Rat :=
  (List.ofFn (fun i => qabs (x i - y i))).foldl qmax 0

structure CoordinatePermutation (d : Nat) where
  forward : Fin d → Fin d
  inverse : Fin d → Fin d
  inverse_forward : ∀ i, inverse (forward i) = i
  forward_inverse : ∀ i, forward (inverse i) = i

/--
A simplex is a lower grid corner followed by each coordinate increment once.
The explicit vertex table is accompanied by equations certifying that fact.
-/
structure KuhnSimplex (d N : Nat) where
  base : Fin d → Fin N
  perm : CoordinatePermutation d
  vertex : Fin (d + 1) → Grid d N
  start : ∀ j, (vertex ⟨0, by omega⟩ j).val = (base j).val
  step : ∀ (t : Fin d) (j : Fin d),
    (vertex ⟨t.val + 1, by omega⟩ j).val =
      (vertex ⟨t.val, by omega⟩ j).val +
        (if perm.forward t = j then 1 else 0)

def facePair {d N : Nat} (i : Fin d) (u v : Grid d N) : Prop :=
  (u i).val = 0 ∧ (v i).val = N

def faceSeparated {d m N : Nat} (F : QTable d m N) (h : Rat) : Prop :=
  ∀ (i : Fin d) (u v : Grid d N),
    facePair i u v → h ≤ supDist (F u) (F v)

def simplexSmall {d m N : Nat} (F : QTable d m N) (h : Rat) : Prop :=
  ∀ (s : KuhnSimplex d N) (a b : Fin (d + 1)),
    supDist (F (s.vertex a)) (F (s.vertex b)) < h / (d : Rat)

/-- D01, not yet a completed Lean theorem. -/
def FiniteDimensionObstructionTarget : Prop :=
  ∀ d m N, 0 < d → 0 < N →
    ∀ (F : QTable d m N) (h : Rat), 0 < h →
      faceSeparated F h → simplexSmall F h → d ≤ m

inductive ObstructionWitness {d m N : Nat} (F : QTable d m N) (h : Rat)
  | closeFace (i : Fin d) (u v : Grid d N)
      (opposite : facePair i u v)
      (close : supDist (F u) (F v) < h)
  | largeSimplex (s : KuhnSimplex d N) (a b : Fin (d + 1))
      (large : h / (d : Rat) ≤ supDist (F (s.vertex a)) (F (s.vertex b)))

/-- Positive certificate version of D01, with all output witnesses explicit. -/
def PositiveAlternativeTarget : Prop :=
  ∀ d m N, 0 < N → m < d →
    ∀ (F : QTable d m N) (h : Rat), 0 < h → Nonempty (ObstructionWitness F h)

abbrev Labeling (d N : Nat) := Grid d N → Fin (d + 1)

/-- Coordinate i here has zero-based index; the chapter uses i+1. -/
def cubicalBoundary {d N : Nat} (label : Labeling d N) : Prop :=
  ∀ (i : Fin d) (v : Grid d N),
    ((v i).val = 0 → (label v).val < i.val + 1) ∧
    ((v i).val = N → (label v).val ≠ i.val)

def full {d N : Nat} (label : Labeling d N) (s : KuhnSimplex d N) : Prop :=
  ∀ color : Fin (d + 1), ∃ t : Fin (d + 1), label (s.vertex t) = color

def fullFlag {d N : Nat} (label : Labeling d N) (s : KuhnSimplex d N) : Bool :=
  (List.finRange (d + 1)).all fun color =>
    (List.finRange (d + 1)).any fun t => label (s.vertex t) == color

def fullCount {d N : Nat} (label : Labeling d N)
    (simplices : List (KuhnSimplex d N)) : Nat :=
  simplices.foldl (fun total s => total + if fullFlag label s then 1 else 0) 0

/--
D02 requires proving oddness for the canonical enumeration of bases and
permutations.  The following is its existence consequence; the parity target
below additionally takes the concrete canonical list as an argument.
-/
def CubicalSpernerTarget : Prop :=
  ∀ d N, 0 < d → 0 < N → ∀ label : Labeling d N,
    cubicalBoundary label → ∃ s : KuhnSimplex d N, full label s

def CubicalParityForList {d N : Nat} (label : Labeling d N)
    (canonicalList : List (KuhnSimplex d N)) : Prop :=
  cubicalBoundary label → fullCount label canonicalList % 2 = 1

/-- Positive-denominator integer division is the floor of a rational. -/
def floorRat (q : Rat) : Int := q.num / Int.ofNat q.den

def staggeredCell {d m : Nat} (h : Rat) (i : Fin d) (y : QPoint m) : Fin m → Int :=
  fun j => floorRat (y j / h - (i.val : Rat) / (d : Rat))

def dyadic (p : Nat) : Rat := 1 / (2 : Rat) ^ p

def inUnitCube {d : Nat} (q : QPoint d) : Prop :=
  ∀ i, 0 ≤ q i ∧ q i ≤ 1

def normalizedVertex {d N : Nat} (v : Grid d N) : QPoint d :=
  fun i => ((v i).val : Rat) / (N : Rat)

structure EquippedDimensionData (d m : Nat) where
  evaluate : QPoint d → Nat → QPoint m
  modulus : Nat → Nat
  inverseScale : Nat
  forwardContract : ∀ q q' p k, inUnitCube q → inUnitCube q' →
    supDist q q' ≤ dyadic (modulus k) →
    supDist (evaluate q p) (evaluate q' p) ≤ dyadic k + 2 * dyadic p
  inverseContract : ∀ q q' p, inUnitCube q → inUnitCube q' →
    supDist (evaluate q p) (evaluate q' p) + 2 * dyadic p < dyadic inverseScale →
    supDist q q' ≤ (1 / 2 : Rat)

/-- D04 with explicit arithmetic contracts. -/
def EquippedDimensionTarget : Prop :=
  ∀ d m, Nonempty (EquippedDimensionData d m) → d ≤ m

/-!
Remaining implementation/proof steps, in dependency order:

1. Encode grid vertices and base/permutation pairs as bounded natural numbers;
   construct a canonical list of exactly N^d*d! distinct Kuhn simplices.
2. Prove that fullFlag reflects full.  Implement the three facet-mate cases
   from D02, check that the map is an involution without fixed points, and
   identify its unpaired entries with boundary facets.
3. Formalize the door-count identity modulo two.  Induct on restricted faces
   of one fixed table to obtain CubicalParityForList for the canonical list.
4. Prove the rational floor and staggered-threshold statements D03, including
   the half-open endpoint convention and negative coordinates.
5. Construct the first-zero-bit labeling, obtain a full simplex, and select
   differing target coordinates.  Implement finite pigeonhole either as an
   injection bound or as a repeated-coordinate witness.  This proves D01.
6. Instantiate N=2^(modulus k), p=k=inverseScale+d+5 and h=2^(-a-1).
   Prove the elementary slack inequalities, then D04.  Apply twice for D05.
7. D06 additionally has a genuine image map with certified evaluation errors;
   exact target values are not implied solely by the two finite contracts.
   Choose a denominator-bounded b with 2^(-b)≤epsilon, then p=k=b+d+5.
8. Translate the primitive recursive table operations and Boolean invariants
   into the chosen first-order iPRA syntax; do not identify ambient Lean
   functions or propositions with that object-language proof.

No arbitrary topological homeomorphism is claimed to furnish these data.
-/

end GeneralTopologyIPRA.Dimension
