import SmallGainBlueprint

/-!
# Finite towers and the nonlinear lattice example

This is a compiled definition-and-target blueprint. Every declaration ending
in `Target` is a proposition, not a theorem: no inhabitant of that proposition
is asserted here. There is no `axiom` or `sorry`. The few proof terms in the
definitions merely certify bounds of finite indices.

The imported SmallGainBlueprint uses Std only. Host functions in these
definitions are schematic; an iPRA instance supplies fixed PR programs and
literal object-calculus proofs after encoding the finite data.
-/

namespace CoupledIPRA.Towers

/-- A finite sum with its primitive recursion visible. -/
def sumRange (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- Varying finite dimensions, certified regions, maps, and residual data. -/
structure TowerData where
  dim : Nat → Nat
  region : (n : Nat) → Vec (dim n) → Prop
  distance : (n : Nat) → Vec (dim n) → Vec (dim n) → Rat
  action : (n : Nat) → Vec (dim n) → Vec (dim n)
  restrict : (n : Nat) → Vec (dim (n + 1)) → Vec (dim n)
  q : Rat
  eta : Nat → Rat
  residualBudget : Nat → Rat
  sample : (n : Nat) → Vec (dim n)

/-- Distance laws only on the supplied finite regions. -/
def DistanceLaws (T : TowerData) : Prop :=
  ∀ n,
    (∀ x y, T.region n x → T.region n y → 0 ≤ T.distance n x y) ∧
    (∀ x, T.region n x → T.distance n x x = 0) ∧
    (∀ x y, T.region n x → T.region n y → T.distance n x y = T.distance n y x) ∧
    (∀ x y z, T.region n x → T.region n y → T.region n z →
      T.distance n x z ≤ T.distance n x y + T.distance n y z) ∧
    (∀ x y, T.region n x → T.region n y → T.distance n x y = 0 → x = y)

def ActionLaws (T : TowerData) : Prop :=
  0 ≤ T.q ∧ T.q < 1 ∧
  ∀ n,
    (∀ x, T.region n x → T.region n (T.action n x)) ∧
    (∀ x y, T.region n x → T.region n y →
      T.distance n (T.action n x) (T.action n y) ≤ T.q * T.distance n x y)

def RestrictionLaws (T : TowerData) : Prop :=
  ∀ n,
    (∀ x, T.region (n + 1) x → T.region n (T.restrict n x)) ∧
    (∀ x y, T.region (n + 1) x → T.region (n + 1) y →
      T.distance n (T.restrict n x) (T.restrict n y) ≤ T.distance (n + 1) x y) ∧
    0 ≤ T.eta n ∧
    (∀ x, T.region (n + 1) x →
      T.distance n (T.restrict n (T.action (n + 1) x))
        (T.action n (T.restrict n x)) ≤ T.eta n)

def SampleLaws (T : TowerData) : Prop :=
  ∀ n, T.region n (T.sample n) ∧ 0 ≤ T.residualBudget n ∧
    T.distance n (T.sample n) (T.action n (T.sample n)) ≤ T.residualBudget n

def TowerContract (T : TowerData) : Prop :=
  DistanceLaws T ∧ ActionLaws T ∧ RestrictionLaws T ∧ SampleLaws T

/-- Composition of finitely many restrictions; n+length is the source level. -/
def project (T : TowerData) (n : Nat) :
    (length : Nat) → Vec (T.dim (n + length)) → Vec (T.dim n)
  | 0, x => x
  | length + 1, x => project T n length (T.restrict (n + length) x)

def adjacentBudget (T : TowerData) (n : Nat) : Rat :=
  (T.residualBudget n + T.residualBudget (n + 1) + T.eta n) / (1 - T.q)

def adjacentDistance (T : TowerData) (n : Nat) : Rat :=
  T.distance n (T.sample n) (T.restrict n (T.sample (n + 1)))

def AdjacentDefectTarget : Prop :=
  ∀ T, TowerContract T → ∀ n, adjacentDistance T n ≤ adjacentBudget T n

def FiniteTelescopingTarget : Prop :=
  ∀ T, TowerContract T → ∀ n length,
    T.distance n (T.sample n) (project T n length (T.sample (n + length))) ≤
      sumRange (fun j => adjacentBudget T (n + j)) length

def DyadicTailTarget : Prop :=
  ∀ T, TowerContract T →
    (∀ n, adjacentBudget T n ≤ dyadic n) → ∀ n length,
      T.distance n (T.sample n) (project T n length (T.sample (n + length))) ≤
        2 * dyadic n

/-! ## Prefix towers and observable coordinates -/

def restrictPrefix {n m : Nat} (h : n ≤ m) (x : Vec m) : Vec n :=
  fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

def prefixOne (n : Nat) (x : Vec (n + 1)) : Vec n := restrictPrefix (Nat.le_succ n) x

def unitRegion {n : Nat} (x : Vec n) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1

def coordinateDistance {n : Nat} (x y : Vec n) : Rat :=
  maxZeroQ (fun i => dyadic i.val * absQ (x i - y i))

def coordinateQuery (samples : (n : Nat) → Vec n) (i k : Nat) : Rat :=
  samples (i + k + 3) ⟨i, by omega⟩

def PrefixTailContract (samples : (n : Nat) → Vec n) : Prop :=
  ∀ n length, 1 ≤ n →
    coordinateDistance (samples n)
      (restrictPrefix (by omega : n ≤ n + length) (samples (n + length))) ≤ 2 * dyadic n

def SharpRegular (U : Nat → Nat → Rat) : Prop :=
  ∀ i k l, absQ (U i k - U i l) ≤ dyadic (min k l + 2)

def CoordinateRegularityTarget : Prop :=
  ∀ samples, PrefixTailContract samples → SharpRegular (coordinateQuery samples)

/-! ## Exact rational lattice map and synchronous dyadic rounding -/

def coefficient (i : Nat) : Rat := 1 / (4 * ((i + 1 : Nat) : Rat))

def coordinateOrZero {n : Nat} (x : Vec n) (j : Nat) : Rat :=
  if h : j < n then x ⟨j, h⟩ else 0

def latticeMap (n : Nat) (x : Vec n) : Vec n := fun i =>
  coefficient i.val + (x i)^2 / 8 + coordinateOrZero x (i.val + 1) / 8

/-- Exact integer floor, not a floating-point approximation. -/
def roundDown (p : Nat) (x : Rat) : Rat :=
  (((x * (2 : Rat)^p).floor : Int) : Rat) / (2 : Rat)^p

def RoundDownTarget : Prop :=
  ∀ p x, 0 ≤ x → 0 ≤ roundDown p x ∧ roundDown p x ≤ x ∧
    x - roundDown p x ≤ dyadic p

/-- Every output coordinate is computed from the same old vector. -/
def roundedMap (n p : Nat) (x : Vec n) : Vec n :=
  fun i => roundDown p (latticeMap n x i)

def exactIterates (n : Nat) : Nat → Vec n
  | 0 => zero
  | t + 1 => latticeMap n (exactIterates n t)

def roundedIterates (n p : Nat) : Nat → Vec n
  | 0 => zero
  | t + 1 => roundedMap n p (roundedIterates n p t)

def latticePoint (n : Nat) : Vec n := roundedIterates n (n + 8) (n + 4)
def latticeResidual (n : Nat) : Rat :=
  coordinateDistance (latticePoint n) (latticeMap n (latticePoint n))

def latticeTower : TowerData where
  dim := id
  region := fun _ => unitRegion
  distance := fun _ => coordinateDistance
  action := latticeMap
  restrict := prefixOne
  q := 1 / 2
  eta := fun n => dyadic (n + 2)
  residualBudget := fun n => 7 * dyadic (n + 8)
  sample := latticePoint

/-- The example also has a harmless empty level 0 for total indexing. -/
def LatticeTowerContractTarget : Prop := TowerContract latticeTower

def LatticeMapTarget : Prop :=
  ∀ n x, unitRegion x →
    (∀ i, 0 ≤ latticeMap n x i ∧ latticeMap n x i ≤ 1 / 2) ∧
    (∀ y, unitRegion y →
      coordinateDistance (latticeMap n x) (latticeMap n y) ≤
        coordinateDistance x y / 2)

def RoundedResidualTarget : Prop :=
  ∀ n, 1 ≤ n → unitRegion (latticePoint n) ∧ latticeResidual n ≤ 7 * dyadic (n + 8)

def LatticeAdjacentTarget : Prop :=
  ∀ n, 1 ≤ n →
    coordinateDistance (latticePoint n) (prefixOne n (latticePoint (n + 1))) ≤
      (11 / 16 : Rat) * dyadic n

/-- Q in the paper; X is an alias for readers using a coordinate-name notation. -/
def Q (i k : Nat) : Rat := coordinateQuery latticePoint i k
abbrev X := Q

def equationResidual (U : Nat → Nat → Rat) (i p : Nat) : Rat :=
  absQ (U i p - coefficient i - (U i p)^2 / 8 - U (i + 1) p / 8)

def NameRegularityTarget : Prop := SharpRegular Q
def NameEquationTarget : Prop := ∀ i k, equationResidual Q i k ≤ 5 * dyadic (k + 7)

/-! ## Precisely scoped uniqueness: candidates remain in the unit box -/

def UnitBoxName (U : Nat → Nat → Rat) : Prop := ∀ i p, 0 ≤ U i p ∧ U i p ≤ 1

def RegularName (U : Nat → Nat → Rat) : Prop :=
  ∀ i k l, absQ (U i k - U i l) ≤ dyadic k + dyadic l

def AdmissibleName (U : Nat → Nat → Rat) : Prop :=
  UnitBoxName U ∧ RegularName U ∧ ∀ i p, equationResidual U i p ≤ dyadic p

def NamesEquivalent (U V : Nat → Nat → Rat) : Prop :=
  ∀ i k, ∃ cutoff, ∀ p, cutoff ≤ p → absQ (U i p - V i p) ≤ dyadic k

def LatticeExistenceTarget : Prop := AdmissibleName Q

/-- Finite proof uses N=i+k+3 and p=i+k+5. -/
def FiniteUniquenessTarget : Prop :=
  ∀ U V, AdmissibleName U → AdmissibleName V → ∀ i k,
    absQ (U i (i + k + 5) - V i (i + k + 5)) ≤ dyadic (k + 2)

def UniquenessTarget : Prop :=
  ∀ U V, AdmissibleName U → AdmissibleName V → NamesEquivalent U V

/-!
Completion order:
1. Rational codec, finite maximum, distance and restriction laws.
2. AdjacentDefectTarget by a triangle calculation and positive cancellation.
3. FiniteTelescopingTarget by QF induction on the finite restriction length.
4. DyadicTailTarget by a finite geometric-sum identity.
5. RoundDownTarget via integer division bounds; lattice row bound and rounding
   comparison by QF induction on t; derive RoundedResidualTarget.
6. Instantiate the tower contract, extract coordinate regularity, and bound
   the discrepancy between the i+1 coordinate at levels n and n+1.
7. For uniqueness truncate the two candidate names at N=i+k+3, precision
   p=i+k+5, and retain the boundary residual 2^(-N-2).
8. Build literal Prf PRAAx proofs. Compiling the definitions in this file
   establishes neither its Target propositions nor an internal reflection rule.
-/

#check AdjacentDefectTarget
#check FiniteTelescopingTarget
#check CoordinateRegularityTarget
#check Q
#check X
#check NameEquationTarget
#check FiniteUniquenessTarget
#check UniquenessTarget

end CoupledIPRA.Towers
