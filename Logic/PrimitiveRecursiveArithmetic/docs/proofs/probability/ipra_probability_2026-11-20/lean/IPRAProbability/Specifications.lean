import IPRAProbability.Finite
import IPRAProbability.PRSyntax

/-!
Compiling specification types for the continuous layer.
These are semantic interfaces in Lean, NOT a completed embedding into iPRA.
In the final object-language implementation each `regular` field must be an
actual `Prf PRAAx` derivation of the displayed finite inequalities, using the
fixed syntax trees carried by its generators.  No such derivation is hidden
in this file and no general instance is postulated.
-/
namespace IPRAProbability

/-- A rational number with its positive denominator explicit. -/
structure QCode where
  numerator : Int
  denominator : Nat
  denominator_pos : 0 < denominator

/-- Rational distance at most `2^(-k)`, with every denominator cleared. -/
def qClose (k : Nat) (a b : QCode) : Prop :=
  (a.numerator * (b.denominator : Int) -
    b.numerator * (a.denominator : Int)).natAbs * 2 ^ k ≤
      a.denominator * b.denominator

/-- A rational sequence produced by three fixed primitive-recursive programs.
The denominator program gives one less than the actual denominator.
Signed numerators are represented by a difference of two naturals.
-/
structure PRRationalSequence where
  positive : FixedPRFunction 1
  negative : FixedPRFunction 1
  denominatorMinusOne : FixedPRFunction 1

def PRRationalSequence.at (q : PRRationalSequence) (k : Nat) : QCode where
  numerator := (q.positive.value (fun _ => k) : Int) -
    (q.negative.value (fun _ => k) : Int)
  denominator := q.denominatorMinusOne.value (fun _ => k) + 1
  denominator_pos := Nat.zero_lt_succ _

/-- A regular real-name specification; no quotient or real-number trichotomy. -/
structure RegularRealSpec where
  approximation : PRRationalSequence
  regular : ∀ k l, k ≤ l → qClose k (approximation.at k) (approximation.at l)

/-- Two arguments, in a fixed ordering. -/
def argsTwo (a b : Nat) : Fin 2 → Nat := Fin.cases a (fun _ => b)

/-- A family of finite cylinder events on fair bits, with PR depth and PR table.
A nonzero table value denotes membership; only indices below `2^depth` matter.
-/
structure PREventFamily where
  depthProgram : FixedPRFunction 1
  tableProgram : FixedPRFunction 2

def PREventFamily.depth (A : PREventFamily) (k : Nat) : Nat :=
  A.depthProgram.value (fun _ => k)

def PREventFamily.table (A : PREventFamily) (k i : Nat) : Bool :=
  A.tableProgram.value (argsTwo k i) != 0

/-- Lift a cylinder table from depth `d` to depth `D ≥ d` by prefix projection.
Calls with `D < d` have no intended refinement meaning.
-/
def liftCylinder (d D : Nat) (A : Nat → Bool) (i : Nat) : Bool :=
  A (i / 2 ^ (D - d))

/-- Numerator of symmetric-difference distance on the common refinement. -/
def PREventFamily.distanceNumerator (A : PREventFamily) (k l : Nat) : Nat :=
  let D := max (A.depth k) (A.depth l)
  mass (2 ^ D) (fun _ => 1) (fun i =>
    xor (liftCylinder (A.depth k) D (A.table k) i)
        (liftCylinder (A.depth l) D (A.table l) i))

/-- A regular event-name specification, with a rational finite certificate.
This does not assert that every classical measurable event has such a name.
-/
structure RegularEventSpec where
  approximation : PREventFamily
  regular : ∀ k l, k ≤ l →
    approximation.distanceNumerator k l * 2 ^ k ≤
      2 ^ max (approximation.depth k) (approximation.depth l)

end IPRAProbability
