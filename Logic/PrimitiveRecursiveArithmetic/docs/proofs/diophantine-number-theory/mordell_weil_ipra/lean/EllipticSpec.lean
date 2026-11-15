import DescentCore
import FiniteSearch
import E1FiniteTable

/-!
# Concrete arithmetic definitions and explicit remaining targets

This module gives executable native definitions. Its target propositions
are definitions of statements, NOT axioms or proofs of those statements.
The generic native descent proof does not imply these arithmetic targets.

`Rat` is Lean's reduced pair of an integer numerator and positive natural
denominator. Its use here is a native implementation convenience. An iPRA
proof must still verify the fixed natural-number coding and its operations.
-/

namespace MordellWeilIPRA.EllipticSpec

/-- The signed-integer convention used in the paper. -/
def encodeInt : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def decodeInt (n : Nat) : Int :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def pair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1) - 1

/-- A bounded decoder; its inverse identities are arithmetic proof goals. -/
def unpair (n : Nat) : Nat × Nat :=
  let a := FiniteSearch.bounded
    (fun k => decide ((n + 1) % (2 ^ k) = 0 ∧
      ((n + 1) / (2 ^ k)) % 2 = 1)) (n + 2)
  (a, ((n + 1) / (2 ^ a) - 1) / 2)

def nilCode : Nat := 0
def consCode (head tail : Nat) : Nat := 1 + pair head tail

def encodeRat (q : Rat) : Nat := pair (encodeInt q.num) q.den

def decodeRat (n : Nat) : Rat :=
  let nd := unpair n
  if hd : nd.2 = 0 then 0 else Rat.normalize (decodeInt nd.1) nd.2 hd

inductive Point where
  | origin
  | affine (x y : Rat)
  deriving Repr, DecidableEq

open Point

def encodePoint : Point → Nat
  | origin => 0
  | affine x y => 1 + pair (encodeRat x) (encodeRat y)

def decodePoint : Nat → Point
  | 0 => origin
  | n + 1 =>
      let xy := unpair n
      affine (decodeRat xy.1) (decodeRat xy.2)

structure Curve where
  a : Int
  b : Int
  deriving Repr, DecidableEq

def Nonsingular (E : Curve) : Prop := 4 * E.a ^ 3 + 27 * E.b ^ 2 ≠ 0

def cubic (E : Curve) (x : Rat) : Rat :=
  x * x * x + (E.a : Rat) * x + (E.b : Rat)

def onCurve (E : Curve) : Point → Prop
  | origin => True
  | affine x y => y * y = cubic E x

instance (E : Curve) (P : Point) : Decidable (onCurve E P) := by
  cases P <;> unfold onCurve <;> infer_instance

/-- The first-order validity test additionally requires a canonical code. -/
def validCode (E : Curve) (n : Nat) : Bool :=
  decide (encodePoint (decodePoint n) = n ∧ onCurve E (decodePoint n))

def normalizeCode (E : Curve) (n : Nat) : Nat :=
  if validCode E n then n else 0

def pointOfCode (E : Curve) (n : Nat) : Point :=
  decodePoint (normalizeCode E n)

def negate : Point → Point
  | origin => origin
  | affine x y => affine x (-y)

private def chordResult (x₁ y₁ x₂ slope : Rat) : Point :=
  let x₃ := slope * slope - x₁ - x₂
  affine x₃ (slope * (x₁ - x₃) - y₁)

/-- Total chord-and-tangent formulas. Algebraic properties are separate
proof obligations restricted to valid points on a nonsingular curve. -/
def add (E : Curve) : Point → Point → Point
  | origin, Q => Q
  | P, origin => P
  | affine x₁ y₁, affine x₂ y₂ =>
      if x₁ = x₂ then
        if y₁ + y₂ = 0 then origin
        else chordResult x₁ y₁ x₂
          ((3 * x₁ * x₁ + (E.a : Rat)) / (2 * y₁))
      else chordResult x₁ y₁ x₂ ((y₂ - y₁) / (x₂ - x₁))

def twice (E : Curve) (P : Point) : Point := add E P P
def subtract (E : Curve) (P Q : Point) : Point := add E P (negate Q)

def addCode (E : Curve) (p q : Nat) : Nat :=
  encodePoint (add E (pointOfCode E p) (pointOfCode E q))

def negateCode (E : Curve) (p : Nat) : Nat :=
  encodePoint (negate (pointOfCode E p))

def H : Point → Nat
  | origin => 1
  | affine x _ => max x.num.natAbs x.den

/-- Ceiling binary logarithm by bounded search, with height zero at O. -/
def height : Point → Nat
  | origin => 0
  | P@(.affine _ _) =>
      FiniteSearch.bounded (fun k => decide (H P ≤ 2 ^ k)) (H P + 1)

def heightCode (E : Curve) (p : Nat) : Nat := height (pointOfCode E p)

def EncodingTargets : Prop :=
  (∀ z, decodeInt (encodeInt z) = z) ∧
  (∀ a b, unpair (pair a b) = (a, b)) ∧
  (∀ q, decodeRat (encodeRat q) = q) ∧
  (∀ P, decodePoint (encodePoint P) = P)

/-- Coefficients in ascending degree order for the halving quartic. -/
def halvingQuartic (E : Curve) (targetX : Rat) : List Int :=
  let u := targetX.num
  let v : Int := targetX.den
  [E.a ^ 2 * v - 4 * E.b * u,
   -(8 * E.b * v + 4 * E.a * u),
   -2 * E.a * v,
   -4 * u,
   v]

def evalPolynomial (x : Rat) : List Int → Rat
  | [] => 0
  | c :: cs => (c : Rat) + x * evalPolynomial x cs

/-- Supplied actual representatives; no finite Selmer upper bound occurs. -/
def Cover (E : Curve) (representatives : List Point) : Prop :=
  (∀ R, R ∈ representatives → onCurve E R) ∧
  ∀ P, onCurve E P → ∃ R, R ∈ representatives ∧
    ∃ Q, onCurve E Q ∧ add E (twice E Q) R = P

/-- All declarations ending in `Target` are propositions to prove later. -/
def HalvesCorrectTarget (E : Curve) (halves : Point → List Point) : Prop :=
  ∀ T, onCurve E T → ∀ Q,
    Q ∈ halves T ↔ onCurve E Q ∧ twice E Q = T

def candidatePairs (E : Curve) (representatives : List Point)
    (halves : Point → List Point) (P : Point) : List (Point × Point) :=
  representatives.flatMap fun R =>
    (halves (subtract E P R)).map fun Q => (Q, R)

def divisionTest (E : Curve) (P : Point) (QR : Point × Point) : Bool :=
  decide (add E (twice E QR.1) QR.2 = P)

def divisionChoice (E : Curve) (representatives : List Point)
    (halves : Point → List Point) (P : Point) : Point × Point :=
  FiniteSearch.select (divisionTest E P) (origin, origin)
    (candidatePairs E representatives halves P)

def CoverImpliesSearchSuccessTarget (E : Curve)
    (representatives : List Point) (halves : Point → List Point) : Prop :=
  HalvesCorrectTarget E halves → Cover E representatives →
    ∀ P, onCurve E P → ∃ QR,
      QR ∈ candidatePairs E representatives halves P ∧
      divisionTest E P QR = true

def DoublingHeightTarget (E : Curve) (D : Nat) : Prop :=
  ∀ Q, onCurve E Q → 4 * height Q ≤ height (twice E Q) + D

def TranslationHeightTarget (E : Curve) (R : Point) (B : Nat) : Prop :=
  ∀ P, onCurve E P → height (subtract E P R) ≤ 2 * height P + B

def ContractionTarget (E : Curve) (representatives : List Point)
    (C : Nat) : Prop :=
  ∀ P Q R, onCurve E P → onCurve E Q → R ∈ representatives →
    add E (twice E Q) R = P → 2 * height Q ≤ height P + C

def EnumerationTarget (E : Curve) (enum : Nat → List Point) : Prop :=
  ∀ B P, P ∈ enum B ↔ onCurve E P ∧ height P ≤ B

inductive GroupWord (generatorCount : Nat) where
  | zero
  | atom : Fin generatorCount → GroupWord generatorCount
  | add : GroupWord generatorCount → GroupWord generatorCount →
      GroupWord generatorCount
  | neg : GroupWord generatorCount → GroupWord generatorCount
  deriving Repr, DecidableEq

def evalWord (E : Curve) (generators : List Point) :
    GroupWord generators.length → Point
  | .zero => origin
  | .atom i => generators.get i
  | .add w v => add E (evalWord E generators w) (evalWord E generators v)
  | .neg w => negate (evalWord E generators w)

def GeneratesTarget (E : Curve) (generators : List Point) : Prop :=
  (∀ P, P ∈ generators → onCurve E P) ∧
  ∀ P, onCurve E P → ∃ w : GroupWord generators.length,
    evalWord E generators w = P

def E1 : Curve := ⟨-1, 0⟩

def E1ClassificationTarget : Prop :=
  ∀ P, onCurve E1 P →
    P = origin ∨ P = affine (-1) 0 ∨ P = affine 0 0 ∨ P = affine 1 0

def E1Point : E1FiniteTable.Point → Point
  | .origin => origin
  | .minusOne => affine (-1) 0
  | .zero => affine 0 0
  | .plusOne => affine 1 0

def E1PointsValidTarget : Prop :=
  ∀ P : E1FiniteTable.Point, onCurve E1 (E1Point P)

/-- A separate target for agreement of the 16 exact rational additions
with the finite table. This is a statement, not an asserted proof. -/
def E1TableTarget : Prop :=
  ∀ P Q : E1FiniteTable.Point,
    add E1 (E1Point P) (E1Point Q) = E1Point (E1FiniteTable.add P Q)

/-- A record of the group-law proof obligations, not a supplied instance. -/
structure GroupLawCertificate (E : Curve) : Prop where
  nonsingular : Nonsingular E
  closed : ∀ P Q, onCurve E P → onCurve E Q → onCurve E (add E P Q)
  associative : ∀ P Q R, onCurve E P → onCurve E Q → onCurve E R →
    add E (add E P Q) R = add E P (add E Q R)
  commutative : ∀ P Q, onCurve E P → onCurve E Q → add E P Q = add E Q P
  identity : ∀ P, onCurve E P → add E P origin = P
  inverse : ∀ P, onCurve E P → add E P (negate P) = origin

end MordellWeilIPRA.EllipticSpec
