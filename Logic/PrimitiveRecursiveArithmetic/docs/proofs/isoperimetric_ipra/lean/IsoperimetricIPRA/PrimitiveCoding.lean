import IsoperimetricIPRA.FiniteData

/-!
# Explicit numerical codecs

STATUS: UNCOMPILED BLUEPRINT. These total definitions specify one concrete
coding convention. Their inverse laws and compilation into the `PR` syntax
of ConciseIPRA remain obligations. In particular this file does not define a
primitive-recursive universal evaluator for arbitrary PR programs.
-/

namespace IsoperimetricIPRA.Codec

/-- Positive pairing, with zero reserved for an empty list. -/
def pair (a b : ℕ) : ℕ := 2 ^ a * (2 * b + 1)

/-- Remove at most `fuel` powers of two. -/
def peel : ℕ → ℕ → ℕ × ℕ
  | 0, n => (0, n)
  | fuel + 1, n =>
      if n ≠ 0 ∧ n % 2 = 0 then
        let out := peel fuel (n / 2)
        (out.1 + 1, out.2)
      else (0, n)

def unpair (n : ℕ) : ℕ × ℕ :=
  let out := peel n n
  (out.1, (out.2 - 1) / 2)

def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: rest => pair a (encodeList rest)

/-- Explicitly fueled decoding is total even before the decrease lemma
for the tail of a positive pair has been formalized. -/
def decodeListFuel : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, n =>
      let out := unpair n
      out.1 :: decodeListFuel fuel out.2

def decodeList (n : ℕ) : List ℕ := decodeListFuel n n

def encodeInt : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def decodeInt (n : ℕ) : ℤ :=
  if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)

/-- Denominator minus one is stored, so every numerical code denotes a
rational with a positive denominator. Canonical normalization is optional
for the arithmetic proof but is performed by Lean's ambient `Rat` type. -/
def encodeRat (q : ℚ) : ℕ := pair (encodeInt q.num) (q.den - 1)

def decodeRat (n : ℕ) : ℚ :=
  let out := unpair n
  (decodeInt out.1 : ℚ) / ((out.2 + 1 : ℕ) : ℚ)

def encodePoint (p : Point) : ℕ := pair (encodeRat p.x) (encodeRat p.y)

def decodePoint (n : ℕ) : Point :=
  let out := unpair n
  ⟨decodeRat out.1, decodeRat out.2⟩

def encodePolygon (p : List Point) : ℕ := encodeList (p.map encodePoint)

def decodePolygon (n : ℕ) : List Point := (decodeList n).map decodePoint

def encodeUpperLengths (u : List ℚ) : ℕ := encodeList (u.map encodeRat)

def decodeUpperLengths (n : ℕ) : List ℚ := (decodeList n).map decodeRat

/-- The three arguments are polygon code, upper-length code, precision.
Return zero for acceptance, one for rejection. This is the concrete function
to be compiled to a named `PR 3` symbol in `InternalGoal.lean`. -/
def checkNat (p u k : ℕ) : ℕ :=
  if finiteCheck (decodePolygon p) (decodeUpperLengths u) k then 0 else 1

/- Codec proof obligations:

* `unpair (pair a b) = (a,b)` by bounded division and powers-of-two induction.
* The second component of `unpair n` is less than positive `n`.
* `decodeList (encodeList xs) = xs`; prove fuel sufficiency with a bounded
  prefix invariant, not an unbounded search for the end of a computation.
* The integer, rational, point, and polygon round-trip laws.
* Replace ambient normalized rationals by signed integer pairs in the object
  language and clear positive denominators in every comparison.
* Give each used numerical operation an actual `ConciseIPRA.PR` expression.

The concrete codes are intentionally simple, not efficient. Large bounds
do not violate primitive recursiveness.
-/

end IsoperimetricIPRA.Codec
