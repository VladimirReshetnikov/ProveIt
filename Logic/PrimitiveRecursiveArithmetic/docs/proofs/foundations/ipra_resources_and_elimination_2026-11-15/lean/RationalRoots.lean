import Std

/-!
# Concrete rational-root list program and exact proof targets

This module supplies executable finite data and algorithms, not a proof of
their completeness. `RationalRootsTarget` and `DegreeBoundTarget` are defined
propositions awaiting proofs. The human proof and the plane-intersection
extension appear in the article. The zero polynomial returns `none`, so it
cannot be confused with a nonzero polynomial having no rational roots.
-/

namespace IPRAFramework.RationalRoots

/-- Coefficients are in increasing order of degree; trailing zeros are allowed. -/
abbrev QPoly := List Rat
abbrev PlanePoly := List (List Rat)
abbrev QPoint := Rat × Rat

def eval (p : QPoly) (t : Rat) : Rat :=
  p.foldr (fun a r => a + t * r) 0

/-- Row i contains coefficients of X^i Y^j, in increasing j. -/
def evalPlane (p : PlanePoly) (x y : Rat) : Rat := eval (p.map (fun row => eval row y)) x

def commonDen (p : QPoly) : Nat := p.foldl (fun d a => d * a.den) 1

def integerCoeffs (p : QPoly) : List Int :=
  p.map (fun a => a.num * Int.ofNat (commonDen p / a.den))

def nonzeroIntegers (p : QPoly) : List Int :=
  (integerCoeffs p).filter (fun a => a != 0)

def numeratorBox (B : Nat) : List Int :=
  (List.range (2 * B + 1)).map (fun i => Int.ofNat i - Int.ofNat B)

def candidateBox (B C : Nat) : List Rat :=
  (numeratorBox B).flatMap (fun p => (List.range C).map (fun j => mkRat p (j + 1)))

/-- The first nonzero coefficient bounds the reduced numerator after removing
the initial power of T; the last bounds the positive reduced denominator.
Zero is always tested separately. -/
def rationalRoots (p : QPoly) : Option (List Rat) :=
  match nonzeroIntegers p with
  | [] => none
  | a :: rest =>
      let b := ((a :: rest).reverse.head?).getD 0
      some (((0 : Rat) :: candidateBox a.natAbs b.natAbs).filter
        (fun x => eval p x == 0)).eraseDups

def nonzero (p : QPoly) : Prop := ∃ a ∈ p, a ≠ 0

def degree (p : QPoly) : Nat :=
  (p.zipIdx).foldl (fun d ai => if ai.1 == 0 then d else max d ai.2) 0

def rationalHeight (q : Rat) : Nat := max q.num.natAbs q.den

def listHeight (xs : List Rat) : Nat :=
  xs.foldl (fun h q => max h (rationalHeight q)) 0

def RationalRootsTarget : Prop :=
  ∀ p, nonzero p → ∃ L, rationalRoots p = some L ∧ L.Nodup ∧
    (∀ x, x ∈ L ↔ eval p x = 0)

def DegreeBoundTarget : Prop :=
  ∀ p L, nonzero p → rationalRoots p = some L → L.length ≤ degree p

def HeightBoundTarget : Prop :=
  ∀ p L, nonzero p → rationalRoots p = some L →
    ∀ x, eval p x = 0 → rationalHeight x ≤ listHeight L

end IPRAFramework.RationalRoots
