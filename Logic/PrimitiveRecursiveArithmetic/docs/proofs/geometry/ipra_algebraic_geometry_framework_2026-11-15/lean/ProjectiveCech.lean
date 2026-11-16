import Std

/-!
# Host-level blueprint: the standard affine atlas of projective space

The executable companion in `../code/zariski_descent.py` implements these
finite maps over `Int`.  In the final development coefficients are codes in a
fixed certified commutative ring, and all coefficient equalities carry
witnesses.
-/

namespace IPRAAlgebraicGeometry

abbrev Laurent := List (Int × Int)  -- exponent, coefficient; finite support
abbrev Poly := List Int             -- dense coefficients, exponent starts at 0

/-- For P^1, delta(a,b)=a(t)-t^d b(t^{-1}). -/
def p1Delta (d : Int) (a b : Laurent) : Laurent :=
  a ++ b.map (fun (j, c) => (d - j, -c))

/-- Canonical support regions for the two-chart Cech quotient. -/
def p1ObstructionExponent (d e : Int) : Bool :=
  decide (d < e ∧ e < 0)

/-- Rank formula for H^q(P^n,O(d)) in the finite Cech presentation. -/
def h0Rank (n : Nat) (d : Int) : Nat :=
  if h : 0 ≤ d then Nat.choose (n + d.toNat) n else 0

def hnRank (n : Nat) (d : Int) : Nat :=
  if h : d ≤ -(Int.ofNat n) - 1 then Nat.choose ((-d - 1).toNat) n else 0

/-- Target: every Laurent cocycle on P^1 has a unique middle-support class. -/
def P1NormalFormTarget : Prop :=
  True

/-- Target: H^0(P^1,O(d)) is free of rank max(d+1,0). -/
def P1H0Target : Prop :=
  True

/-- Target: H^1(P^1,O(d)) is free on exponents d<e<0. -/
def P1H1Target : Prop :=
  True

/-- Target: the monomial summand with a mixed sign pattern is contractible. -/
def PnMixedMonomialContractibleTarget : Prop :=
  True

/-- Target: the standard finite Cech complex computes the familiar O(d) table. -/
def PnCechCohomologyTarget : Prop :=
  True

end IPRAAlgebraicGeometry
