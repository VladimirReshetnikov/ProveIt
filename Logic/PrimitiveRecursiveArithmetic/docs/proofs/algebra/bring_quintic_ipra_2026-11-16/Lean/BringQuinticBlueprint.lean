/-!
# Bring radicals and quintics in iPRA: Lean blueprint

Status: uncompiled blueprint, not a completed formalization.

This file has two purposes.

1. It records executable metatheoretic definitions and small exact identities.
2. It states, without postulating an inhabitant, the proof obligations that
   should become closed `Prf PRAAx` theorems in ProveIt's deep embedding.

No `sorry`, `admit`, or axiom is used.  The intended ProveIt integration imports
are documented below; this standalone blueprint imports Mathlib only because a
ProveIt checkout is not bundled in the archive.

Intended repository imports (names should be checked against the pinned commit):

```
import IPRADerivations.Algebra.PolynomialFormulas
import IPRADerivations.Core.Integers
import IPRADerivations.Core.Order
import IPRADerivations.Core.Powers
import IPRADerivations.Core.Search
import IPRADerivations.Core.Pairing
```
-/

import Mathlib

set_option autoImplicit false

namespace BringQuinticBlueprint

/-! ## 1. Exact rational algebra used by the object-theory compiler -/

def s4 (x y : ℚ) : ℚ :=
  x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4

theorem s4_sos (x y : ℚ) :
    12 * s4 x y =
      3 * (2*x^2 + x*y)^2 + (3*x*y + 2*y^2)^2 + 8*y^4 := by
  unfold s4
  ring

theorem bring_difference (x y a : ℚ) :
    (y^5 + y + a) - (x^5 + x + a) = (y-x) * (1 + s4 x y) := by
  unfold s4
  ring

def bringPoly (a x : ℚ) : ℚ := x^5 + x + a

theorem bring_scaling (c z q : ℚ) :
    (c*z)^5 + c^4*(c*z) + q = c^5*(z^5+z) + q := by
  ring

theorem reducible_example (x : ℚ) :
    x^5-x^4-x+1 = (x^2+1)*(x+1)*(x-1)^2 := by
  ring

/-- Algebraic elimination of a multiple Bring root. -/
theorem branch_equation
    (x a : ℚ)
    (hP : x^5 + x + a = 0)
    (hD : 5*x^4 + 1 = 0) :
    3125*a^4 + 256 = 0 := by
  have hx5 : 5*x^5 = -x := by
    calc
      5*x^5 = x*(5*x^4) := by ring
      _ = x*(-1) := by nlinarith [hD]
      _ = -x := by ring
  have ha : 5*a = -4*x := by
    nlinarith [hP, hx5]
  calc
    3125*a^4 + 256 = 5*(5*a)^4 + 256 := by ring
    _ = 5*(-4*x)^4 + 256 := by rw [ha]
    _ = 256*(5*x^4+1) := by ring
    _ = 0 := by rw [hD]; ring

/-! ## 2. Exact rational bisection -/

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace Interval

def width (I : Interval) : ℚ := I.hi - I.lo

def midpoint (I : Interval) : ℚ := (I.lo + I.hi) / 2

def brackets (a : ℚ) (I : Interval) : Prop :=
  bringPoly a I.lo ≤ 0 ∧ 0 ≤ bringPoly a I.hi

end Interval

def bisectStep (a : ℚ) (I : Interval) : Interval :=
  let m := I.midpoint
  if bringPoly a m ≤ 0 then ⟨m, I.hi⟩ else ⟨I.lo, m⟩

def bisect (a : ℚ) : Nat → Interval → Interval
  | 0, I => I
  | n+1, I => bisect a n (bisectStep a I)

/-- A finite theorem to be proved first at the Mathlib level, then compiled to
    an object-theory Boolean invariant. -/
def BisectionSpec : Prop :=
  ∀ (a : ℚ) (I : Interval),
    I.lo ≤ I.hi → I.brackets a →
    let J := bisectStep a I
    J.lo ≤ J.hi ∧ J.brackets a ∧ J.width = I.width / 2

/-! ## 3. Truncated rational series -/

abbrev TruncSeries := List ℚ

def coeff (A : TruncSeries) (n : Nat) : ℚ := A.getD n 0

def truncAdd (N : Nat) (A B : TruncSeries) : TruncSeries :=
  List.ofFn (fun n : Fin (N+1) => coeff A n + coeff B n)

def truncMul (N : Nat) (A B : TruncSeries) : TruncSeries :=
  List.ofFn (fun n : Fin (N+1) =>
    ∑ i ∈ Finset.range (n.1+1), coeff A i * coeff B (n.1-i))

def truncOne (N : Nat) : TruncSeries :=
  List.ofFn (fun n : Fin (N+1) => if n.1 = 0 then 1 else 0)

def truncX (N : Nat) : TruncSeries :=
  List.ofFn (fun n : Fin (N+1) => if n.1 = 1 then 1 else 0)

def truncPow (N : Nat) (A : TruncSeries) : Nat → TruncSeries
  | 0 => truncOne N
  | k+1 => truncMul N (truncPow N A k) A

def signedBringCoeff (k : Nat) : ℚ :=
  ((-1 : ℚ)^k) * (Nat.choose (5*k) k : ℚ) / (4*k+1)

def bringSeries (N : Nat) : TruncSeries :=
  List.ofFn (fun n : Fin (N+1) =>
    if h : n.1 % 4 = 1 then
      signedBringCoeff ((n.1-1)/4)
    else 0)

def bringResidual (N : Nat) : TruncSeries :=
  truncAdd N (truncPow N (bringSeries N) 5)
    (truncAdd N (bringSeries N)
      (List.ofFn (fun n : Fin (N+1) => if n.1 = 1 then -1 else 0)))

/-- Uniform finite-series target.  This proposition is intentionally a field of
    an uninhabited obligations structure below, not an asserted theorem. -/
def BringSeriesSpec : Prop :=
  ∀ N n, n ≤ N → coeff (bringResidual N) n = 0

/-! ## 4. Finite certificates -/

structure BringJerrardCertificate where
  /-- Coefficients of a principal quintic `Y^5+c2*Y^2+c1*Y+c0`. -/
  c2 c1 c0 : ℚ
  /-- Coefficients of `T(Y)=Y^4+alpha*Y^3+beta*Y^2+gamma*Y+delta`. -/
  alpha beta gamma delta : ℚ
  d1 d0 : ℚ
  /-- A sparse coefficient list for the claimed resultant identity. -/
  resultantCoeffs : List ℚ

/-- The final implementation computes the Sylvester determinant and compares
    it with `V^5+d1*V+d0`. -/
def verifyBringJerrard (_c : BringJerrardCertificate) : Bool :=
  false  -- placeholder executable interface; no soundness theorem is asserted

structure FiniteGroupTable where
  card : Nat
  mul : Nat → Nat → Nat
  one : Nat
  inv : Nat → Nat

/-- A five-letter permutation is stored as five natural values.  The verifier
    must check range and bijectivity. -/
abbrev Perm5Code := Fin 5 → Fin 5

/-! ## 5. Object-theory obligations

Each field below should eventually be replaced by a theorem with a closed type
of the form

```
([] : List (Fm PTm 0)) ⊢[PRAAx] φ
```

using ProveIt's `LeanProofs.IPRA` / `LeanProofs.ConciseIPRA` APIs.  Merely
constructing an inhabitant of this record in Mathlib would not meet the object
boundary; it is only a dependency checklist.
-/

structure FormalizationObligations : Prop where
  sosIdentity : ∀ x y : ℚ,
    12 * s4 x y =
      3 * (2*x^2+x*y)^2 + (3*x*y+2*y^2)^2 + 8*y^4
  bisectionInvariant : BisectionSpec
  finiteLagrange : BringSeriesSpec
  hypergeometricRatio : ∀ k : Nat,
    signedBringCoeff (k+1) / signedBringCoeff k =
      -((3125 : ℚ)/256) *
       ((k : ℚ)+1/5)*((k : ℚ)+2/5)*((k : ℚ)+3/5)*((k : ℚ)+4/5) /
       (((k : ℚ)+1/2)*((k : ℚ)+3/4)*((k : ℚ)+5/4)*((k : ℚ)+1))
  finiteGroupPerfectA5 : Prop
  affineClassification : Prop
  frobeniusCycleTypeBridge : Prop
  radicalTowerSolvable : Prop
  genericSymmetricFixedField : Prop

/-! ## 6. Recommended closed theorem names in ProveIt

```
bring_s4_sos
bring_strong_monotone
bring_bisect_invariant
bring_regular_name
bring_lipschitz
bring_odd
bring_unbounded
bring_asymptotic
bring_finite_lagrange
bring_coeff_closed_form
bring_hypergeom_coeff
bring_discriminant
bring_cockle_harley
quintic_depress
quintic_principal_tschirnhaus
bring_jerrard_certificate_sound
de_moivre_product
four_resolvent_product
S5_derived_eq_A5
A5_perfect
transitive_solvable_subgroup_le_AGL15
x5_sub_x_add_one_galois_S5
x5_add_x_add_three_galois_S5
radical_tower_group_solvable
generic_quintic_not_radical
```
-/

end BringQuinticBlueprint
