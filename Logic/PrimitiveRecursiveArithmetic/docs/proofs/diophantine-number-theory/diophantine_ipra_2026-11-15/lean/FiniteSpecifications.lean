import Mathlib

/-!
Concrete arithmetic definitions and proof targets for the accompanying report.

STATUS: this file has not been elaborated in the delivery environment.  The
polynomial identities below are intended complete Lean proofs; the principal
Diophantine conclusions below are definitions of specifications, not theorems.
No general Roth theorem or object-iPRA correctness theorem is asserted here.
-/

namespace DiophantineIPRA

def pellBound (D : Nat) : Nat :=
  (2 * D + 2) ^ (2 * (2 * D + 1) ^ 3 + 2)

def pellSolution (D x y : Nat) : Prop :=
  0 < x ∧ 0 < y ∧ x ^ 2 = D * y ^ 2 + 1

def pellFirstY (D : Nat) : Nat :=
  ((List.range (pellBound D)).find? fun y =>
    decide (0 < y ∧ (Nat.sqrt (D * y ^ 2 + 1)) ^ 2 = D * y ^ 2 + 1)).getD 0

def smooth (S : List Nat) (n : Nat) : Prop :=
  0 < n ∧ ∀ p, p ≤ n → Nat.Prime p → p ∣ n → p ∈ S

def primeList (S : List Nat) : Prop := S.Nodup ∧ ∀ p ∈ S, Nat.Prime p

def stormerSpecification (neighbors : List Nat → List Nat) : Prop :=
  ∀ S, primeList S →
    (neighbors S).Nodup ∧
    (neighbors S).length ≤ 3 ^ S.length - 2 ^ S.length ∧
    (∀ n, n ∈ neighbors S ↔ smooth S n ∧ smooth S (n + 1)) ∧
    (∀ n ∈ neighbors S, 2 * n + 1 < pellBound (S.prod ^ 2))

structure Quadratic where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq

def Quadratic.height (f : Quadratic) : Nat :=
  max f.a.natAbs (max f.b.natAbs f.c.natAbs)

def Quadratic.eval (f : Quadratic) (x : Rat) : Rat :=
  (f.a : Rat) * x ^ 2 + (f.b : Rat) * x + (f.c : Rat)

def Quadratic.derivative (f : Quadratic) (x : Rat) : Rat :=
  2 * (f.a : Rat) * x + (f.b : Rat)

def Quadratic.primitive (f : Quadratic) : Prop :=
  Nat.gcd f.a.natAbs (Nat.gcd f.b.natAbs f.c.natAbs) = 1

theorem quadratic_shift (f : Quadratic) (x t : Rat) :
    f.eval (x + t) = f.eval x + f.derivative x * t + (f.a : Rat) * t ^ 2 := by
  simp only [Quadratic.eval, Quadratic.derivative]
  ring

theorem discriminant_identity (f : Quadratic) (x : Rat) :
    f.derivative x ^ 2 - 4 * (f.a : Rat) * f.eval x =
      (f.b : Rat) ^ 2 - 4 * (f.a : Rat) * (f.c : Rat) := by
  simp only [Quadratic.eval, Quadratic.derivative]
  ring

theorem pell_product_norm (D u v x y : Int) :
    (u*x + D*v*y)^2 - D*(v*x + u*y)^2 =
      (u^2-D*v^2)*(x^2-D*y^2) := by
  ring

def dsJump (rho : Nat → Nat) (R : Nat) : Nat :=
  max (R + 2) (8 * 2 ^ rho R)

def dsIndependentBound (rho : Nat → Nat) (R : Nat) : Nat :=
  max (R + 1) (32 * 2 ^ rho (2 * R ^ 2) + 1)

def dsThreshold (rho : Nat → Nat) (h : Nat) : Nat :=
  max 16385 (32768 * h * 2 ^ rho h + 1)

def dsCoreBound (rho : Nat → Nat) (T : Nat) : Nat :=
  let A := dsJump rho T
  let A' := dsJump rho A
  let U := dsJump rho (dsIndependentBound rho A')
  let R := max (U + 1) (16 * 2 ^ rho U + 1)
  let V := dsJump rho R
  let V' := dsJump rho V
  dsJump rho (dsIndependentBound rho V')

def dsRealBound (rho : Nat → Nat) (h : Nat) : Nat :=
  let sigma := fun H => rho H + 1
  dsCoreBound sigma (dsThreshold sigma h)

def dsFreezePrecision (rho : Nat → Nat) (h : Nat) : Nat :=
  let B := dsRealBound rho h
  let W := 2 * B ^ 2
  rho W + 8 * W + 3 * B + 10

def finiteSeparation (x : Rat) (rho : Nat → Nat) (W : Nat) : Prop :=
  ∀ H, 1 ≤ H → H ≤ W → ∀ f : Quadratic,
    0 < f.height → f.height ≤ H →
      (1 : Rat) / (2 : Rat) ^ rho H ≤ |f.eval x|

def largeDerivative (x : Rat) (f : Quadratic) : Prop :=
  (f.height : Rat) ^ 3 * |f.eval x| < 4096 * |f.derivative x|

def finiteDSTarget (x : Rat) (rho : Nat → Nat) (T : Nat) : Prop :=
  let B := dsCoreBound rho T
  0 < x → x < 1 → 16385 ≤ T → Monotone rho →
    finiteSeparation x rho (2 * B ^ 2) →
      ∃ f : Quadratic, f.primitive ∧ T < f.height ∧
        f.height ≤ B ∧ largeDerivative x f

def rothUpperError (r : Rat) (p : Int) (q k : Nat) : Rat :=
  |(p : Rat) / (q : Rat) - r| + (1 : Rat) / (2 : Rat) ^ k

def rothGoodCertificate (r : Rat) (p : Int) (q a b k : Nat) : Prop :=
  0 < q ∧ 0 < a ∧ 0 < b ∧
    (q : Rat) ^ (2 * b + a) * rothUpperError r p q k ^ b < 1

def finiteLiouvilleTarget (r : Rat) (p : Int) (q k K d : Nat) : Prop :=
  0 < q → 0 < K →
    (1 : Rat) / ((K : Rat) * (q : Rat) ^ d) ≤ rothUpperError r p q k

/-
The main pending theorems are the correctness of a concrete neighbors
implementation, finiteDSTarget under its displayed hypotheses, and
finiteLiouvilleTarget from the polynomial/bisection certificates.

The higher-order rho parameter here is a convenient METATHEORETIC Lean
parameter.  For an object-iPRA instance it must be replaced by a fixed PR
symbol/definition; it is not a function quantifier inside first-order iPRA.
-/

end DiophantineIPRA
