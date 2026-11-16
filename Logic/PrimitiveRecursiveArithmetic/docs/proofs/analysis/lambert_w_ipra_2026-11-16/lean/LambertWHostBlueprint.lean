import Mathlib
import ConciseIPRA.NativeBiInterpretation

/-!
# Lambert W: host-level constructive blueprint

This file states the intended Lean interfaces.  It is deliberately a blueprint:
proofs marked `sorry` are the obligations described in the accompanying paper.
The target toolchain is the ProveIt root toolchain (Lean/mathlib v4.32.0 at the
inspected repository revision).

The formalization has two layers:

1. this host-level layer, where rapid rational names are related to `ℝ` and the
   mathematics can use Mathlib's real analysis;
2. `LambertWObjectBlueprint.lean`, where the bounded algorithms and their
   invariants are represented using `PR`, `PTm`, `PRAAx`, `Prf`, and
   `PRA.qfInd`.
-/

namespace LambertWIPRA

open scoped BigOperators

/-- The rational radius `2⁻ᵖ` used throughout the packet. -/
def radius (p : ℕ) : ℚ := 1 / (2 ^ p : ℚ)

/-- A regular rational name.  The deliberately redundant bound is stable under
primitive-recursive arithmetic on names. -/
structure RapidReal where
  approx : ℕ → ℚ
  regular : ∀ p q, |approx p - approx q| ≤ radius p + radius q

/-- Extensional equality of rapid names. -/
def RapidReal.Eqv (x y : RapidReal) : Prop :=
  ∀ p, |x.approx (p + 2) - y.approx (p + 2)| ≤ radius p

/-- Positive separation, the constructive replacement for a negative equality
hypothesis in every division rule. -/
def RapidReal.Apart (x y : RapidReal) : Prop :=
  ∃ p, radius p < |x.approx (p + 2) - y.approx (p + 2)|

/-- A host real realizes a rapid name.  The object theory never quantifies over
`ℝ`; this relation is used only for the correctness bridge. -/
def RapidReal.Realizes (x : RapidReal) (r : ℝ) : Prop :=
  ∀ p, |(x.approx p : ℝ) - r| ≤ (radius p : ℝ)

/-- Integer, rational, addition, negation, multiplication, and bounded
summation names are implemented first. -/
def RapidReal.ofRat (q : ℚ) : RapidReal := by sorry

def RapidReal.add (x y : RapidReal) : RapidReal := by sorry

def RapidReal.neg (x : RapidReal) : RapidReal := by sorry

def RapidReal.mul (x y : RapidReal) : RapidReal := by sorry

/-- Division consumes an apartness witness and therefore contains no hidden
case split on equality of real names. -/
def RapidReal.div (x y : RapidReal) (hy : y.Apart (RapidReal.ofRat 0)) : RapidReal := by sorry

/-- The exponential name is the factorial polynomial with outward rational
rounding and a primitive-recursive truncation index. -/
def RapidReal.exp (x : RapidReal) : RapidReal := by sorry

/-- The logarithm name is range reduction plus the atanh series; positivity is
supplied as data. -/
def RapidReal.log (x : RapidReal) (hx : ∃ q : ℚ, 0 < q ∧ ∀ p, q ≤ x.approx p + radius p) : RapidReal := by sorry

/-- Correctness statements for the analytic primitives. -/
theorem RapidReal.realizes_exp {x : RapidReal} {r : ℝ}
    (hx : x.Realizes r) : (RapidReal.exp x).Realizes (Real.exp r) := by sorry

/-- The ordinary real map whose inverse is Lambert W. -/
def F (w : ℝ) : ℝ := w * Real.exp w

@[simp] theorem F_neg_one : F (-1) = -(Real.exp (-1)) := by
  simp [F]

/-- Principal and secondary real-branch specifications. -/
def PrincipalSpec (x w : ℝ) : Prop := -1 ≤ w ∧ F w = x

def SecondarySpec (x w : ℝ) : Prop := w ≤ -1 ∧ F w = x

/-- Monotonicity of `F` on the two intervals.  A completion should prove this
from the derivative and then package an effective slope lower bound on every
rational compact interval separated from `-1`. -/
theorem F_strictMono_principal : StrictMonoOn F (Set.Ici (-1)) := by sorry

theorem F_strictAnti_secondary : StrictAntiOn F (Set.Iic (-1)) := by sorry

/-- Classical host statement corresponding to the constructive interval-search
algorithm. -/
theorem principal_exists_unique {x : ℝ} (hx : -(Real.exp (-1)) ≤ x) :
    ∃! w, PrincipalSpec x w := by sorry

theorem secondary_exists_unique {x : ℝ}
    (hlo : -(Real.exp (-1)) ≤ x) (hhi : x < 0) :
    ∃! w, SecondarySpec x w := by sorry

/-- Host definitions are introduced only after uniqueness is proved. -/
noncomputable def W0 (x : ℝ) (hx : -(Real.exp (-1)) ≤ x) : ℝ :=
  Classical.choose (principal_exists_unique hx)

noncomputable def Wm1 (x : ℝ)
    (hlo : -(Real.exp (-1)) ≤ x) (hhi : x < 0) : ℝ :=
  Classical.choose (secondary_exists_unique hlo hhi)

theorem W0_spec (x : ℝ) (hx : -(Real.exp (-1)) ≤ x) :
    PrincipalSpec x (W0 x hx) := by sorry

theorem Wm1_spec (x : ℝ) (hlo : -(Real.exp (-1)) ≤ x) (hhi : x < 0) :
    SecondarySpec x (Wm1 x hlo hhi) := by sorry

/-- The certified implementation returns a rapid name and an interval invariant,
not a choice term. -/
structure PrincipalCertificate (x : RapidReal) where
  value : RapidReal
  lower : ℕ → ℚ
  upper : ℕ → ℚ
  nested : ∀ p, lower p ≤ lower (p + 1) ∧ upper (p + 1) ≤ upper p
  width : ∀ p, upper p - lower p ≤ radius p
  range : ∀ p, -1 ≤ lower p
  residualSign : ∀ p, True  -- replace by interval signs for F(lower)-x and F(upper)-x

/-- Bisection over rational intervals; its body is a bounded primitive recursion
once an initial branch bracket is supplied. -/
def principalSearch (x : RapidReal) : PrincipalCertificate x := by sorry

/-- Correctness bridge between the interval algorithm and the host inverse. -/
theorem principalSearch_realizes {x : RapidReal} {xr : ℝ}
    (hx : x.Realizes xr) (hdom : -(Real.exp (-1)) ≤ xr) :
    (principalSearch x).value.Realizes (W0 xr hdom) := by sorry

/-! ## Finite truncated series -/

/-- Coefficient vector for `Q[X]/(X^(N+1))`. -/
abbrev TruncSeries (N : ℕ) := Fin (N + 1) → ℚ

/-- Bounded Cauchy multiplication. -/
def TruncSeries.mul {N : ℕ} (a b : TruncSeries N) : TruncSeries N := by sorry

/-- Bounded composition, guarded by a zero constant coefficient. -/
def TruncSeries.comp {N : ℕ} (a b : TruncSeries N) (hb0 : b 0 = 0) : TruncSeries N := by sorry

/-- Truncated exponential. -/
def TruncSeries.exp {N : ℕ} (a : TruncSeries N) (ha0 : a 0 = 0) : TruncSeries N := by sorry

/-- The exact Lambert coefficient. -/
def lambertCoeff (n : ℕ) : ℚ :=
  if h : n = 0 then 0 else (↑((- (n : ℤ)) ^ (n - 1)) : ℚ) / Nat.factorial n

/-- The vector of the first `N` Lambert coefficients. -/
def lambertTrunc (N : ℕ) : TruncSeries N := fun i => lambertCoeff i

/-- Central finite theorem.  The object-language formalization should prove the
encoded coefficient equality by `PRA.qfInd`; the host proof can use the finite
Lagrange--Bürmann lemma from the companion packet. -/
theorem lambertTrunc_defining (N : ℕ) :
    True := by
  -- Replace `True` by equality in `TruncSeries N` after the vector API is fixed:
  -- `lambertTrunc N * exp (lambertTrunc N) = X`.
  trivial

/-- Polynomial recurrence for the higher derivatives. -/
def derivPoly : ℕ → Polynomial ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let P := derivPoly (n + 1)
      (Polynomial.X + 1) * P.derivative +
        (Polynomial.C (1 - 3 * Int.ofNat (n + 1)) -
          Polynomial.C (Int.ofNat (n + 1)) * Polynomial.X) * P

/-- Completion target for the derivative theorem. -/
theorem higherDerivative_formula (n : ℕ) (hn : 1 ≤ n) : True := by
  -- State using `HasDerivAt`/`iteratedDeriv` on a branch neighborhood and prove
  -- by induction after changing variables from `z` to `w`.
  trivial

/-! ## Formalization order

A complete development should proceed in this order:

* finite encodings and bounded folds;
* rapid-name arithmetic, apartness, exp/log tail bounds;
* monotone branch search and correctness;
* truncated-series Lagrange inversion;
* derivative/integral/asymptotic/bound modules;
* translation of every bounded invariant to an object-language `Fm PTm n`;
* `PRA.qfInd` proofs and transfer through `pra_iff_native`.
-/

end LambertWIPRA
