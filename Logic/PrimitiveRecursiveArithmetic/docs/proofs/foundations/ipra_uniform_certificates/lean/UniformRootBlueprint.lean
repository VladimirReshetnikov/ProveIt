/-!
# Uniform certificate blueprint for iPRA
This file is a Lean 4 / Mathlib-oriented *outline*, NOT claimed compiled.
The `...Target` definitions are propositions, not proof declarations.
For the final object-language theorem, replace Rat with PR rational codes
and construct `Prf PRAAx` terms as described in framework.tex.
-/
import Mathlib

namespace UniformCertificates

def cubic (x y : ℚ) : ℚ := y*y*y+y-x

def clipped (x : ℚ) : ℚ := min 1 (max 0 x)

def step (x : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  let m := (p.1+p.2)/2
  if cubic x m ≤ 0 then (m,p.2) else (p.1,m)

def interval (x : ℚ) (n : ℕ) : ℚ × ℚ :=
  (step (clipped x))^[n] (0,1)

def approx (x : ℚ) (n : ℕ) : ℚ :=
  let p := interval x n
  (p.1+p.2)/2

-- Key general finite arithmetic lemmas to prove in the native reference layer.
def BracketTarget : Prop :=
  ∀ (x : ℚ) (n : ℕ), 0 ≤ x → x ≤ 1 →
    let p := interval x n
    cubic x p.1 ≤ 0 ∧ 0 ≤ cubic x p.2 ∧
    p.2 - p.1 = (1 : ℚ) / 2^n

def FactorTarget : Prop :=
  ∀ (x y z : ℚ),
    (y-z) * (cubic x y - cubic x z) =
    (y-z)^2 * (y*y+y*z+z*z+1)

def StabilityTarget : Prop :=
  ∀ (x x' y z : ℚ), 0 ≤ y → 0 ≤ z →
    cubic x y = 0 → cubic x' z = 0 →
    |y-z| ≤ |x-x'|

-- Finite stage formulation avoids using a completed real in object iPRA.
def TwoIndexTarget : Prop :=
  ∀ (x : ℚ) (n t : ℕ), 0 ≤ x → x ≤ 1 →
    |approx x n - approx x (n+t)| ≤ (1 : ℚ)/2^n

-- The input evaluator is a fixed primitive-recursive name, NOT an arbitrary
-- Lean function quantified inside iPRA. This is a metatheory specification.
def NameOutput (r : ℕ → ℚ) (k : ℕ) : ℚ :=
  approx (r (k+3)) (k+3)

-- Formalization dependencies:
-- Rat-code PR arithmetic -> cubic factorization -> bracket induction ->
-- two-index fast-name estimate -> modulus/stability -> object Prf PRAAx.
-- Nothing here declares an axiom or uses `sorry` to pretend completion.

end UniformCertificates
