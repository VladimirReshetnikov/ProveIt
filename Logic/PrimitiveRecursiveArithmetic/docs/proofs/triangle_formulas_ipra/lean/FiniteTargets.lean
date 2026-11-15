import Mathlib.Tactic

/-!
# Exact quantitative theorem specifications matching Section 8 of the paper

STATUS: proposition definitions only, not proved theorems.  This file was
not compiled in the delivery environment.  The parameter `rho` is intended
to be the rational root routine specified in `DyadicSpec.lean`; the
implementation/correspondence and `RootContract` proof remain obligations.
These targets are stated in ambient Lean.  They must subsequently be coded
and proved as `Prf PRAAx` targets as explained in `ObjectTargets.lean`.

All precision choices are literal copies of the paper's conservative
schedules, rather than unspecified existence of a modulus.
-/

namespace TriangleIPRA.FiniteTargets

def eps (k : ℕ) : ℚ := 1 / (2 : ℚ) ^ k

def uSq (x y : ℚ) : ℚ := x ^ 2 + y ^ 2

def vSq (z w : ℚ) : ℚ := z ^ 2 + w ^ 2

def wSq (x y z w : ℚ) : ℚ := (x - z) ^ 2 + (y - w) ^ 2

def dot (x y z w : ℚ) : ℚ := x * z + y * w

def det (x y z w : ℚ) : ℚ := x * w - y * z

/-- Contract supplied by the bounded root scan, for each rational input. -/
def RootContract (rho : ℚ → ℕ → ℚ) : Prop :=
  ∀ (q : ℚ) (k : ℕ), 0 ≤ q →
    0 ≤ rho q k ∧ (rho q k) ^ 2 ≤ q ∧
      q < (rho q k + eps k) ^ 2

/-- Section 8.1, including the final radical and the degenerate cases.
This definition names the proof obligation; it does not prove it. -/
def finiteHeron (rho : ℚ → ℕ → ℚ) : Prop :=
  RootContract rho →
  ∀ (x y z w : ℚ) (Q k : ℕ),
    1 ≤ Q →
    uSq x y ≤ (Q : ℚ) ^ 2 →
    vSq z w ≤ (Q : ℚ) ^ 2 →
    wSq x y z w ≤ (Q : ℚ) ^ 2 →
    let n := 2 * k + 4 + 3 * Q
    let a := rho (wSq x y z w) n
    let b := rho (vSq z w) n
    let c := rho (uSq x y) n
    let s := (a + b + c) / 2
    let P := s * (s - a) * (s - b) * (s - c)
    let H := rho (max P 0) (k + 1)
    let area := |det x y z w| / 2
    |H - area| ≤ eps k

/-- Section 8.2: denominator positivity, three cosine residuals, exact finite
sine-ratio equalities, and comparison with the computed circumradius.
This definition names the proof obligation; it does not prove it. -/
def finiteTrig (rho : ℚ → ℕ → ℚ) : Prop :=
  RootContract rho →
  ∀ (x y z w : ℚ) (M d k : ℕ),
    1 ≤ M →
    |x| ≤ (M : ℚ) → |y| ≤ (M : ℚ) →
    |z| ≤ (M : ℚ) → |w| ≤ (M : ℚ) →
    eps d ≤ |det x y z w| →
    let Q := 4 * M
    let n := 2 * k + 2 * d + 5 * Q + 8
    let U := uSq x y
    let V := vSq z w
    let W := wSq x y z w
    let p := dot x y z w
    let t := det x y z w
    let h := |t|
    let a := rho W n
    let b := rho V n
    let c := rho U n
    let CA := p / (b * c)
    let CB := (U - p) / (c * a)
    let CC := (V - p) / (a * b)
    let SA := h / (b * c)
    let SB := h / (c * a)
    let SC := h / (a * b)
    let ox := (U * w - V * y) / (2 * t)
    let oy := (V * x - U * z) / (2 * t)
    let QR := ox ^ 2 + oy ^ 2
    let radius := rho QR (k + 2)
    let K := a * b * c / h
    0 < a ∧ 0 < b ∧ 0 < c ∧ t ≠ 0 ∧
    0 < SA ∧ 0 < SB ∧ 0 < SC ∧
    |a ^ 2 - b ^ 2 - c ^ 2 + 2 * b * c * CA| ≤ eps k ∧
    |b ^ 2 - c ^ 2 - a ^ 2 + 2 * c * a * CB| ≤ eps k ∧
    |c ^ 2 - a ^ 2 - b ^ 2 + 2 * a * b * CC| ≤ eps k ∧
    a / SA = K ∧ b / SB = K ∧ c / SC = K ∧
    |K - 2 * radius| ≤ eps k

end TriangleIPRA.FiniteTargets
