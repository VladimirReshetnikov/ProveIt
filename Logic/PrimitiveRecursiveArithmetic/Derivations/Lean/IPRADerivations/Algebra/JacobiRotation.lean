import IPRADerivations.Core.Tactic

/-!
# The algebra of a rational Jacobi rotation

Packet: `algebra/ipra_stable_observables` (Section "A rational approximate spectral theorem":
`eq:pivot`, the row invariance behind `eq:energy`, both branches of `lem:pivot`; and the Lagrange
identity behind the finite Cauchy–Schwarz inequality of Section "Finite rational linear
algebra"). A symmetric matrix has the pivot block `[[a, b], [b, d]]`, and a plane rotation has
the block `[[c, −s], [s, c]]`. All statements are polynomial identities over the integers,
cleared of denominators.

* `pivot`: the off-diagonal entry of `Gᵀ A G` is `(c² − s²) b − c s (a − d)`;
* `row_invariant`: `(c x + s y)² + (−s x + c y)² = (c² + s²)(x² + y²)`, so a rotation preserves
  the squared sum of each off-pivot pair;
* `rational_circle`: `(1 − t²)² + (2t)² = (1 + t²)²`, i.e. `c = (1 − t²)/(1 + t²)`,
  `s = 2t/(1 + t²)` satisfy `c² + s² = 1`;
* `high_branch`: with `b = 4 h t` and that rotation, `2 (1 + t²)² b′ = b (1 − 11 t² + 2 t⁴)`;
* `low_branch`: for `c = 3/5`, `s = ±4/5` the two pivots are `(−7b ∓ 12h)/25`, and
  `(−7b − 12h)² + (−7b + 12h)² = 2 (49 b² + 144 h²)`;
* `lagrange2`, `lagrange3`: `(∑ uᵢ²)(∑ vᵢ²) − (∑ uᵢvᵢ)² = ∑_{i<j} (uᵢvⱼ − uⱼvᵢ)²` for two and
  three terms.

The inequalities of `lem:pivot`, the fuel bound and the diagonalization theorem are not
formalized.
-/

namespace LeanProofs.IPRA.Algebra.JacobiRotation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

abbrev p4 {n : ℕ} (u : ZT n) : ZT n := u * u * u * u

section Rotation

abbrev a : ZT 12 := .var2 0 1
abbrev b : ZT 12 := .var2 2 3
abbrev d : ZT 12 := .var2 4 5
abbrev c : ZT 12 := .var2 6 7
abbrev s : ZT 12 := .var2 8 9
abbrev y : ZT 12 := .var2 10 11

/-- `(Gᵀ A G)₀₁ = (c a + s b)(−s) + (c b + s d) c`. -/
def pivotFormula : Fm PTm 12 :=
  ZT.eq ((c * a + s * b) * (-s) + (c * b + s * d) * c) ((c * c - s * s) * b - c * s * (a - d))

/-- A rotation preserves the squared sum of a pair `(x, y)`; here `x = a`. -/
def rowFormula : Fm PTm 12 :=
  ZT.eq (ZT.sq (c * a + s * y) + ZT.sq (-(s * a) + c * y)) ((c * c + s * s) * (a * a + y * y))

theorem pivot_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] pivotFormula := by
  unfold pivotFormula; ipra_ring

theorem row_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] rowFormula := by
  unfold rowFormula; ipra_ring

/-- `eq:pivot`. -/
theorem pivot : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 pivotFormula := closeAll 12 pivot_open

/-- The row invariance behind `eq:energy`. -/
theorem row_invariant : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 rowFormula := closeAll 12 row_open

end Rotation

section Branches

abbrev t : ZT 6 := .var2 0 1
abbrev h : ZT 6 := .var2 2 3
abbrev b' : ZT 6 := .var2 4 5

def circleFormula : Fm PTm 6 :=
  ZT.eq (ZT.sq (ZT.natLit 1 - t * t) + ZT.sq (ZT.natLit 2 * t)) (ZT.sq (ZT.natLit 1 + t * t))

/-- With `b = 4 h t`, `C = 1 − t²`, `S = 2t` (numerators over `1 + t²`):
`2 ((C² − S²) b − C S h) = b (1 − 11 t² + 2 t⁴)`. -/
def highFormula : Fm PTm 6 :=
  ZT.eq (ZT.natLit 2 * ((ZT.sq (ZT.natLit 1 - t * t) - ZT.sq (ZT.natLit 2 * t)) * (ZT.natLit 4 * h * t) -
      (ZT.natLit 1 - t * t) * (ZT.natLit 2 * t) * h))
    ((ZT.natLit 4 * h * t) * (ZT.natLit 1 - ZT.natLit 11 * (t * t) + ZT.natLit 2 * p4 t))

/-- With `c = 3`, `s = ±4` (numerators over `5`): the pivots `(9 − 16) b ∓ 12 h`, and their
squares. Here `b = b'`. -/
def lowFormula : Fm PTm 6 :=
  (ZT.eq ((ZT.natLit 9 - ZT.natLit 16) * b' - ZT.natLit 3 * ZT.natLit 4 * h) (-(ZT.natLit 7 * b') - ZT.natLit 12 * h)) ⋏
    ((ZT.eq (ZT.natLit 9 + ZT.natLit 16) (ZT.natLit 25)) ⋏
      ZT.eq (ZT.sq (-(ZT.natLit 7 * b') - ZT.natLit 12 * h) + ZT.sq (-(ZT.natLit 7 * b') + ZT.natLit 12 * h))
        (ZT.natLit 2 * (ZT.natLit 49 * (b' * b') + ZT.natLit 144 * (h * h))))

theorem circle_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] circleFormula := by
  unfold circleFormula; ipra_ring

theorem high_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] highFormula := by
  unfold highFormula; ipra_ring

theorem low_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] lowFormula := by
  unfold lowFormula
  exact .andI (by ipra_ring) (.andI (by ipra_ring) (by ipra_ring))

/-- `(1 − t²)² + (2t)² = (1 + t²)²`. -/
theorem rational_circle : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 circleFormula := closeAll 6 circle_open

/-- The high-difference branch of `lem:pivot`. -/
theorem high_branch : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 highFormula := closeAll 6 high_open

/-- The low-difference branch of `lem:pivot`. -/
theorem low_branch : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 lowFormula := closeAll 6 low_open

end Branches

section Lagrange

abbrev u₁ : ZT 12 := .var2 0 1
abbrev u₂ : ZT 12 := .var2 2 3
abbrev u₃ : ZT 12 := .var2 4 5
abbrev v₁ : ZT 12 := .var2 6 7
abbrev v₂ : ZT 12 := .var2 8 9
abbrev v₃ : ZT 12 := .var2 10 11

def lagrange2Formula : Fm PTm 12 :=
  ZT.eq ((u₁ * u₁ + u₂ * u₂) * (v₁ * v₁ + v₂ * v₂)) (ZT.sq (u₁ * v₁ + u₂ * v₂) + ZT.sq (u₁ * v₂ - u₂ * v₁))

def lagrange3Formula : Fm PTm 12 :=
  ZT.eq ((u₁ * u₁ + u₂ * u₂ + u₃ * u₃) * (v₁ * v₁ + v₂ * v₂ + v₃ * v₃))
    (ZT.sq (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) + ZT.sq (u₁ * v₂ - u₂ * v₁) + ZT.sq (u₁ * v₃ - u₃ * v₁) +
      ZT.sq (u₂ * v₃ - u₃ * v₂))

theorem lagrange2_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] lagrange2Formula := by
  unfold lagrange2Formula; ipra_ring

theorem lagrange3_open : ([] : List (Fm PTm 12)) ⊢[PRAAx] lagrange3Formula := by
  unfold lagrange3Formula; ipra_ring

/-- Lagrange's identity for two terms. -/
theorem lagrange2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 lagrange2Formula := closeAll 12 lagrange2_open

/-- Lagrange's identity for three terms. -/
theorem lagrange3 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 lagrange3Formula := closeAll 12 lagrange3_open

end Lagrange

end LeanProofs.IPRA.Algebra.JacobiRotation
