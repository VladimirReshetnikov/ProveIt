import IPRADerivations.Geometry.ConwayAlgebra
import IPRADerivations.Core.IntCancel
import IPRADerivations.Core.LinearCombination

/-!
# The period lattice of the Conway criterion

Packet: `geometry/conway_criterion_ipra_2026-11-16`, `cor:lattice` (Section 4) and the lattice
coordinates `eq:latticecoords` (Section 5). The periods are `t = (t₁, t₂)` and `u = (u₁, u₂)`
with integer coordinates (`ZT`), `D = det(t, u)`.

The packet's coordinates `α(x) = det(x, u) / D` and `β(x) = det(t, x) / D` are rational. Here
they are used in cleared form: the pair `(det(x, u), det(t, x))` with the common denominator `D`.

* `zpos`, `zpos_congr`, `zpos_ne`: positivity of an integer term, its invariance under integer
  equality, and `X > 0 → X ≠ 0`;
* `lattice_indep` (`cor:lattice`, linear independence): if `D ≠ 0` and `α t + β u = 0` then
  `α = 0` and `β = 0`;
* `coeff_unique`: if `D ≠ 0` and `a t + b u = a' t + b' u` then `a = a'` and `b = b'`;
* `cramer₁`, `cramer₂` (`eq:latticecoords`, cleared): `D x = det(x, u) t + det(t, x) u`;
* `coords_of_mem`: if `x = a t + b u` then `det(x, u) = a D` and `det(t, x) = b D`;
* `mem_of_coords`: if `D ≠ 0`, `det(x, u) = a D` and `det(t, x) = b D` then `x = a t + b u`.
  So `x` is in the lattice `ℤ t + ℤ u` exactly when `D` divides both cleared coordinates;
* `coord_shift_t`, `coord_shift_u`, `coord_half`: the cleared coordinates of `x + t`, `x + u`
  and of the half-turn image `s − x`: a translation by a period changes one cleared coordinate
  by `D` and fixes the other;
* `period_det_eq`, `period_det_pos`, `period_lattice` (`cor:lattice`): from the five path
  relations of `thm:periodarea` and `J(∂T) = A` with `A > 0` (`A` is twice the tile area),
  `det(t, u) = A`, `det(t, u) > 0`, and the periods are linearly independent.

The identification of the boundary shoelace sum with twice the area of the disk certificate is
a hypothesis here (`J(∂T) = A`, `A > 0`).
-/

namespace LeanProofs.IPRA.Geometry.ConwayLattice

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.ConwayAlgebra (det period_area_paths)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Positive integer terms -/

/-- `X > 0` for an integer term `X = X.pos − X.neg`. -/
abbrev zpos (X : ZT n) : Fm PTm n := lt X.neg X.pos

/-- Positivity respects integer equality. -/
theorem zpos_congr {X Y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq X Y) (hY : Γ ⊢[PRAAx] zpos Y) :
    Γ ⊢[PRAAx] zpos X := by
  have a : Γ ⊢[PRAAx] le (succ Y.neg + X.neg) (Y.pos + X.neg) := add_le_add_right X.neg hY
  have e₁ : Γ ⊢[PRAAx] succ Y.neg + X.neg ≐ succ X.neg + Y.neg := by
    ipra_ring
  have h' : Γ ⊢[PRAAx] X.pos + Y.neg ≐ Y.pos + X.neg := h
  exact le_of_add_le_add_right (le_congr e₁ h'.eqSymm a)

/-- A positive integer term is nonzero. -/
theorem zpos_ne {X : ZT n} (h : Γ ⊢[PRAAx] zpos X) :
    Γ ⊢[PRAAx] neg (ZT.eq X (ZT.natLit 0)) := by
  refine .impI (lt_irrefl X.neg _ ?_)
  have e : (ZT.eq X (ZT.natLit 0) :: Γ) ⊢[PRAAx] X.pos + zero ≐ num 0 + X.neg := Prf.hyp0
  have e' : (ZT.eq X (ZT.natLit 0) :: Γ) ⊢[PRAAx] X.pos ≐ X.neg := by
    have r := natEq e
    apply deriveNat; ipra_simps
    try simp only [Nat.cast_zero] at *
    linear_combination r
  exact lt_congr (.eqRefl _) e' h.wk

/-! ## Linear independence -/

section Independence

variable {α β t₁ t₂ u₁ u₂ : ZT n}

theorem det_mul_left
    (h₁ : Γ ⊢[PRAAx] ZT.eq (α * t₁ + β * u₁) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (α * t₂ + β * u₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ u₁ u₂ * α) (ZT.natLit 0) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  try simp only [Nat.cast_zero] at *
  linear_combination (ZT.toZ Γ u₂) * e₁ - (ZT.toZ Γ u₁) * e₂

theorem det_mul_right
    (h₁ : Γ ⊢[PRAAx] ZT.eq (α * t₁ + β * u₁) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (α * t₂ + β * u₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ u₁ u₂ * β) (ZT.natLit 0) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  try simp only [Nat.cast_zero] at *
  linear_combination (ZT.toZ Γ t₁) * e₂ - (ZT.toZ Γ t₂) * e₁

/-- `cor:lattice`: with `det(t, u) ≠ 0`, the periods are linearly independent over the
integers. -/
theorem lattice_indep (hD : Γ ⊢[PRAAx] neg (ZT.eq (det t₁ t₂ u₁ u₂) (ZT.natLit 0)))
    (h₁ : Γ ⊢[PRAAx] ZT.eq (α * t₁ + β * u₁) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (α * t₂ + β * u₂) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq α (ZT.natLit 0) ⋏ ZT.eq β (ZT.natLit 0) :=
  .andI (zt_mul_cancel_left hD (det_mul_left h₁ h₂)) (zt_mul_cancel_left hD (det_mul_right h₁ h₂))

/-- An integer term that vanishes after subtraction: `X − Y = 0` gives `X = Y`. -/
theorem eq_of_sub_zero {X Y : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (X - Y) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq X Y := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  try simp only [Nat.cast_zero] at *
  linear_combination e

/-- The coefficients of a lattice vector in the basis `t, u` are unique. -/
theorem coeff_unique {a b a' b' : ZT n}
    (hD : Γ ⊢[PRAAx] neg (ZT.eq (det t₁ t₂ u₁ u₂) (ZT.natLit 0)))
    (h₁ : Γ ⊢[PRAAx] ZT.eq (a * t₁ + b * u₁) (a' * t₁ + b' * u₁))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (a * t₂ + b * u₂) (a' * t₂ + b' * u₂)) :
    Γ ⊢[PRAAx] ZT.eq a a' ⋏ ZT.eq b b' := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  have g₁ : Γ ⊢[PRAAx] ZT.eq ((a - a') * t₁ + (b - b') * u₁) (ZT.natLit 0) := by
    apply ZT.derive
    ipra_simps
    try simp only [Nat.cast_zero] at *
    linear_combination e₁
  have g₂ : Γ ⊢[PRAAx] ZT.eq ((a - a') * t₂ + (b - b') * u₂) (ZT.natLit 0) := by
    apply ZT.derive
    ipra_simps
    try simp only [Nat.cast_zero] at *
    linear_combination e₂
  have r := lattice_indep hD g₁ g₂
  exact .andI (eq_of_sub_zero (Prf.andE₁ r)) (eq_of_sub_zero (Prf.andE₂ r))

end Independence

/-! ## Lattice coordinates -/

section Coordinates

variable (t₁ t₂ u₁ u₂ x₁ x₂ : ZT n)

/-- `eq:latticecoords`, first coordinate, cleared of the denominator `det(t, u)`. -/
theorem cramer₁ : Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ u₁ u₂ * x₁)
    (det x₁ x₂ u₁ u₂ * t₁ + det t₁ t₂ x₁ x₂ * u₁) := by
  ipra_ring

/-- `eq:latticecoords`, second coordinate, cleared of the denominator `det(t, u)`. -/
theorem cramer₂ : Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ u₁ u₂ * x₂)
    (det x₁ x₂ u₁ u₂ * t₂ + det t₁ t₂ x₁ x₂ * u₂) := by
  ipra_ring

/-- Translating by `t` adds `det(t, u)` to the first cleared coordinate and fixes the second. -/
theorem coord_shift_t :
    Γ ⊢[PRAAx] ZT.eq (det (x₁ + t₁) (x₂ + t₂) u₁ u₂) (det x₁ x₂ u₁ u₂ + det t₁ t₂ u₁ u₂) ⋏
      ZT.eq (det t₁ t₂ (x₁ + t₁) (x₂ + t₂)) (det t₁ t₂ x₁ x₂) :=
  .andI (by ipra_ring) (by ipra_ring)

/-- Translating by `u` fixes the first cleared coordinate and adds `det(t, u)` to the second. -/
theorem coord_shift_u :
    Γ ⊢[PRAAx] ZT.eq (det (x₁ + u₁) (x₂ + u₂) u₁ u₂) (det x₁ x₂ u₁ u₂) ⋏
      ZT.eq (det t₁ t₂ (x₁ + u₁) (x₂ + u₂)) (det t₁ t₂ x₁ x₂ + det t₁ t₂ u₁ u₂) :=
  .andI (by ipra_ring) (by ipra_ring)

/-- The cleared coordinates of the half-turn image `s − x`. -/
theorem coord_half (s₁ s₂ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (det (s₁ - x₁) (s₂ - x₂) u₁ u₂) (det s₁ s₂ u₁ u₂ - det x₁ x₂ u₁ u₂) ⋏
      ZT.eq (det t₁ t₂ (s₁ - x₁) (s₂ - x₂)) (det t₁ t₂ s₁ s₂ - det t₁ t₂ x₁ x₂) :=
  .andI (by ipra_ring) (by ipra_ring)

end Coordinates

section Membership

variable {t₁ t₂ u₁ u₂ x₁ x₂ a b : ZT n}

/-- A lattice vector `x = a t + b u` has cleared coordinates `a det(t, u)` and `b det(t, u)`. -/
theorem coords_of_mem
    (h₁ : Γ ⊢[PRAAx] ZT.eq x₁ (a * t₁ + b * u₁)) (h₂ : Γ ⊢[PRAAx] ZT.eq x₂ (a * t₂ + b * u₂)) :
    Γ ⊢[PRAAx] ZT.eq (det x₁ x₂ u₁ u₂) (a * det t₁ t₂ u₁ u₂) ⋏
      ZT.eq (det t₁ t₂ x₁ x₂) (b * det t₁ t₂ u₁ u₂) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  refine .andI ?_ ?_
  · ipra_lc (ZT.toZ Γ u₂) * e₁ - (ZT.toZ Γ u₁) * e₂
  · ipra_lc (ZT.toZ Γ t₁) * e₂ - (ZT.toZ Γ t₂) * e₁

/-- If `det(t, u) ≠ 0` and the cleared coordinates of `x` are `a det(t, u)` and `b det(t, u)`,
then `x = a t + b u`. -/
theorem mem_of_coords (hD : Γ ⊢[PRAAx] neg (ZT.eq (det t₁ t₂ u₁ u₂) (ZT.natLit 0)))
    (ha : Γ ⊢[PRAAx] ZT.eq (det x₁ x₂ u₁ u₂) (a * det t₁ t₂ u₁ u₂))
    (hb : Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ x₁ x₂) (b * det t₁ t₂ u₁ u₂)) :
    Γ ⊢[PRAAx] ZT.eq x₁ (a * t₁ + b * u₁) ⋏ ZT.eq x₂ (a * t₂ + b * u₂) := by
  have ea := ZT.toZ_eq ha; have eb := ZT.toZ_eq hb
  have g₁ : Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ u₁ u₂ * (x₁ - (a * t₁ + b * u₁))) (ZT.natLit 0) := by
    apply ZT.derive
    ipra_simps
    try simp only [Nat.cast_zero] at *
    linear_combination (ZT.toZ Γ t₁) * ea + (ZT.toZ Γ u₁) * eb
  have g₂ : Γ ⊢[PRAAx] ZT.eq (det t₁ t₂ u₁ u₂ * (x₂ - (a * t₂ + b * u₂))) (ZT.natLit 0) := by
    apply ZT.derive
    ipra_simps
    try simp only [Nat.cast_zero] at *
    linear_combination (ZT.toZ Γ t₂) * ea + (ZT.toZ Γ u₂) * eb
  exact .andI (eq_of_sub_zero (zt_mul_cancel_left hD g₁)) (eq_of_sub_zero (zt_mul_cancel_left hD g₂))

end Membership

/-! ## The nondegenerate period lattice -/

section Period

variable {Ja Jb Jc Jd Je Jf P₁ P₂ Q₁ Q₂ R₁ R₂ S₁ S₂ w₁ w₂ A : ZT n}

/-- `cor:lattice`: `det(t, u)` equals the boundary shoelace sum `A` (twice the tile area). -/
theorem period_det_eq
    (had : Γ ⊢[PRAAx] ZT.eq (Ja + Jd) (-(det w₁ w₂ (Q₁ - P₁) (Q₂ - P₂))))
    (hb : Γ ⊢[PRAAx] ZT.eq Jb (det Q₁ Q₂ R₁ R₂))
    (hc : Γ ⊢[PRAAx] ZT.eq Jc (det R₁ R₂ (Q₁ + w₁) (Q₂ + w₂)))
    (he : Γ ⊢[PRAAx] ZT.eq Je (det (P₁ + w₁) (P₂ + w₂) S₁ S₂))
    (hf : Γ ⊢[PRAAx] ZT.eq Jf (det S₁ S₂ P₁ P₂))
    (hA : Γ ⊢[PRAAx] ZT.eq (Ja + Jb + Jc + Jd + Je + Jf) A) :
    Γ ⊢[PRAAx] ZT.eq (det w₁ w₂ (P₁ + w₁ + S₁ - Q₁ - R₁) (P₂ + w₂ + S₂ - Q₂ - R₂)) A := by
  have e := ZT.toZ_eq (period_area_paths had hb hc he hf)
  have e' := ZT.toZ_eq hA
  apply ZT.derive
  linear_combination e' - e

/-- `cor:lattice`: the fundamental parallelogram is positively oriented, `det(t, u) > 0`. -/
theorem period_det_pos
    (had : Γ ⊢[PRAAx] ZT.eq (Ja + Jd) (-(det w₁ w₂ (Q₁ - P₁) (Q₂ - P₂))))
    (hb : Γ ⊢[PRAAx] ZT.eq Jb (det Q₁ Q₂ R₁ R₂))
    (hc : Γ ⊢[PRAAx] ZT.eq Jc (det R₁ R₂ (Q₁ + w₁) (Q₂ + w₂)))
    (he : Γ ⊢[PRAAx] ZT.eq Je (det (P₁ + w₁) (P₂ + w₂) S₁ S₂))
    (hf : Γ ⊢[PRAAx] ZT.eq Jf (det S₁ S₂ P₁ P₂))
    (hA : Γ ⊢[PRAAx] ZT.eq (Ja + Jb + Jc + Jd + Je + Jf) A) (hpos : Γ ⊢[PRAAx] zpos A) :
    Γ ⊢[PRAAx] zpos (det w₁ w₂ (P₁ + w₁ + S₁ - Q₁ - R₁) (P₂ + w₂ + S₂ - Q₂ - R₂)) :=
  zpos_congr (period_det_eq had hb hc he hf hA) hpos

/-- `cor:lattice`: the periods `t = w` and `u = P + w + S − Q − R` of a Conway datum with
positive area are linearly independent over the integers. -/
theorem period_lattice {α β : ZT n}
    (had : Γ ⊢[PRAAx] ZT.eq (Ja + Jd) (-(det w₁ w₂ (Q₁ - P₁) (Q₂ - P₂))))
    (hb : Γ ⊢[PRAAx] ZT.eq Jb (det Q₁ Q₂ R₁ R₂))
    (hc : Γ ⊢[PRAAx] ZT.eq Jc (det R₁ R₂ (Q₁ + w₁) (Q₂ + w₂)))
    (he : Γ ⊢[PRAAx] ZT.eq Je (det (P₁ + w₁) (P₂ + w₂) S₁ S₂))
    (hf : Γ ⊢[PRAAx] ZT.eq Jf (det S₁ S₂ P₁ P₂))
    (hA : Γ ⊢[PRAAx] ZT.eq (Ja + Jb + Jc + Jd + Je + Jf) A) (hpos : Γ ⊢[PRAAx] zpos A)
    (h₁ : Γ ⊢[PRAAx] ZT.eq (α * w₁ + β * (P₁ + w₁ + S₁ - Q₁ - R₁)) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (α * w₂ + β * (P₂ + w₂ + S₂ - Q₂ - R₂)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq α (ZT.natLit 0) ⋏ ZT.eq β (ZT.natLit 0) :=
  lattice_indep (zpos_ne (period_det_pos had hb hc he hf hA hpos)) h₁ h₂

end Period

end LeanProofs.IPRA.Geometry.ConwayLattice
