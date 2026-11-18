import IPRADerivations.Geometry.SphericalHalf

/-!
# Half-tangent rational forms (`spherical_trigonometry_ipra_2026-11-15`, (6.16), (6.17))

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, Subsection "Half-tangent rational
forms": with `t_a = tan(a/2)`, …, `t_A = tan(A/2)`, …,

`t_A² = (t_a - t_b + t_c + t_a t_b t_c)(t_a + t_b - t_c + t_a t_b t_c) /
        ((t_a + t_b + t_c - t_a t_b t_c)(-t_a + t_b + t_c + t_a t_b t_c))`   (6.16)

and its polar dual (6.17). "To verify (6.16), write every `sin(p - a)` and `sin p` using the
tangent-of-a-sum formula and cancel the common positive products ... after cross
multiplication, it is directly suitable for an exact certificate checker."

From `half_angle_tan` and `half_side_tan` of `Geometry/SphericalHalf`, with the half-side
(respectively half-angle) unit pairs `(sᵢ, cᵢ)` and tangents given by `sᵢ = tᵢ cᵢ`, in
cross-multiplied form and times the guard `K² = (c₁ c₂ c₃)²` that the packet cancels:

* `half_tangent_angle` (6.16), with `h = sin²(A/2)`, so `t_A² = h / (1 - h)`:
  `K² (t₁ + t₂ + t₃ - t₁t₂t₃)(t₂ + t₃ + t₁t₂t₃ - t₁) h
     = K² (t₁ + t₃ + t₁t₂t₃ - t₂)(t₁ + t₂ + t₁t₂t₃ - t₃)(1 - h)`;
* `half_tangent_side` (6.17), with `k = sin²(a/2)`, so `t_a² = k / (1 - k)`:
  `K² k (t₂t₃ + t₁t₂ + 1 - t₃t₁)(t₂t₃ + t₃t₁ + 1 - t₁t₂)
     = K² (t₂t₃ + t₃t₁ + t₁t₂ - 1)(t₃t₁ + t₁t₂ + 1 - t₂t₃)(1 - k)`.

The remaining five equations are the cyclic relabellings of these two.
-/

namespace LeanProofs.IPRA.Geometry.SphericalHalfTangent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.SphericalHalf
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable {s₁ c₁ s₂ c₂ s₃ c₃ t₁ t₂ t₃ : ZT n}

/-- (6.16), cross-multiplied and times `(c₁ c₂ c₃)²`. -/
theorem half_tangent_angle {cA h : ZT n}
    (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1))
    (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1))
    (law : Γ ⊢[PRAAx] ZT.eq (cosD s₁ c₁)
      (cosD s₂ c₂ * cosD s₃ c₃ + sinD s₂ c₂ * sinD s₃ c₃ * cA))
    (hA : Γ ⊢[PRAAx] ZT.eq cA (ZT.natLit 1 - ZT.natLit 2 * h))
    (ht₁ : Γ ⊢[PRAAx] ZT.eq s₁ (t₁ * c₁)) (ht₂ : Γ ⊢[PRAAx] ZT.eq s₂ (t₂ * c₂))
    (ht₃ : Γ ⊢[PRAAx] ZT.eq s₃ (t₃ * c₃)) :
    Γ ⊢[PRAAx] ZT.eq
      (c₁ * c₂ * c₃ * (c₁ * c₂ * c₃) *
        ((t₁ + t₂ + t₃ - t₁ * t₂ * t₃) * (t₂ + t₃ + t₁ * t₂ * t₃ - t₁) * h))
      (c₁ * c₂ * c₃ * (c₁ * c₂ * c₃) *
        ((t₁ + t₃ + t₁ * t₂ * t₃ - t₂) * (t₁ + t₂ + t₁ * t₂ * t₃ - t₃) *
          (ZT.natLit 1 - h))) := by
  have H := ZT.toZ_eq (half_angle_tan u₁ u₂ u₃ law hA)
  have e₁ := ZT.toZ_eq ht₁
  have e₂ := ZT.toZ_eq ht₂
  have e₃ := ZT.toZ_eq ht₃
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] at H e₁ e₂ e₃ ⊢
  push_cast at H ⊢
  rw [e₁, e₂, e₃] at H
  linear_combination H

/-- (6.17), cross-multiplied and times `(c₁ c₂ c₃)²`; here the unit pairs are the half angles
and `k = sin²(a/2)`. -/
theorem half_tangent_side {ca k : ZT n}
    (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1))
    (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1))
    (law : Γ ⊢[PRAAx] ZT.eq (cosD s₁ c₁)
      (-(cosD s₂ c₂ * cosD s₃ c₃) + sinD s₂ c₂ * sinD s₃ c₃ * ca))
    (ha : Γ ⊢[PRAAx] ZT.eq ca (ZT.natLit 1 - ZT.natLit 2 * k))
    (ht₁ : Γ ⊢[PRAAx] ZT.eq s₁ (t₁ * c₁)) (ht₂ : Γ ⊢[PRAAx] ZT.eq s₂ (t₂ * c₂))
    (ht₃ : Γ ⊢[PRAAx] ZT.eq s₃ (t₃ * c₃)) :
    Γ ⊢[PRAAx] ZT.eq
      (c₁ * c₂ * c₃ * (c₁ * c₂ * c₃) *
        (k * ((t₂ * t₃ + t₁ * t₂ + ZT.natLit 1 - t₃ * t₁) *
          (t₂ * t₃ + t₃ * t₁ + ZT.natLit 1 - t₁ * t₂))))
      (c₁ * c₂ * c₃ * (c₁ * c₂ * c₃) *
        ((t₂ * t₃ + t₃ * t₁ + t₁ * t₂ - ZT.natLit 1) *
          (t₃ * t₁ + t₁ * t₂ + ZT.natLit 1 - t₂ * t₃) * (ZT.natLit 1 - k))) := by
  have H := ZT.toZ_eq (half_side_tan u₁ u₂ u₃ law ha)
  have e₁ := ZT.toZ_eq ht₁
  have e₂ := ZT.toZ_eq ht₂
  have e₃ := ZT.toZ_eq ht₃
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] at H e₁ e₂ e₃ ⊢
  push_cast at H ⊢
  rw [e₁, e₂, e₃] at H
  linear_combination H

end LeanProofs.IPRA.Geometry.SphericalHalfTangent
