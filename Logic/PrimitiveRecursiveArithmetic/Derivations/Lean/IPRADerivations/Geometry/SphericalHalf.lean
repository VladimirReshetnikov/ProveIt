import IPRADerivations.Geometry.CevaMenelaus

/-!
# The spherical half-angle formulas

Packet: `spherical_trigonometry_ipra_2026-11-15`, `sections/06_half_formulas.tex`, Theorem
`thm:half-angle`, as ring certificates. The half sides `a/2, b/2, c/2` are unit pairs
`(s₁, c₁), (s₂, c₂), (s₃, c₃)` (`sᵢ² + cᵢ² = 1`), so `sin a = 2 s₁ c₁`, `cos a = c₁² − s₁²`, …, and
with `p = (a + b + c)/2`

  `sin p = sin(α + β + γ)`, `sin(p − a) = sin(−α + β + γ)`, …

are the finite addition-formula polynomials. With `h = sin²(A/2)` and the side cosine law
`cos a = cos b cos c + sin b sin c cos A`, `cos A = 1 − 2h`:

* `product_to_sum_diff`, `product_to_sum_sum`: `cos(b − c) − cos a = 2 sin(p − b) sin(p − c)` and
  `cos a − cos(b + c) = 2 sin p sin(p − a)`, modulo the unit relations (certificates computed by
  polynomial reduction);
* `half_angle_sin` (6.1): `sin b sin c · h = sin(p − b) sin(p − c)`;
* `half_angle_cos` (6.2): `sin b sin c · (1 − h) = sin p sin(p − a)`;
* `half_angle_tan` (6.3), cross-multiplied: `sin p sin(p − a) · h = sin(p − b) sin(p − c) · (1 − h)`.

The positive square roots (6.4)–(6.6) are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.SphericalHalf

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.CevaMenelaus (nz zt_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The ring identities -/

section Ring

variable {R : Type*} [CommRing R]

/-- `sin(x + y + z)` from unit pairs. -/
def sin3R (sx cx sy cy sz cz : R) : R := sx * cy * cz + cx * sy * cz + cx * cy * sz - sx * sy * sz

theorem diffR (s₁ c₁ s₂ c₂ s₃ c₃ : R) (u₁ : s₁ * s₁ + c₁ * c₁ = 1) (u₂ : s₂ * s₂ + c₂ * c₂ = 1)
    (u₃ : s₃ * s₃ + c₃ * c₃ = 1) :
    (c₂ * c₂ - s₂ * s₂) * (c₃ * c₃ - s₃ * s₃) + 2 * s₂ * c₂ * (2 * s₃ * c₃) - (c₁ * c₁ - s₁ * s₁) =
      2 * sin3R s₁ c₁ (-s₂) c₂ s₃ c₃ * sin3R s₁ c₁ s₂ c₂ (-s₃) c₃ := by
  simp only [sin3R]
  linear_combination (2 * c₂ ^ 2 * s₃ ^ 2 - 4 * c₂ * c₃ * s₂ * s₃ + 2 * c₃ ^ 2 * s₂ ^ 2 - 1) * u₁ +
    (-2 * c₃ ^ 2 * s₁ ^ 2 + c₃ ^ 2 - 2 * s₁ ^ 2 * s₃ ^ 2 + s₃ ^ 2) * u₂ + (1 - 2 * s₁ ^ 2) * u₃

theorem sumR (s₁ c₁ s₂ c₂ s₃ c₃ : R) (u₁ : s₁ * s₁ + c₁ * c₁ = 1) (u₂ : s₂ * s₂ + c₂ * c₂ = 1)
    (u₃ : s₃ * s₃ + c₃ * c₃ = 1) :
    (c₁ * c₁ - s₁ * s₁) - ((c₂ * c₂ - s₂ * s₂) * (c₃ * c₃ - s₃ * s₃) - 2 * s₂ * c₂ * (2 * s₃ * c₃)) =
      2 * sin3R s₁ c₁ s₂ c₂ s₃ c₃ * sin3R (-s₁) c₁ s₂ c₂ s₃ c₃ := by
  simp only [sin3R]
  linear_combination (-2 * c₂ ^ 2 * s₃ ^ 2 - 4 * c₂ * c₃ * s₂ * s₃ - 2 * c₃ ^ 2 * s₂ ^ 2 + 1) * u₁ +
    (2 * c₃ ^ 2 * s₁ ^ 2 - c₃ ^ 2 + 2 * s₁ ^ 2 * s₃ ^ 2 - s₃ ^ 2) * u₂ + (2 * s₁ ^ 2 - 1) * u₃

end Ring

/-! ## Integer terms -/

section Terms

variable (s₁ c₁ s₂ c₂ s₃ c₃ : ZT n)

/-- `sin(x + y + z)`. -/
abbrev sin3 (sx cx sy cy sz cz : ZT n) : ZT n := sx * cy * cz + cx * sy * cz + cx * cy * sz - sx * sy * sz

/-- `cos a = c₁² − s₁²` and `sin a = 2 s₁ c₁`, and so on. -/
abbrev cosD (s c : ZT n) : ZT n := c * c - s * s
abbrev sinD (s c : ZT n) : ZT n := ZT.natLit 2 * s * c

/-- `sin p`, `sin(p − a)`, `sin(p − b)`, `sin(p − c)`. -/
abbrev sP : ZT n := sin3 s₁ c₁ s₂ c₂ s₃ c₃
abbrev sPa : ZT n := sin3 (-s₁) c₁ s₂ c₂ s₃ c₃
abbrev sPb : ZT n := sin3 s₁ c₁ (-s₂) c₂ s₃ c₃
abbrev sPc : ZT n := sin3 s₁ c₁ s₂ c₂ (-s₃) c₃

end Terms

theorem toZ_sin3 (sx cx sy cy sz cz : ZT n) :
    ZT.toZ Γ (sin3 sx cx sy cy sz cz) =
      sin3R (ZT.toZ Γ sx) (ZT.toZ Γ cx) (ZT.toZ Γ sy) (ZT.toZ Γ cy) (ZT.toZ Γ sz) (ZT.toZ Γ cz) := by
  simp only [sin3R, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]

theorem nz_two : Γ ⊢[PRAAx] nz (ZT.natLit 2 : ZT n) := by
  have e : Γ ⊢[PRAAx] (monus (PTm.num 2) zero + monus zero (PTm.num 2) : PTm n) ≐ PTm.num 2 + zero :=
    congrAdd (monus_zero _) (zero_monus _)
  exact le_congr (.eqRefl _) e.eqSymm (le_of_eq_add (d := one) (by apply deriveNat; ipra_simps; norm_num))

section Half

variable {s₁ c₁ s₂ c₂ s₃ c₃ cA h : ZT n}

/-- `cos(b − c) − cos a = 2 sin(p − b) sin(p − c)`. -/
theorem product_to_sum_diff (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1)) (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (cosD s₂ c₂ * cosD s₃ c₃ + sinD s₂ c₂ * sinD s₃ c₃ - cosD s₁ c₁)
      (ZT.natLit 2 * sPb s₁ c₁ s₂ c₂ s₃ c₃ * sPc s₁ c₁ s₂ c₂ s₃ c₃) := by
  have e₁ := ZT.toZ_eq u₁; have e₂ := ZT.toZ_eq u₂; have e₃ := ZT.toZ_eq u₃
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one] at e₁ e₂ e₃
  refine ZT.derive ?_
  simp only [sPb, sPc, toZ_sin3, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]
  have k := diffR _ _ _ _ _ _ e₁ e₂ e₃
  simp only [sin3R] at k ⊢
  push_cast
  linear_combination k

/-- `cos a − cos(b + c) = 2 sin p sin(p − a)`. -/
theorem product_to_sum_sum (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1)) (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (cosD s₁ c₁ - (cosD s₂ c₂ * cosD s₃ c₃ - sinD s₂ c₂ * sinD s₃ c₃))
      (ZT.natLit 2 * sP s₁ c₁ s₂ c₂ s₃ c₃ * sPa s₁ c₁ s₂ c₂ s₃ c₃) := by
  have e₁ := ZT.toZ_eq u₁; have e₂ := ZT.toZ_eq u₂; have e₃ := ZT.toZ_eq u₃
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one] at e₁ e₂ e₃
  refine ZT.derive ?_
  simp only [sP, sPa, toZ_sin3, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit]
  have k := sumR _ _ _ _ _ _ e₁ e₂ e₃
  simp only [sin3R] at k ⊢
  push_cast
  linear_combination k

/-- (6.1): `sin b sin c · sin²(A/2) = sin(p − b) sin(p − c)`, given the side cosine law and
`cos A = 1 − 2h`. -/
theorem half_angle_sin (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1)) (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1))
    (law : Γ ⊢[PRAAx] ZT.eq (cosD s₁ c₁) (cosD s₂ c₂ * cosD s₃ c₃ + sinD s₂ c₂ * sinD s₃ c₃ * cA))
    (hA : Γ ⊢[PRAAx] ZT.eq cA (ZT.natLit 1 - ZT.natLit 2 * h)) :
    Γ ⊢[PRAAx] ZT.eq (sinD s₂ c₂ * sinD s₃ c₃ * h) (sPb s₁ c₁ s₂ c₂ s₃ c₃ * sPc s₁ c₁ s₂ c₂ s₃ c₃) := by
  have d := ZT.toZ_eq (product_to_sum_diff u₁ u₂ u₃)
  have l := ZT.toZ_eq law; have a := ZT.toZ_eq hA
  refine zt_cancel nz_two (ZT.derive ?_)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] at d l a ⊢
  push_cast at d l a ⊢
  linear_combination d + l + (2 * ZT.toZ Γ s₂ * ZT.toZ Γ c₂ * (2 * ZT.toZ Γ s₃ * ZT.toZ Γ c₃)) * a

/-- (6.2): `sin b sin c · cos²(A/2) = sin p sin(p − a)`, with `cos²(A/2) = 1 − h`. -/
theorem half_angle_cos (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1)) (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1))
    (law : Γ ⊢[PRAAx] ZT.eq (cosD s₁ c₁) (cosD s₂ c₂ * cosD s₃ c₃ + sinD s₂ c₂ * sinD s₃ c₃ * cA))
    (hA : Γ ⊢[PRAAx] ZT.eq cA (ZT.natLit 1 - ZT.natLit 2 * h)) :
    Γ ⊢[PRAAx] ZT.eq (sinD s₂ c₂ * sinD s₃ c₃ * (ZT.natLit 1 - h)) (sP s₁ c₁ s₂ c₂ s₃ c₃ * sPa s₁ c₁ s₂ c₂ s₃ c₃) := by
  have d := ZT.toZ_eq (product_to_sum_sum u₁ u₂ u₃)
  have l := ZT.toZ_eq law; have a := ZT.toZ_eq hA
  refine zt_cancel nz_two (ZT.derive ?_)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit] at d l a ⊢
  push_cast at d l a ⊢
  linear_combination d - l - (2 * ZT.toZ Γ s₂ * ZT.toZ Γ c₂ * (2 * ZT.toZ Γ s₃ * ZT.toZ Γ c₃)) * a

/-- (6.3), cross-multiplied: `sin p sin(p − a) · h = sin(p − b) sin(p − c) · (1 − h)`. -/
theorem half_angle_tan (u₁ : Γ ⊢[PRAAx] ZT.eq (s₁ * s₁ + c₁ * c₁) (ZT.natLit 1))
    (u₂ : Γ ⊢[PRAAx] ZT.eq (s₂ * s₂ + c₂ * c₂) (ZT.natLit 1)) (u₃ : Γ ⊢[PRAAx] ZT.eq (s₃ * s₃ + c₃ * c₃) (ZT.natLit 1))
    (law : Γ ⊢[PRAAx] ZT.eq (cosD s₁ c₁) (cosD s₂ c₂ * cosD s₃ c₃ + sinD s₂ c₂ * sinD s₃ c₃ * cA))
    (hA : Γ ⊢[PRAAx] ZT.eq cA (ZT.natLit 1 - ZT.natLit 2 * h)) :
    Γ ⊢[PRAAx] ZT.eq (sP s₁ c₁ s₂ c₂ s₃ c₃ * sPa s₁ c₁ s₂ c₂ s₃ c₃ * h)
      (sPb s₁ c₁ s₂ c₂ s₃ c₃ * sPc s₁ c₁ s₂ c₂ s₃ c₃ * (ZT.natLit 1 - h)) := by
  have hs := ZT.toZ_eq (half_angle_sin u₁ u₂ u₃ law hA)
  have hc := ZT.toZ_eq (half_angle_cos u₁ u₂ u₃ law hA)
  refine ZT.derive ?_
  simp only [ZT.toZ_mul] at hs hc ⊢
  linear_combination ZT.toZ Γ (ZT.natLit 1 - h) * hs - ZT.toZ Γ h * hc

end Half

end LeanProofs.IPRA.Geometry.SphericalHalf
