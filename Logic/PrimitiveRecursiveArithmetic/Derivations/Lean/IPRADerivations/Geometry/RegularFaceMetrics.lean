import IPRADerivations.Core.PolynomialImplications
import IPRADerivations.Core.IntCancel
import IPRADerivations.Core.Order

/-!
# The regular face metrics and the spherical hinge (`platonic_solids_ipra`)

Packet: `geometry/platonic_solids_ipra`, Section "Finite geometric rigidity".

**Uniqueness of the small regular face metrics.** "Center a regular face and let `R` be its
cyclic rotation. In oriented orthonormal coordinates, `R = [[c, −s], [s, c]]`, `c² + s² = 1`,
`s > 0`, and its order is exactly `p`. Put `t = 2c`; then `R² − tR + I = 0`. For `p = 3`, the
identity `I + R + R² = 0` gives `t = −1`. For `p = 4`, exact order four gives `R² = −I`, hence
`t = 0`. ... For `p = 5`, ... the result is `t² + t − 1 = 0`. The negative root is less than `−1`
and violates convex order: `det(u_1 − u_0, u_3 − u_0) = 2s(1 − c)(t + 1) > 0` ... the edge
square `L` fixes the circumradius square `L/(2 − t)` ... for a pentagon the diagonal-square to
side-square ratio is `2 + t`."

The rotation is the complex number `c + i s`; its powers are written out in coordinates. Each
statement is an implication between integer polynomial equations whose certificate holds in
every commutative ring (`Core/PolynomialImplications.derive_imp`), so it applies in the
quadratic stages where `c` and `s` live:

* `trace_relation`: `c² + s² = 1` gives the real part of `R² − tR + I = 0`;
* `triangle_trace`: with `I + R + R² = 0`, `2c + 1 = 0` (`t = −1`);
* `square_trace`: with `R² = −I`, `(2c)² = 0`;
* `pentagon_trace`: with `Re R⁵ = 1`, `(c − 1)(4c² + 2c − 1)² = 0`, where
  `4c² + 2c − 1 = t² + t − 1`;
* `pentagon_imag`: `Im R⁵ = s (4c² + 2c − 1)(4c² − 2c − 1)`;
* `convex_det`: `det(u_1 − u_0, u_3 − u_0) = 2s(1 − c)(2c + 1)` for `u_i = R^i u_0`, `u_0 = (1, 0)`;
* `side_square`, `diagonal_square`: `|u_1 − u_0|² = 2 − 2c` and
  `|u_2 − u_0|² = (2 − 2c)(2 + 2c)`.

The steps that need an integral domain are rules for integer terms:

* `zt_sq_zero`: `K² = 0 → K = 0`; `zt_cancel_sq`: `X ≠ Y`, `(X − Y) K² = 0 → K = 0`
  (for `p = 5`: `c ≠ 1` and `pentagon_trace` give `t² + t − 1 = 0`; for `p = 4`: `t = 0`).

**The spherical hinge** (`eq:hinge`): "Resolving two unit vectors into their components
parallel and perpendicular to a third gives the spherical hinge identity
`cos c = cos a cos b + sin a sin b cos γ`." For vectors `u, v, w` with `v · v = 1`:

* `hinge_split`: `u · w = (u · v)(w · v) + u⊥ · w⊥` with `u⊥ = u − (u · v) v`;
* `hinge_perp`: `u⊥ · v = 0`; `hinge_norm`: `u⊥ · u⊥ = u · u − (u · v)²` (`sin² a = 1 − cos² a`
  for a unit `u`).

Not derived: the order statements (`s > 0`, the choice of the root `t = (√5 − 1)/2`), the
monotonicity of the hinge in `γ`, and the arm lemma.
-/

namespace LeanProofs.IPRA.Geometry.RegularFaceMetrics

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## The rotation `c + i s` -/

section Rotation

local notation "c" => (ZExp.var 0 : ZExp 2)
local notation "s" => (ZExp.var 1 : ZExp 2)

/-- The real part of `R² − tR + I = 0` with `t = 2c`. -/
theorem trace_relation :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1)] (c ^ 2 - s ^ 2 - 2 * c * c + 1, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-1 : R) * h)

/-- `p = 3`: `I + R + R² = 0` gives `t = −1`. -/
theorem triangle_trace :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1), (1 + c + (c ^ 2 - s ^ 2), 0), (s + 2 * c * s, 0)]
        (2 * c + 1, 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination (-(ρ 0) - 1) * h₁ + ρ 0 * h₂ + ρ 1 * h₃)

/-- `p = 4`: `R² = −I` gives `t² = 0`. -/
theorem square_trace :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1), (c ^ 2 - s ^ 2 + 1, 0)] ((2 * c) ^ 2, 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (2 : R) * h₁ + (2 : R) * h₂)

/-- `p = 5`: `Re R⁵ = 1` gives `(c − 1)(t² + t − 1)² = 0` with `t = 2c`. -/
theorem pentagon_trace :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1), (c ^ 5 - 10 * c ^ 3 * s ^ 2 + 5 * c * s ^ 4, 1)]
        ((c - 1) * (4 * c ^ 2 + 2 * c - 1) ^ 2, 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (-5 * ρ 0 * ρ 1 ^ 2 + 15 * ρ 0 ^ 3 - 5 * ρ 0) * h₁ + h₂)

/-- `Im R⁵ = s (t² + t − 1)(t² − t − 1)` with `t = 2c`. -/
theorem pentagon_imag :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1)]
        (5 * c ^ 4 * s - 10 * c ^ 2 * s ^ 3 + s ^ 5,
          s * (4 * c ^ 2 + 2 * c - 1) * (4 * c ^ 2 - 2 * c - 1))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination (ρ 1 * (ρ 1 ^ 2 - 11 * ρ 0 ^ 2 + 1)) * h)

/-- The supporting-side determinant: `det(u_1 − u_0, u_3 − u_0) = 2s(1 − c)(t + 1)`. -/
theorem convex_det :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1)]
        ((c - 1) * (3 * c ^ 2 * s - s ^ 3) - s * (c ^ 3 - 3 * c * s ^ 2 - 1),
          2 * s * (1 - c) * (2 * c + 1))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination (ρ 1 * (2 * ρ 0 + 1)) * h)

/-- The edge square of the unit regular face: `|u_1 − u_0|² = 2 − t`. -/
theorem side_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1)] ((c - 1) ^ 2 + s ^ 2, 2 - 2 * c)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination h)

/-- The diagonal square: `|u_2 − u_0|² = (2 − t)(2 + t)`. -/
theorem diagonal_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(c ^ 2 + s ^ 2, 1)]
        ((c ^ 2 - s ^ 2 - 1) ^ 2 + (2 * c * s) ^ 2, (2 - 2 * c) * (2 + 2 * c))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination (ρ 0 ^ 2 + ρ 1 ^ 2 + 3) * h)

end Rotation

/-! ## The spherical hinge -/

section Hinge

local notation "u₁" => (ZExp.var 0 : ZExp 9)
local notation "u₂" => (ZExp.var 1 : ZExp 9)
local notation "u₃" => (ZExp.var 2 : ZExp 9)
local notation "v₁" => (ZExp.var 3 : ZExp 9)
local notation "v₂" => (ZExp.var 4 : ZExp 9)
local notation "v₃" => (ZExp.var 5 : ZExp 9)
local notation "w₁" => (ZExp.var 6 : ZExp 9)
local notation "w₂" => (ZExp.var 7 : ZExp 9)
local notation "w₃" => (ZExp.var 8 : ZExp 9)

/-- `u · v`. -/
abbrev uv : ZExp 9 := u₁ * v₁ + u₂ * v₂ + u₃ * v₃
/-- `w · v`. -/
abbrev wv : ZExp 9 := w₁ * v₁ + w₂ * v₂ + w₃ * v₃

/-- `eq:hinge`: `u · w = (u · v)(w · v) + u⊥ · w⊥` for a unit vector `v`. -/
theorem hinge_split :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [(v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2, 1)]
        (u₁ * w₁ + u₂ * w₂ + u₃ * w₃,
          uv * wv + ((u₁ - uv * v₁) * (w₁ - wv * v₁) + (u₂ - uv * v₂) * (w₂ - wv * v₂) +
            (u₃ - uv * v₃) * (w₃ - wv * v₃)))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination
      (-((ρ 0 * ρ 3 + ρ 1 * ρ 4 + ρ 2 * ρ 5) * (ρ 6 * ρ 3 + ρ 7 * ρ 4 + ρ 8 * ρ 5))) * h)

/-- The perpendicular part is perpendicular: `u⊥ · v = 0`. -/
theorem hinge_perp :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [(v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2, 1)]
        ((u₁ - uv * v₁) * v₁ + (u₂ - uv * v₂) * v₂ + (u₃ - uv * v₃) * v₃, 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination (-(ρ 0 * ρ 3 + ρ 1 * ρ 4 + ρ 2 * ρ 5)) * h)

/-- `u⊥ · u⊥ = u · u − (u · v)²`. -/
theorem hinge_norm :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [(v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2, 1)]
        ((u₁ - uv * v₁) ^ 2 + (u₂ - uv * v₂) ^ 2 + (u₃ - uv * v₃) ^ 2,
          u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 - uv ^ 2)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    linear_combination ((ρ 0 * ρ 3 + ρ 1 * ρ 4 + ρ 2 * ρ 5) ^ 2) * h)

end Hinge

/-! ## The integral-domain steps -/

section Domain

open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `K² = 0 → K = 0` for integer terms. -/
theorem zt_sq_zero {K : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (K * K) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq K (ZT.natLit 0) := by
  refine .orE (eq_or_ne (K.pos + (ZT.natLit 0 : ZT n).neg) ((ZT.natLit 0 : ZT n).pos + K.neg))
    Prf.hyp0 ?_
  exact zt_mul_cancel_left Prf.hyp0 h.wk

/-- `X ≠ Y` and `(X − Y) K² = 0` give `K = 0`. -/
theorem zt_cancel_sq {X Y K : ZT n} (hXY : Γ ⊢[PRAAx] neg (ZT.eq X Y))
    (h : Γ ⊢[PRAAx] ZT.eq ((X - Y) * (K * K)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq K (ZT.natLit 0) :=
  zt_sq_zero (zt_mul_cancel_sub hXY h)

end Domain

end LeanProofs.IPRA.Geometry.RegularFaceMetrics
