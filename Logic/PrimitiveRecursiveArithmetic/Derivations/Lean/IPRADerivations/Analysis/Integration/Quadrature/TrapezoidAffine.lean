import IPRADerivations.Core.Telescoping

/-!
# Exact facts about trapezoidal sums

Packet: `analysis/cauchy_residue_ipra` (`lem:algebra`, "Exact algebraic facts"). Complex numbers
are pairs of integers (the packet's Gaussian rationals, cleared of denominators), and
`T(u, v; f, g) = (v − u)(f + g)` is twice the trapezoid of the values `f`, `g` on the edge
`u → v`. For a complex-affine `A(z) = α + β z` put `P(z) = 2 α z + β z²`.

* `edge_reverse_re`, `edge_reverse_im`: reversing an edge negates the trapezoid;
* `edge_affine_re`, `edge_affine_im`: `T(u, v; A(u), A(v)) = P(v) − P(u)`, i.e. the trapezoid is
  `α (v − u) + (β/2)(v² − u²)`;
* `edge_additive_re`, `edge_additive_im`: for an affine `A` and any intermediate point `w`,
  `T(u, w) + T(w, v) = T(u, v)`; so every subdivision of an edge gives the same trapezoidal sum;
* `closed_polygon_zero`: for a sequence of vertices with potentials `P(v_i)` whose real (or
  imaginary) part has positive and negative parts `p(i)`, `q(i)`, if `P(v_N) = P(v_0)` then the
  sum of the edge contributions `P(v_{i+1}) − P(v_i)` is zero.

The uniform-continuity estimate `lem:quadrature`, the regular names of contour integrals and the
Cauchy and residue theorems are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.TrapezoidAffine

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Complex arithmetic on pairs of integers -/

/-- The real part of `(x₁ + i x₂)(y₁ + i y₂)`. -/
abbrev mre {k : ℕ} (x₁ x₂ y₁ y₂ : ZT k) : ZT k := x₁ * y₁ - x₂ * y₂
/-- The imaginary part of `(x₁ + i x₂)(y₁ + i y₂)`. -/
abbrev mim {k : ℕ} (x₁ x₂ y₁ y₂ : ZT k) : ZT k := x₁ * y₂ + x₂ * y₁

/-- `A(z) = α + β z`, real part. -/
abbrev Are {k : ℕ} (a₁ b₁ b₂ z₁ z₂ : ZT k) : ZT k := a₁ + mre b₁ b₂ z₁ z₂
/-- `A(z) = α + β z`, imaginary part. -/
abbrev Aim {k : ℕ} (a₂ b₁ b₂ z₁ z₂ : ZT k) : ZT k := a₂ + mim b₁ b₂ z₁ z₂

/-- `P(z) = 2 α z + β z²`, real part. -/
abbrev Pre {k : ℕ} (a₁ a₂ b₁ b₂ z₁ z₂ : ZT k) : ZT k :=
  ZT.natLit 2 * mre a₁ a₂ z₁ z₂ + mre b₁ b₂ (mre z₁ z₂ z₁ z₂) (mim z₁ z₂ z₁ z₂)
/-- `P(z) = 2 α z + β z²`, imaginary part. -/
abbrev Pim {k : ℕ} (a₁ a₂ b₁ b₂ z₁ z₂ : ZT k) : ZT k :=
  ZT.natLit 2 * mim a₁ a₂ z₁ z₂ + mim b₁ b₂ (mre z₁ z₂ z₁ z₂) (mim z₁ z₂ z₁ z₂)

/-- `T(u, v; f, g) = (v − u)(f + g)`, real part. -/
abbrev Tre {k : ℕ} (u₁ u₂ v₁ v₂ f₁ f₂ g₁ g₂ : ZT k) : ZT k := mre (v₁ - u₁) (v₂ - u₂) (f₁ + g₁) (f₂ + g₂)
/-- `T(u, v; f, g) = (v − u)(f + g)`, imaginary part. -/
abbrev Tim {k : ℕ} (u₁ u₂ v₁ v₂ f₁ f₂ g₁ g₂ : ZT k) : ZT k := mim (v₁ - u₁) (v₂ - u₂) (f₁ + g₁) (f₂ + g₂)

/-! ## One edge -/

section Edge

variable (a₁ a₂ b₁ b₂ u₁ u₂ v₁ v₂ w₁ w₂ f₁ f₂ g₁ g₂ : ZT n)

theorem edge_reverse_re :
    Γ ⊢[PRAAx] ZT.eq (Tre v₁ v₂ u₁ u₂ g₁ g₂ f₁ f₂) (-(Tre u₁ u₂ v₁ v₂ f₁ f₂ g₁ g₂)) := by
  ipra_ring

theorem edge_reverse_im :
    Γ ⊢[PRAAx] ZT.eq (Tim v₁ v₂ u₁ u₂ g₁ g₂ f₁ f₂) (-(Tim u₁ u₂ v₁ v₂ f₁ f₂ g₁ g₂)) := by
  ipra_ring

/-- The trapezoid of an affine function is a potential difference (real part). -/
theorem edge_affine_re :
    Γ ⊢[PRAAx] ZT.eq
      (Tre u₁ u₂ v₁ v₂ (Are a₁ b₁ b₂ u₁ u₂) (Aim a₂ b₁ b₂ u₁ u₂) (Are a₁ b₁ b₂ v₁ v₂) (Aim a₂ b₁ b₂ v₁ v₂))
      (Pre a₁ a₂ b₁ b₂ v₁ v₂ - Pre a₁ a₂ b₁ b₂ u₁ u₂) := by
  ipra_ring

/-- The trapezoid of an affine function is a potential difference (imaginary part). -/
theorem edge_affine_im :
    Γ ⊢[PRAAx] ZT.eq
      (Tim u₁ u₂ v₁ v₂ (Are a₁ b₁ b₂ u₁ u₂) (Aim a₂ b₁ b₂ u₁ u₂) (Are a₁ b₁ b₂ v₁ v₂) (Aim a₂ b₁ b₂ v₁ v₂))
      (Pim a₁ a₂ b₁ b₂ v₁ v₂ - Pim a₁ a₂ b₁ b₂ u₁ u₂) := by
  ipra_ring

/-- Subdividing an edge at any point `w` does not change the trapezoidal sum of an affine
function (real part). -/
theorem edge_additive_re :
    Γ ⊢[PRAAx] ZT.eq
      (Tre u₁ u₂ w₁ w₂ (Are a₁ b₁ b₂ u₁ u₂) (Aim a₂ b₁ b₂ u₁ u₂) (Are a₁ b₁ b₂ w₁ w₂) (Aim a₂ b₁ b₂ w₁ w₂) +
        Tre w₁ w₂ v₁ v₂ (Are a₁ b₁ b₂ w₁ w₂) (Aim a₂ b₁ b₂ w₁ w₂) (Are a₁ b₁ b₂ v₁ v₂) (Aim a₂ b₁ b₂ v₁ v₂))
      (Tre u₁ u₂ v₁ v₂ (Are a₁ b₁ b₂ u₁ u₂) (Aim a₂ b₁ b₂ u₁ u₂) (Are a₁ b₁ b₂ v₁ v₂) (Aim a₂ b₁ b₂ v₁ v₂)) := by
  ipra_ring

/-- Subdividing an edge at any point `w` does not change the trapezoidal sum of an affine
function (imaginary part). -/
theorem edge_additive_im :
    Γ ⊢[PRAAx] ZT.eq
      (Tim u₁ u₂ w₁ w₂ (Are a₁ b₁ b₂ u₁ u₂) (Aim a₂ b₁ b₂ u₁ u₂) (Are a₁ b₁ b₂ w₁ w₂) (Aim a₂ b₁ b₂ w₁ w₂) +
        Tim w₁ w₂ v₁ v₂ (Are a₁ b₁ b₂ w₁ w₂) (Aim a₂ b₁ b₂ w₁ w₂) (Are a₁ b₁ b₂ v₁ v₂) (Aim a₂ b₁ b₂ v₁ v₂))
      (Tim u₁ u₂ v₁ v₂ (Are a₁ b₁ b₂ u₁ u₂) (Aim a₂ b₁ b₂ u₁ u₂) (Are a₁ b₁ b₂ v₁ v₂) (Aim a₂ b₁ b₂ v₁ v₂)) := by
  ipra_ring

end Edge

/-! ## Closed forms -/

section Closed

abbrev A₁ : ZT 16 := .var2 0 1
abbrev A₂ : ZT 16 := .var2 2 3
abbrev B₁ : ZT 16 := .var2 4 5
abbrev B₂ : ZT 16 := .var2 6 7
abbrev U₁ : ZT 16 := .var2 8 9
abbrev U₂ : ZT 16 := .var2 10 11
abbrev V₁ : ZT 16 := .var2 12 13
abbrev V₂ : ZT 16 := .var2 14 15

def edgeAffineFormula : Fm PTm 16 :=
  (ZT.eq
    (Tre U₁ U₂ V₁ V₂ (Are A₁ B₁ B₂ U₁ U₂) (Aim A₂ B₁ B₂ U₁ U₂) (Are A₁ B₁ B₂ V₁ V₂) (Aim A₂ B₁ B₂ V₁ V₂))
    (Pre A₁ A₂ B₁ B₂ V₁ V₂ - Pre A₁ A₂ B₁ B₂ U₁ U₂)) ⋏
  (ZT.eq
    (Tim U₁ U₂ V₁ V₂ (Are A₁ B₁ B₂ U₁ U₂) (Aim A₂ B₁ B₂ U₁ U₂) (Are A₁ B₁ B₂ V₁ V₂) (Aim A₂ B₁ B₂ V₁ V₂))
    (Pim A₁ A₂ B₁ B₂ V₁ V₂ - Pim A₁ A₂ B₁ B₂ U₁ U₂))

/-- `lem:algebra`, the affine assertion, for all complex integers `α, β, u, v`. -/
theorem edge_affine : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 16 edgeAffineFormula :=
  closeAll 16 (.andI (edge_affine_re _ _ _ _ _ _ _ _) (edge_affine_im _ _ _ _ _ _ _ _))

end Closed

/-! ## Closed polygons -/

/-- For a signed sequence `p − q` with `(p − q)(N) = (p − q)(0)`, the sum of the differences
`(p − q)(i+1) − (p − q)(i)` is the integer zero. With `p − q` a coordinate of the potential
`P(v_i)`, this is: the trapezoidal sum of an affine function around a closed polygon is zero. -/
theorem closed_polygon_zero (p q : PTm 2) {N x : PTm n}
    (hc : Γ ⊢[PRAAx] inst2 p N x + inst2 q zero x ≐ inst2 p zero x + inst2 q N x) :
    Γ ⊢[PRAAx] ZT.eq ⟨ap2 (sumF (upB p q)) N x, ap2 (sumF (dnB p q)) N x⟩ (ZT.natLit 0) := by
  show Γ ⊢[PRAAx] ap2 (sumF (upB p q)) N x + zero ≐ PTm.num 0 + ap2 (sumF (dnB p q)) N x
  ipra_lc natEq (closed_signed p q hc)

end LeanProofs.IPRA.Analysis.TrapezoidAffine
