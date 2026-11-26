import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerAlgebra

/-!
# The algebra of the interpolated Euler polygons on one coarse cell

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Theorem
`thm:ode-produced-refinement`, the last step of the proof of `eq:ode-produced-refine`: "Both polygons are affine on
each interval `[t_j, t_{j+1}]` of the fine mesh. Their difference at an intermediate point is a convex combination
of the differences at the two endpoints. The triangle inequality therefore extends the node estimate to every
rational point."

The setting is that of `EulerPolygons/EulerAlgebra`: a commutative ring with a cone, the coarse node value `x / D`
with matrix `M / β` and mesh `ν`, the fine values `w₀ / q₀`, `w₁ / q₁`, `w₂ / q₂` of mesh `κ = 2ν` with matrices
`M₀ / c₀`, `M₁ / c₁`, and the numerators `a₀ = x q₀ − w₀ D`, `a₁ = y q₁ − w₁ κ β D`, `a₂ = x' q₂ − w₂ D'` of the
differences at the three fine nodes of the cell. A rational point of the cell is `t = (i + ρ/q)/ν` with
`0 ≤ ρ ≤ q`. The coarse polygon has the value `pc / (ν q β D)` there, `pc = ν q β x + ρ M x`.

* `interp_first`: on the first half of the cell (`2ρ ≤ q`) the fine polygon has the value
  `pf / (κ q c₀ q₀)`, `pf = κ q c₀ w₀ + 2ρ M₀ w₀`, and

      pc (κ q c₀ q₀) − pf (ν q β D) = q ((q − 2ρ) κ ν β c₀ a₀ + ρ a₁),

  the convex combination of the differences at the fine nodes `2i` and `2i + 1` with the weights `(q − 2ρ)/q` and
  `2ρ/q` (the factors are the ratios of the denominators);
* `interp_second`: on the second half (`ρ' = 2ρ − q ≥ 0`, `ρ ≤ q`) the fine polygon has the value
  `pf / (κ q c₁ q₁)`, `pf = κ q c₁ w₁ + ρ' M₁ w₁`, and

      pc (κ q c₁ q₁) − pf (ν q β D) = q ((q − ρ) κ c₁ a₁ + ρ' a₂),

  the convex combination of the differences at the fine nodes `2i + 1` and `2i + 2` with the weights `2(q − ρ)/q`
  and `ρ'/q`.

Both are polynomial identities; no bound of a matrix is used.
-/

namespace LeanProofs.IPRA.Analysis.EulerInterpAlgebra

open LeanProofs.IPRA.Foundations.SignedCone

variable {R : Type*} [CommRing R] {P : R → Prop} {d : ℕ}

variable {ν β c₀ c₁ q ρ ρ' s E₀ E₁ E₂ D D' q₀ q₁ q₂ : R} {M M₀ M₁ : Fin d → Fin d → R}
  {x x' y w₀ w₁ w₂ pc pf : Fin d → R}

/-- The difference of the two polygons on the first half of a coarse cell. -/
theorem interp_first (hP : Cone P) (hν : P ν) (hβ : P β) (hc₀ : P c₀) (hq : P q) (hρ : P ρ)
    (hqρ : P (q - 2 * ρ))
    (hy : ∀ k, y k = 2 * ν * β * x k + ∑ l, M k l * x l)
    (hw₁ : ∀ k, w₁ k = 2 * ν * c₀ * w₀ k + ∑ l, M₀ k l * w₀ l)
    (hq₁ : q₁ = 2 * ν * c₀ * q₀)
    (hpc : ∀ k, pc k = ν * q * β * x k + ρ * ∑ l, M k l * x l)
    (hpf : ∀ k, pf k = 2 * ν * q * c₀ * w₀ k + 2 * ρ * ∑ l, M₀ k l * w₀ l)
    (h₀ : ∀ k, Bd P (s * (x k * q₀ - w₀ k * D)) E₀)
    (h₁ : ∀ k, Bd P (s * (y k * q₁ - w₁ k * (2 * ν * β * D))) E₁) (k : Fin d) :
    Bd P (s * (pc k * (2 * ν * q * c₀ * q₀) - pf k * (ν * q * β * D)))
      (q * ((q - 2 * ρ) * (2 * ν * ν * β * c₀) * E₀ + ρ * E₁)) := by
  have hc : P ((q - 2 * ρ) * (2 * ν * ν * β * c₀)) :=
    hP.mul hqρ (hP.mul (hP.mul (hP.mul (hP.mul hP.two hν) hν) hβ) hc₀)
  refine ((((h₀ k).smul hP hc).add hP ((h₁ k).smul hP hρ)).smul hP hq).congr ?_ rfl
  rw [hpc k, hpf k, hy k, hw₁ k, hq₁]
  ring

/-- The difference of the two polygons on the second half of a coarse cell. -/
theorem interp_second (hP : Cone P) (hν : P ν) (hc₁ : P c₁) (hq : P q) (hρ' : P ρ') (hqρ : P (q - ρ))
    (hρ : ρ' = 2 * ρ - q)
    (hy : ∀ k, y k = 2 * ν * β * x k + ∑ l, M k l * x l)
    (hx' : ∀ k, x' k = ν * β * x k + ∑ l, M k l * x l)
    (hw₂ : ∀ k, w₂ k = 2 * ν * c₁ * w₁ k + ∑ l, M₁ k l * w₁ l)
    (hq₂ : q₂ = 2 * ν * c₁ * q₁) (hD' : D' = ν * β * D)
    (hpc : ∀ k, pc k = ν * q * β * x k + ρ * ∑ l, M k l * x l)
    (hpf : ∀ k, pf k = 2 * ν * q * c₁ * w₁ k + ρ' * ∑ l, M₁ k l * w₁ l)
    (h₁ : ∀ k, Bd P (s * (y k * q₁ - w₁ k * (2 * ν * β * D))) E₁)
    (h₂ : ∀ k, Bd P (s * (x' k * q₂ - w₂ k * D')) E₂) (k : Fin d) :
    Bd P (s * (pc k * (2 * ν * q * c₁ * q₁) - pf k * (ν * q * β * D)))
      (q * ((q - ρ) * (2 * ν * c₁) * E₁ + ρ' * E₂)) := by
  have hc : P ((q - ρ) * (2 * ν * c₁)) := hP.mul hqρ (hP.mul (hP.mul hP.two hν) hc₁)
  refine ((((h₁ k).smul hP hc).add hP ((h₂ k).smul hP hρ')).smul hP hq).congr ?_ rfl
  rw [hpc k, hpf k, hy k, hx' k, hw₂ k, hq₂, hD', hρ]
  ring

end LeanProofs.IPRA.Analysis.EulerInterpAlgebra
