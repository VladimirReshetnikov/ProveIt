import IPRADerivations.Core.PolynomialImplications

/-!
# Exact algebra of the Platonic-solids packet (`platonic_solids_ipra`)

Packet: `geometry/platonic_solids_ipra`. `Geometry/PlatonicSolids` derives the numerical
classification of the pairs `{p, q}`. This module derives further exact statements of the
packet as implications between integer polynomial equations
(`Core/PolynomialImplications`):

* `stage_norm` (`lem:orderedstage`, the inverse and the sign rule `eq:towersign`): in a
  quadratic stage with `s² = r`, `(a + b s)(a − b s) = a² − b² r`;
* `stage_mul`: the product rule of the stage under `s² = r`,
  `(a + b s)(c + d s) = (a c + b d r) + (a d + b c) s`;
* `disk_edges`, `disk_count` (`lem:disk`): for a triangulated triangle with `k` interior
  vertices, `T` triangles and `E` edges, of which `e_II` join two interior vertices and `e_IB`
  join an interior to a boundary vertex: the Euler relation `(k + 3) + T = E + 1`, the incidence
  count `3 T + 3 = 2 E`, the edge split `E = e_II + e_IB + 3` and the degree-five count
  `2 e_II + e_IB = 5 k` give `E = 3 k + 3` and `e_II = 2 k`;
* `golden_inverse`, `golden_square` (`prop:five-examples`): for `φ² = φ + 1` and `ψ = φ − 1`,
  `φ ψ = 1` and `ψ² = 2 − φ`.

The order of a quadratic stage, the height lemma, the Euler relation itself, Cauchy's
rigidity theorem and the verification of the five models are not derived.
-/

namespace LeanProofs.IPRA.Geometry.PlatonicAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## A quadratic stage: `a, b, c, d, s, r` -/

section Stage

local notation "a" => (ZExp.var 0 : ZExp 6)
local notation "b" => (ZExp.var 1 : ZExp 6)
local notation "c" => (ZExp.var 2 : ZExp 6)
local notation "d" => (ZExp.var 3 : ZExp 6)
local notation "s" => (ZExp.var 4 : ZExp 6)
local notation "r" => (ZExp.var 5 : ZExp 6)

theorem stage_norm :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [(s ^ 2, r)] ((a + b * s) * (a - b * s), a ^ 2 - b ^ 2 * r)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (-(ρ 1 ^ 2)) * h)

/-- `(a + b s)(c + d s) = (a c + b d r) + (a d + b c) s` when `s² = r`. -/
theorem stage_mul :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [(s ^ 2, r)] ((a + b * s) * (c + d * s), (a * c + b * d * r) + (a * d + b * c) * s)) :=
  derive_imp _ _ (by ipra_poly R ρ h; linear_combination (ρ 1 * ρ 3) * h)

end Stage

/-! ## The triangular disk count: `k, T, E, e_II, e_IB` -/

section Disk

local notation "kk" => (ZExp.var 0 : ZExp 5)
local notation "T" => (ZExp.var 1 : ZExp 5)
local notation "E" => (ZExp.var 2 : ZExp 5)
local notation "eII" => (ZExp.var 3 : ZExp 5)
local notation "eIB" => (ZExp.var 4 : ZExp 5)

/-- The four counting relations of `lem:disk`. -/
abbrev diskHyps : List (ZExp 5 × ZExp 5) :=
  [((kk + 3) + T, E + 1), (3 * T + 3, 2 * E), (E, eII + eIB + 3), (2 * eII + eIB, 5 * kk)]

theorem disk_edges :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp diskHyps (E, 3 * kk + 3)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, _, _⟩ := h
    linear_combination (-3 : R) * h₁ + h₂)

theorem disk_count :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5) (imp diskHyps (eII, 2 * kk)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    linear_combination (3 : R) * h₁ - h₂ + h₃ + h₄)

end Disk

/-! ## The golden ratio: `φ, ψ` -/

section Golden

local notation "φ" => (ZExp.var 0 : ZExp 2)
local notation "ψ" => (ZExp.var 1 : ZExp 2)

theorem golden_inverse :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(φ ^ 2, φ + 1), (ψ, φ - 1)] (φ * ψ, 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ + ρ 0 * h₂)

theorem golden_square :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [(φ ^ 2, φ + 1), (ψ, φ - 1)] (ψ ^ 2, 2 - φ)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination h₁ + (ρ 1 + ρ 0 - 1) * h₂)

end Golden

end LeanProofs.IPRA.Geometry.PlatonicAlgebra
