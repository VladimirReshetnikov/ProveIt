import IPRADerivations.Foundations.SignedCone

/-!
# The algebra of one Euler step and of one refinement cell

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Lemma `lem:ode-polybound`
and Theorem `thm:ode-produced-refinement`. This module contains the estimates of the paper for one step of the
exact Euler array, cleared of denominators, in a commutative ring `R` with a cone `P`
(`Foundations/SignedCone`: `Bd P y T` is `|y| ≤ T`, `RowBd P M A` is `‖M‖ ≤ A` for the row-sum norm). The iPRA
derivations of `EulerPolygons/EulerNodeBound`, `EulerPolygons/EulerRefinement` and `EulerPolygons/EulerCauchy`
instantiate `R` with the ring of differences and `P` with the values of terms, and supply the inductions.

A rational vector is a numerator vector `x : Fin d → R` over a positive denominator `D`. The coefficient matrix
at a node is `M / β`. With mesh `ν` the Euler step `X' = X + (1/ν) (M/β) X` is `x' = ν β x + M x` over
`D' = ν β D`.

* `node_step` (`lem:ode-polybound`): `‖M‖ ≤ K β` and `s |x_k| ≤ T` for all `k` give `s |x'_i| ≤ (ν + K) β T`, that
  is `‖X'‖ ≤ (1 + K/ν) ‖X‖` ("Induction in `eq:exact-euler` gives `‖X_{n,j}‖ ≤ (1 + K/n)^j U`").

For the refinement estimate one coarse cell of mesh `ν` is compared with its two fine cells of mesh `κ = 2ν`. The
coarse node value is `x / D` with matrix `M / β`; the fine values are `w₀ / q₀`, `w₁ / q₁`, `w₂ / q₂` with the
matrices `M₀ / c₀` and `M₁ / c₁` at the two fine nodes. The coarse polygon takes the values `x / D`,
`y / (κ β D)` with `y = κ β x + M x` (its midpoint, by interpolation) and `x' / D'`. The numerators of the three
differences are `a₀ = x q₀ − w₀ D`, `a₁ = y q₁ − w₁ κ β D` and `a₂ = x' q₂ − w₂ D'`.

* `odd_step`: `a₁ = κ (κ β c₀ a₀ + β M₀ a₀ + q₀ (c₀ M − β M₀) x)`; the last term vanishes because `M / β` and
  `M₀ / c₀` are the matrix at the same point ("If `j = 2i` … `r_j = 0`"), hence
  `|a₁| ≤ κ β c₀ (κ + K) E₀` from `|a₀| ≤ E₀`: `e_{2i+1} ≤ (1 + K δ) e_{2i}`.
* `even_step`: `2 a₂ = (κ c₁ + M₁) a₁ + q₁ (κ (c₁ M − β M₁) x − M₁ M x)`, the cleared form of
  `eq:ode-residual-identity`, `r_j = δ ((B(t_{j−1}) − B(t_j)) x − δ B(t_j) B(t_{j−1}) x)`; with the Lipschitz
  bound `κ ‖c₁ M − β M₁‖ ≤ L β c₁` and `‖x‖ ≤ Ξ` it gives
  `2 |a₂| ≤ c₁ ((κ + K) E₁ + q₁ β (L + K²) Ξ)`: `e_{2i+2} ≤ (1 + K δ) e_{2i+1} + δ² (L + K²) Y`.
* `cell_majorant`: the two steps against a scalar majorant. If `κ^{j+2} |a₀| ≤ u_j D q₀` (with `κ p = κ^{j+2}`),
  then `κ^{j+3} |a₁| ≤ u_{j+1} κ β D q₁` and `κ^{j+4} |a₂| ≤ u_{j+2} D' q₂` for
  `u_{j+1} = (κ + K) u_j + κ^{j+1} H`, `H = (L + K²) Y`: the produced recurrence
  `eq:ode-produced-recurrence`, `e_{j+1} ≤ (1 + K δ) e_j + δ² H`, in the form consumed by
  `Foundations/OdeRefinement.node_bound`.
* `tele_step`: the triangle inequality for three rational vectors `A / α`, `B / β`, `Z / ζ`:
  `β (A ζ − Z α) = ζ (A β − B α) + α (B ζ − Z β)`.
-/

namespace LeanProofs.IPRA.Analysis.EulerAlgebra

open LeanProofs.IPRA.Foundations.SignedCone

variable {R : Type*} [CommRing R] {P : R → Prop} {d : ℕ}

/-! ## One Euler step -/

/-- `lem:ode-polybound`, one step: `‖X'‖ ≤ (1 + K/ν) ‖X‖`. -/
theorem node_step (hP : Cone P) {ν β K s T : R} {M : Fin d → Fin d → R} {x x' : Fin d → R}
    (hν : P ν) (hβ : P β) (hT : P T) (hM : RowBd P M (K * β))
    (hx' : ∀ i, x' i = ν * β * x i + ∑ k, M i k * x k)
    (hx : ∀ k, Bd P (s * x k) T) (i : Fin d) :
    Bd P (s * x' i) ((ν + K) * β * T) := by
  have e : ν * β * (s * x i) + ∑ k, M i k * (s * x k) = s * x' i := by
    rw [hx' i, dot_smul]; ring
  exact (((hx i).smul hP (hP.mul hν hβ)).add hP (hM.mulVec hP hT hx i)).congr e (by ring)

/-! ## One refinement cell -/

section Cell

variable {ν β c₀ c₁ K L s E₀ E₁ Ξ D D' q₀ q₁ q₂ : R} {M M₀ M₁ : Fin d → Fin d → R}
  {x x' y w₀ w₁ w₂ : Fin d → R}

/-- The first fine step of a coarse cell: `e_{2i+1} ≤ (1 + K δ) e_{2i}`. -/
theorem odd_step (hP : Cone P) (hν : P ν) (hβ : P β) (hc₀ : P c₀) (hE₀ : P E₀) (hΞ : P Ξ)
    (hM₀ : RowBd P M₀ (K * c₀))
    (hL₀ : RowBd P (fun i k => c₀ * M i k - β * M₀ i k) 0)
    (hy : ∀ k, y k = 2 * ν * β * x k + ∑ l, M k l * x l)
    (hw₁ : ∀ k, w₁ k = 2 * ν * c₀ * w₀ k + ∑ l, M₀ k l * w₀ l)
    (hq₁ : q₁ = 2 * ν * c₀ * q₀)
    (hx : ∀ k, Bd P (x k) Ξ)
    (he : ∀ k, Bd P (s * (x k * q₀ - w₀ k * D)) E₀) (k : Fin d) :
    Bd P (s * (y k * q₁ - w₁ k * (2 * ν * β * D))) (2 * ν * β * c₀ * (2 * ν + K) * E₀) := by
  have hz : c₀ * ∑ l, M k l * x l - β * ∑ l, M₀ k l * x l = 0 := by
    rw [← dot_comb]; exact hL₀.mulVec_zero hP hΞ hx k
  have ea : ∑ l, M₀ k l * (s * (x l * q₀ - w₀ l * D)) =
      s * (q₀ * ∑ l, M₀ k l * x l - D * ∑ l, M₀ k l * w₀ l) := by
    rw [dot_smul, dot_cross]
  have e : 2 * ν * (2 * ν * β * c₀) * (s * (x k * q₀ - w₀ k * D)) +
      2 * ν * β * ∑ l, M₀ k l * (s * (x l * q₀ - w₀ l * D)) =
      s * (y k * q₁ - w₁ k * (2 * ν * β * D)) := by
    rw [hy k, hw₁ k, hq₁]
    linear_combination (2 * ν * β) * ea - (2 * ν * s * q₀) * hz
  have h2ν : P (2 * ν) := hP.mul hP.two hν
  exact (((he k).smul hP (hP.mul h2ν (hP.mul (hP.mul h2ν hβ) hc₀))).add hP
    ((hM₀.mulVec hP hE₀ he k).smul hP (hP.mul h2ν hβ))).congr e (by ring)

/-- The second fine step of a coarse cell, with the exact residual `eq:ode-residual-identity`:
`e_{2i+2} ≤ (1 + K δ) e_{2i+1} + δ² (L + K²) Y`, doubled. -/
theorem even_step (hP : Cone P) (hν : P ν) (hβ : P β) (hc₁ : P c₁) (hK : P K) (hq₁ : P q₁) (hs : P s)
    (hE₁ : P E₁) (hΞ : P Ξ)
    (hM : RowBd P M (K * β)) (hM₁ : RowBd P M₁ (K * c₁))
    (hL₁ : RowBd P (fun i k => 2 * ν * (c₁ * M i k - β * M₁ i k)) (L * β * c₁))
    (hy : ∀ k, y k = 2 * ν * β * x k + ∑ l, M k l * x l)
    (hx' : ∀ k, x' k = ν * β * x k + ∑ l, M k l * x l)
    (hw₂ : ∀ k, w₂ k = 2 * ν * c₁ * w₁ k + ∑ l, M₁ k l * w₁ l)
    (hq₂ : q₂ = 2 * ν * c₁ * q₁) (hD' : D' = ν * β * D)
    (hx : ∀ k, Bd P (x k) Ξ)
    (he : ∀ k, Bd P (s * (y k * q₁ - w₁ k * (2 * ν * β * D))) E₁) (k : Fin d) :
    Bd P (2 * (s * (x' k * q₂ - w₂ k * D')))
      (c₁ * ((2 * ν + K) * E₁ + q₁ * β * s * (L + K * K) * Ξ)) := by
  have h2ν : P (2 * ν) := hP.mul hP.two hν
  have hsΞ : P (s * Ξ) := hP.mul hs hΞ
  have hsx : ∀ l, Bd P (s * x l) (s * Ξ) := fun l => (hx l).smul hP hs
  have hMx : ∀ l, Bd P (s * ∑ j, M l j * x j) (s * (K * β * Ξ)) := fun l =>
    (hM.mulVec hP hΞ hx l).smul hP hs
  have hKβΞ : P (s * (K * β * Ξ)) := hP.mul hs (hP.mul (hP.mul hK hβ) hΞ)
  -- the four bounded pieces
  have b1 := (he k).smul hP (hP.mul h2ν hc₁)
  have b2 := hM₁.mulVec hP hE₁ he k
  have b3 := hL₁.mulVec hP hsΞ hsx k
  have b4 := hM₁.mulVec hP hKβΞ hMx k
  -- the sums, expanded
  have e2 : ∑ l, M₁ k l * (s * (y l * q₁ - w₁ l * (2 * ν * β * D))) =
      s * (q₁ * ∑ l, M₁ k l * y l - 2 * ν * β * D * ∑ l, M₁ k l * w₁ l) := by
    rw [dot_smul, dot_cross]
  have ey : ∑ l, M₁ k l * y l =
      2 * ν * β * ∑ l, M₁ k l * x l + ∑ l, M₁ k l * ∑ j, M l j * x j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hy l]; ring
  have e3 : ∑ l, 2 * ν * (c₁ * M k l - β * M₁ k l) * (s * x l) =
      2 * ν * s * (c₁ * ∑ l, M k l * x l - β * ∑ l, M₁ k l * x l) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e4 : ∑ l, M₁ k l * (s * ∑ j, M l j * x j) = s * ∑ l, M₁ k l * ∑ j, M l j * x j :=
    dot_smul (fun l => M₁ k l) (fun l => ∑ j, M l j * x j) s
  have e : 2 * ν * c₁ * (s * (y k * q₁ - w₁ k * (2 * ν * β * D))) +
      ∑ l, M₁ k l * (s * (y l * q₁ - w₁ l * (2 * ν * β * D))) +
      q₁ * (∑ l, 2 * ν * (c₁ * M k l - β * M₁ k l) * (s * x l) -
        ∑ l, M₁ k l * (s * ∑ j, M l j * x j)) =
      2 * (s * (x' k * q₂ - w₂ k * D')) := by
    rw [e2, ey, e3, e4, hy k, hx' k, hw₂ k, hq₂, hD']
    ring
  exact ((b1.add hP b2).add hP ((b3.sub hP b4).smul hP hq₁)).congr e (by ring)

/-- Both fine steps of a coarse cell against a scalar majorant `u`: the produced recurrence
`eq:ode-produced-recurrence` with `u' = (κ + K) u + p H` and `u'' = (κ + K) u' + κ p H`, where `κ = 2ν`,
`H = (L + K²) Y`, and `κ p` is the power of `κ` that clears the majorant at the coarse node. -/
theorem cell_majorant (hP : Cone P) {p u Y : R} (hν : P ν) (hβ : P β) (hc₀ : P c₀) (hc₁ : P c₁)
    (hK : P K) (hL : P L) (hq₀ : P q₀) (hD : P D) (hp : P p) (hu : P u) (hY : P Y)
    (hM : RowBd P M (K * β)) (hM₀ : RowBd P M₀ (K * c₀)) (hM₁ : RowBd P M₁ (K * c₁))
    (hL₀ : RowBd P (fun i k => c₀ * M i k - β * M₀ i k) 0)
    (hL₁ : RowBd P (fun i k => 2 * ν * (c₁ * M i k - β * M₁ i k)) (L * β * c₁))
    (hy : ∀ k, y k = 2 * ν * β * x k + ∑ l, M k l * x l)
    (hx' : ∀ k, x' k = ν * β * x k + ∑ l, M k l * x l)
    (hw₁ : ∀ k, w₁ k = 2 * ν * c₀ * w₀ k + ∑ l, M₀ k l * w₀ l)
    (hw₂ : ∀ k, w₂ k = 2 * ν * c₁ * w₁ k + ∑ l, M₁ k l * w₁ l)
    (hq₁ : q₁ = 2 * ν * c₀ * q₀) (hq₂ : q₂ = 2 * ν * c₁ * q₁) (hD' : D' = ν * β * D)
    (hx : ∀ k, Bd P (x k) (Y * D))
    (he : ∀ k, Bd P (2 * ν * p * (x k * q₀ - w₀ k * D)) (u * (D * q₀))) :
    (∀ k, Bd P (2 * ν * (2 * ν * p) * (y k * q₁ - w₁ k * (2 * ν * β * D)))
        (((2 * ν + K) * u + p * ((L + K * K) * Y)) * (2 * ν * β * D * q₁))) ∧
      ∀ k, Bd P (2 * ν * (2 * ν) * (2 * ν * p) * (x' k * q₂ - w₂ k * D'))
        (((2 * ν + K) * ((2 * ν + K) * u + p * ((L + K * K) * Y)) + 2 * ν * p * ((L + K * K) * Y)) *
          (D' * q₂)) := by
  have h2ν : P (2 * ν) := hP.mul hP.two hν
  have hs : P (2 * ν * p) := hP.mul h2ν hp
  have hE₀ : P (u * (D * q₀)) := hP.mul hu (hP.mul hD hq₀)
  have hΞ : P (Y * D) := hP.mul hY hD
  have hH : P ((L + K * K) * Y) := hP.mul (hP.add hL (hP.mul hK hK)) hY
  have hq₁' : P q₁ := Cone.of_eq (hP.mul (hP.mul h2ν hc₀) hq₀) hq₁.symm
  have hκK : P (2 * ν + K) := hP.add h2ν hK
  have hodd := odd_step hP hν hβ hc₀ hE₀ hΞ hM₀ hL₀ hy hw₁ hq₁ hx he
  have hE₁ : P (2 * ν * β * c₀ * (2 * ν + K) * (u * (D * q₀))) :=
    hP.mul (hP.mul (hP.mul (hP.mul h2ν hβ) hc₀) hκK) hE₀
  have heven := even_step (L := L) hP hν hβ hc₁ hK hq₁' hs hE₁ hΞ hM hM₁ hL₁ hy hx' hw₂ hq₂ hD' hx hodd
  refine ⟨fun k => ?_, fun k => ?_⟩
  · refine (((hodd k).smul hP h2ν).congr (by ring) rfl).mono hP ?_
    refine Cone.of_eq (hP.mul (hP.mul (hP.mul (hP.mul (hP.mul (hP.mul h2ν h2ν) hβ) hc₀) hD) hq₀)
      (hP.mul hp hH)) ?_
    rw [hq₁]; ring
  · have h := ((heven k).congr rfl (show _ = 2 * (ν * β * c₀ * c₁ * ((2 * ν + K) * (2 * ν + K) * u * (D * q₀) +
        2 * ν * p * q₀ * ((L + K * K) * Y) * D)) by rw [hq₁]; ring)).half hP
    refine ((h.smul hP (hP.mul h2ν h2ν)).congr (by ring) rfl).mono hP ?_
    refine Cone.of_eq (hP.mul (hP.mul (hP.mul (hP.mul (hP.mul (hP.mul (hP.mul (hP.mul h2ν h2ν) hν) hβ) hc₀)
      hc₁) hD) hq₀) (hP.mul (hP.mul hκK hp) hH)) ?_
    rw [hD', hq₂, hq₁]; ring

end Cell

/-! ## The triangle inequality for rational vectors -/

/-- `|A/α − Z/ζ| ≤ |A/α − B/β| + |B/β − Z/ζ|`, cleared: from `s |A β − B α| ≤ E₁` and `t |B ζ − Z β| ≤ E₂`,
`s t β |A ζ − Z α| ≤ t ζ E₁ + s α E₂`. -/
theorem tele_step (hP : Cone P) {s t α β ζ A B Z E₁ E₂ : R} (hs : P s) (ht : P t) (hα : P α) (hζ : P ζ)
    (h₁ : Bd P (s * (A * β - B * α)) E₁) (h₂ : Bd P (t * (B * ζ - Z * β)) E₂) :
    Bd P (s * t * β * (A * ζ - Z * α)) (t * ζ * E₁ + s * α * E₂) :=
  ((h₁.smul hP (hP.mul ht hζ)).add hP (h₂.smul hP (hP.mul hs hα))).congr (by ring) rfl

end LeanProofs.IPRA.Analysis.EulerAlgebra
