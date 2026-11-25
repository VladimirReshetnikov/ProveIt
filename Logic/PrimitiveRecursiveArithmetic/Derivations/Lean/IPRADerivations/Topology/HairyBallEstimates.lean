import IPRADerivations.Core.CertificateTactics

/-!
# The constructive hairy ball theorem: correction, chart and search estimates

Packet: `topology/hairy_ball_ipra`, `sections/degree.tex` (Lemma `lem:mesh`), `sections/search.tex` and
`sections/rationalround.tex`, the finite arithmetic around the obstruction, as iPRA derivations about integer
terms (`ZT`, rational data cleared of denominators) and natural terms. (The obstruction itself is the cycle of
`Topology/SphereCycle`, the prism of `Topology/PrismIdentity` and the carrier identity of
`Topology/CarrierHomotopy`.)

* `correction_tangent` ("Correcting each observed vector"): for `v_p = a_p − (p·a_p / p·p) p`, "Dotting with
  `p` gives exactly zero", cleared by `p·p`: `p · ((p·p) a − (p·a) p) = 0`;
* `chart_unit` (the inverse stereographic chart): "The identity `4U + (1 − U)² = (1 + U)²` proves that the
  output lies on the unit sphere", with `U = ∑ u_j²`: `∑ (2u_j)² + (1 − U)² = (1 + U)²`;
* `chord` (the chord identity): `‖Φ(v) − Φ(u)‖² = 4 ‖v − u‖² / ((1 + V)(1 + U))`, cleared by
  `(1 + U)² (1 + V)²`;
* `mesh_step`, `mesh_rate` (Lemma `lem:mesh`): "For `n ≥ 1`, Bernoulli's inequality gives `(1 + 1/n)^n ≥ 2`",
  that is `2 n^n ≤ (n + 1)^n`, so `n` subdivisions with factor `n/(n+1)` halve the diameter;
* `grid_bound`, `tail_bound`, `round_bound` (the search): with `u = e/256`,
  `e/2 + dδ + 2·2^{-t} + 3·2^{-t} ≤ 3e/4`, `3e/4 + 2e/64 = 25e/32` and
  `(3/4 + 3/64 + 2/64) e = (53/64) e`;
* `round_last` (moving to the search grid): "The discrepancy in the last coordinate is the sum of the other
  rounding errors": `c_d = D − ∑_{i<d} c_i` and `∑ b_i D = D` give `D b_d − c_d = −∑_{i<d} (D b_i − c_i)`.
-/

namespace LeanProofs.IPRA.Topology.HairyBallEstimates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Identities in a commutative ring -/

section Ring

variable {A : Type*} [CommRing A]

/-- `p · ((p·p) a − (p·a) p) = 0`. -/
theorem correction_identity (p a : Fin d → A) :
    ∑ j, p j * ((∑ i, p i * p i) * a j - (∑ i, p i * a i) * p j) = 0 := by
  have h : ∑ j, p j * ((∑ i, p i * p i) * a j - (∑ i, p i * a i) * p j) =
      (∑ i, p i * p i) * ∑ j, p j * a j - (∑ i, p i * a i) * ∑ j, p j * p j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  ring

/-- `∑ (2u_j)² + (1 − U)² = (1 + U)²`. -/
theorem chart_identity (u : Fin d → A) :
    ∑ j, (2 * u j) ^ 2 + (1 - ∑ i, u i ^ 2) ^ 2 = (1 + ∑ i, u i ^ 2) ^ 2 := by
  have h : ∑ j, (2 * u j) ^ 2 = 4 * ∑ j, u j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  ring

theorem expand_diff (v u : Fin d → A) :
    ∑ j, (v j - u j) ^ 2 = ∑ j, v j ^ 2 - 2 * ∑ j, v j * u j + ∑ j, u j ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem expand_chart (v u : Fin d → A) (a b : A) :
    ∑ j, (2 * v j * a - 2 * u j * b) ^ 2 =
      4 * a ^ 2 * ∑ j, v j ^ 2 - 8 * a * b * ∑ j, v j * u j + 4 * b ^ 2 * ∑ j, u j ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The chord identity of the stereographic chart, cleared of denominators. -/
theorem chord_identity (v u : Fin d → A) :
    ∑ j, (2 * v j * (1 + ∑ i, u i ^ 2) - 2 * u j * (1 + ∑ i, v i ^ 2)) ^ 2 +
        ((1 - ∑ i, v i ^ 2) * (1 + ∑ i, u i ^ 2) - (1 - ∑ i, u i ^ 2) * (1 + ∑ i, v i ^ 2)) ^ 2 =
      4 * ((1 + ∑ i, u i ^ 2) * (1 + ∑ i, v i ^ 2)) * ∑ j, (v j - u j) ^ 2 := by
  have h₁ := expand_diff v u
  have h₂ := expand_chart v u (1 + ∑ i, u i ^ 2) (1 + ∑ i, v i ^ 2)
  linear_combination h₂ - 4 * ((1 + ∑ i, u i ^ 2) * (1 + ∑ i, v i ^ 2)) * h₁

end Ring

/-! ## The tangential correction and the chart -/

/-- "Dotting with `p` gives exactly zero": `p · ((p·p) a − (p·a) p) = 0`. -/
theorem correction_tangent (p a : Fin d → ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.sumFin fun j => p j * ((ZT.sumFin fun i => p i * p i) * a j - (ZT.sumFin fun i => p i * a i) * p j))
      (ZT.natLit 0) := by
  have e := correction_identity (fun j => ZT.toZ Γ (p j)) (fun j => ZT.toZ Γ (a j))
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- The chart lands on the unit sphere: `∑ (2u_j)² + (1 − U)² = (1 + U)²`. -/
theorem chart_unit (u : Fin d → ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      ((ZT.sumFin fun j => ZT.sq (ZT.natLit 2 * u j)) + ZT.sq (ZT.natLit 1 - ZT.sumFin fun i => ZT.sq (u i)))
      (ZT.sq (ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (u i))) := by
  have e := chart_identity (fun j => ZT.toZ Γ (u j))
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- The chord identity: `‖Φ(v) − Φ(u)‖² (1 + U)² (1 + V)² = 4 (1 + U)(1 + V) ‖v − u‖²`. -/
theorem chord (v u : Fin d → ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      ((ZT.sumFin fun j => ZT.sq (ZT.natLit 2 * v j * (ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (u i)) -
          ZT.natLit 2 * u j * (ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (v i)))) +
        ZT.sq ((ZT.natLit 1 - ZT.sumFin fun i => ZT.sq (v i)) * (ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (u i)) -
          (ZT.natLit 1 - ZT.sumFin fun i => ZT.sq (u i)) * (ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (v i))))
      (ZT.natLit 4 * ((ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (u i)) *
          (ZT.natLit 1 + ZT.sumFin fun i => ZT.sq (v i))) * ZT.sumFin fun j => ZT.sq (v j - u j)) := by
  have e := chord_identity (fun j => ZT.toZ Γ (v j)) (fun j => ZT.toZ Γ (u j))
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-! ## The mesh after barycentric subdivision -/

theorem bernoulli_aux (N : ℕ) : ∀ m : ℕ, N ^ m * (N + m) ≤ (N + 1) ^ m * N
  | 0 => by simp
  | m + 1 => by
    have ih := bernoulli_aux N m
    have e : N ^ (m + 1) * (N + (m + 1)) + m * N ^ m = (N + 1) * (N ^ m * (N + m)) := by ring
    calc N ^ (m + 1) * (N + (m + 1)) ≤ (N + 1) * (N ^ m * (N + m)) := Nat.le.intro e
      _ ≤ (N + 1) * ((N + 1) ^ m * N) := Nat.mul_le_mul_left _ ih
      _ = (N + 1) ^ (m + 1) * N := by ring

/-- Bernoulli: `2 N^N ≤ (N + 1)^N` for `N ≥ 1`. -/
theorem bernoulli {N : ℕ} (hN : 1 ≤ N) : 2 * N ^ N ≤ (N + 1) ^ N := by
  have h := bernoulli_aux N N
  have e : N ^ N * (N + N) = 2 * N ^ N * N := by ring
  rw [e] at h
  exact Nat.le_of_mul_le_mul_right h hN

/-- One subdivision: a distance at most `N/(N+1)` of the parent diameter, iterated: `(N+1) δ' ≤ N δ`. -/
theorem mesh_step (N : ℕ) {b δ δ' : PTm n} (h : Γ ⊢[PRAAx] le (num (N + 1) * b) (num N * δ))
    (hb : Γ ⊢[PRAAx] le δ' b) : Γ ⊢[PRAAx] le (num (N + 1) * δ') (num N * δ) := by
  ipra_le sl h + ((N + 1 : ℕ) : Groth (Q Γ)) * sl hb using push_cast; ring

/-- `lem:mesh`: `N` subdivisions halve the diameter, `2 N^N ≤ (N + 1)^N`. -/
theorem mesh_rate {N : ℕ} (hN : 1 ≤ N) : Γ ⊢[PRAAx] le (num (2 * N ^ N)) (num ((N + 1) ^ N)) := by
  obtain ⟨c, hc⟩ : ∃ c, (N + 1) ^ N = 2 * N ^ N + c := ⟨(N + 1) ^ N - 2 * N ^ N, by have := bernoulli hN; omega⟩
  rw [hc]
  ipra_le (c : Groth (Q Γ)) using push_cast; ring

/-! ## The search -/

/-- `‖A(q,t)‖ ≤ e/2 + dδ + 2·2^{-t} + 3·2^{-t} ≤ 3e/4`, in units `u = e/256` (`dδ ≤ u`, `2^{-t} = 4u`). -/
theorem grid_bound {L L₁ c u : PTm n} (h₁ : Γ ⊢[PRAAx] le L₁ (num 128 * u + c)) (hc : Γ ⊢[PRAAx] le c u)
    (h₂ : Γ ⊢[PRAAx] le L (L₁ + num 5 * (num 4 * u))) : Γ ⊢[PRAAx] le L (num 192 * u) := by
  ipra_le sl h₂ + sl h₁ + sl hc + 43 * 𝔟 u

/-- "For any such candidate and every `j ≥ t`, (C) gives `‖A(q,j)‖ ≤ 3e/4 + 2e/64 = 25e/32`." -/
theorem tail_bound {Lj L u : PTm n} (h : Γ ⊢[PRAAx] le L (num 192 * u))
    (hC : Γ ⊢[PRAAx] le Lj (L + num 2 * (num 4 * u))) : Γ ⊢[PRAAx] le Lj (num 200 * u) := by
  ipra_le sl hC + sl h

/-- The round witness: `(3/4 + 3/64 + 2/64) e = (53/64) e`. -/
theorem round_bound {Lw L u : PTm n} (h : Γ ⊢[PRAAx] le L (num 192 * u))
    (hUC : Γ ⊢[PRAAx] le Lw (L + num 3 * (num 4 * u) + num 2 * (num 4 * u))) :
    Γ ⊢[PRAAx] le Lw (num 212 * u) := by
  ipra_le sl hUC + sl h

/-- The last grid coordinate: `∑_i D b_i = D` and `c_d = D − ∑_{i<d} c_i` give
`D b_d − c_d = −∑_{i<d} (D b_i − c_i)`. -/
theorem round_last (Db c : Fin d → ZT n) {D Dbd cd : ZT n}
    (hb : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin Db + Dbd) D) (hc : Γ ⊢[PRAAx] ZT.eq cd (D - ZT.sumFin c)) :
    Γ ⊢[PRAAx] ZT.eq (Dbd - cd) (-(ZT.sumFin fun i => Db i - c i)) := by
  ipra_lc [Finset.sum_sub_distrib] ZT.toZ_eq hb - ZT.toZ_eq hc

end LeanProofs.IPRA.Topology.HairyBallEstimates
