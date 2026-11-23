import IPRADerivations.Topology.BarycentricMesh

/-!
# The hairy ball search: correction, modulus and grid rounding

Packet: `topology/hairy_ball_ipra`, `sections/search.tex` ("From noisy values to a bounded witness"), the
estimates between the correction of the observed vectors and the search grid, as iPRA derivations (norms as
natural terms cleared of denominators, rounding errors as integer terms):

* `correction_bound`: "Since `(∑ |p_i|)² ≤ d ∑ p_i²`, the denominator is at least `1/d` … Condition (T) and
  `‖p‖ = 1` give the explicit correction bound `‖v_p − a_p‖ ≤ dδ`": from `corr · (p·p) ≤ |p·a|`,
  `|p·a| ≤ δ` and `1 ≤ d (p·p)` (cleared by the unit `J`);
* `corrected_modulus`: "At two points within `2^{-μ(h)}`, condition (U) now gives
  `‖v_p − v_q‖ ≤ (2d + 3)δ`";
* `precision_choice`: "`(2d + 3)δ ≤ e/(32d)`" from `δ ≤ e/(256 d (d + 1))`;
* `round_dist`: "The discrepancy in the last coordinate is the sum of the other rounding errors before
  restoring signs. Hence `‖p − q‖ ≤ 2(d − 1)/D`": rounding errors `0 ≤ e_i ≤ 1` in `m = d − 1` coordinates give
  total `ℓ¹` error `∑ e_i + ∑ e_i ≤ 2m`.
-/

namespace LeanProofs.IPRA.Topology.HairyBallSearch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.BarycentricMesh (mul_cancel_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The correction bound `‖v_p − a_p‖ ≤ dδ`: `corr · pp ≤ c J`, `c ≤ δ`, `J ≤ d · pp` and `pp ≥ 1` give
`corr ≤ d δ`. -/
theorem correction_bound (d : ℕ) {corr pp c δ J : PTm n} (hcorr : Γ ⊢[PRAAx] le (corr * pp) (c * J))
    (hc : Γ ⊢[PRAAx] le c δ) (hpp : Γ ⊢[PRAAx] le J (num d * pp)) (hpos : Γ ⊢[PRAAx] le (succ zero) pp) :
    Γ ⊢[PRAAx] le corr (num d * δ) := by
  refine mul_cancel_le hpos ?_
  ipra_le sl hcorr + sl hc * 𝔟 J + 𝔟 δ * sl hpp

/-- `‖v_p − v_q‖ ≤ (2d + 3)δ` from the two corrections and condition (U). -/
theorem corrected_modulus (d : ℕ) {dv c₁ c₂ da δ : PTm n} (h : Γ ⊢[PRAAx] le dv (c₁ + c₂ + da))
    (h₁ : Γ ⊢[PRAAx] le c₁ (num d * δ)) (h₂ : Γ ⊢[PRAAx] le c₂ (num d * δ))
    (hU : Γ ⊢[PRAAx] le da (num 3 * δ)) : Γ ⊢[PRAAx] le dv (num (2 * d + 3) * δ) := by
  ipra_le sl h + sl h₁ + sl h₂ + sl hU using push_cast; ring

/-- The proof precision: `256 d (d + 1) δ ≤ e` gives `32 d (2d + 3) δ ≤ e`. -/
theorem precision_choice (d : ℕ) {δ e : PTm n} (h : Γ ⊢[PRAAx] le (num (256 * d * (d + 1)) * δ) e) :
    Γ ⊢[PRAAx] le (num (32 * d * (2 * d + 3)) * δ) e := by
  ipra_le sl h + ((192 * d * d + 160 * d : ℕ) : Groth (Q Γ)) * 𝔟 δ using push_cast; ring

/-- The rounding distance: errors `0 ≤ e_i ≤ 1` in `m` coordinates and their sum in the last coordinate. -/
theorem round_dist {m : ℕ} (e : Fin m → ZT n) (h₁ : ∀ i, Γ ⊢[PRAAx] zle (e i) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin e + ZT.sumFin e) (ZT.natLit (2 * m)) := by
  refine zle_of_comb (2 * ∑ i, zsl (h₁ i)) ?_ (nn_mul (nn_ofNat 2) (nn_sum _ _ fun i _ => nn_zsl _))
  simp only [zsl_def, ZT.toZ_add, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end LeanProofs.IPRA.Topology.HairyBallSearch
