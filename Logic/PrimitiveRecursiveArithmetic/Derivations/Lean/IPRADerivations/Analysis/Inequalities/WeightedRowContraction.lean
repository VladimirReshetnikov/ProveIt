import IPRADerivations.Probability.BayesEvents

/-!
# Weighted row domination and the half-contraction certificate

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `lean/FeedbackReference.lean` (an ambient Lean
reference model; the object-theory port is open there): `row_domination` ("`x ≤ r w` coordinatewise and
`A ≥ 0` give `(Ax)_i ≤ r (Aw)_i`") and `half_contract` (a `HalfCertificate`, `2 (Aw)_i ≤ w_i`, makes a map with
gain `|f x − f y|_i ≤ (A|x − y|)_i` contract the weighted distance by `1/2`).

For one row `(a_j)` of nonnegative entries and a finite list of columns `j`, with weights `w_j`, a vector `z_j`
(the coordinate distances) and a scale `r`, all natural terms:

* `row_domination`: `z_j ≤ r w_j` for all `j` gives `∑ a_j z_j ≤ r ∑ a_j w_j`;
* `half_contract_row`: if moreover `2 ∑ a_j w_j ≤ w_i` (the certificate row) and the gain bound
  `g ≤ ∑ a_j z_j`, then `2 g ≤ r w_i`, i.e. the image coordinate is within `(r/2) w_i`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.WeightedRowContraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le)
open LeanProofs.IPRA.Probability.BayesEvents (wsum_mul wsum_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {α : Type} (a w z : α → PTm n) (L : List α)

/-- `z ≤ r w` coordinatewise gives `∑ a z ≤ r ∑ a w`. -/
theorem row_domination {r : PTm n} (h : ∀ j ∈ L, Γ ⊢[PRAAx] le (z j) (r * w j)) :
    Γ ⊢[PRAAx] le (wsum a z L) (r * wsum a w L) := by
  have s := wsum_le (Γ := Γ) a z (fun j => r * w j) (fun _ => zero) L
    fun j hj => le_congr (.eqRefl _) (add_zero _).eqSymm (h j hj)
  have e := natEq (wsum_mul (Γ := Γ) a w r L)
  have z0 := natEq (wsum_zero (Γ := Γ) a L)
  ipra_le sl s with e + z0

/-- The half-contraction of one coordinate: `2 g ≤ r w_i`. -/
theorem half_contract_row {r wi g : PTm n} (h : ∀ j ∈ L, Γ ⊢[PRAAx] le (z j) (r * w j))
    (hcert : Γ ⊢[PRAAx] le (two * wsum a w L) wi) (hg : Γ ⊢[PRAAx] le g (wsum a z L)) :
    Γ ⊢[PRAAx] le (two * g) (r * wi) := by
  have hd := row_domination a w z L h
  ipra_le 2 * sl hg + 2 * sl hd + 𝔟 r * sl hcert

end LeanProofs.IPRA.Analysis.WeightedRowContraction
