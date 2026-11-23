import IPRADerivations.Core.IntCertificates

/-!
# Component transport and labels relative to stable locators

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/06_clusters.tex`, Proposition
`prop:component-transport` and Theorem `thm:stable-locators`, the metric estimates as iPRA derivations about
natural terms (distances cleared of a common denominator; the triangle inequalities of the ambient metric are
supplied as derived inequalities between the distance terms):

* `path_bound`, `path_bound_le` (`prop:component-transport`): "A shortest edge path between the centers of any
  paired slots … has at most `v − 1` edges. The triangle inequality gives `(v − 1)δ`": along a path with edges
  at most `δ`, the distance after `m` steps is at most `m δ`, and at most `M δ` for `m ≤ M` (the uniform bound
  with `M = 2N − 1`);
* `nearest_upper`: "If `x` is the occurrence assigned to `c_j` and `a` approximates `x`, then
  `d(a, c_j) ≤ r + ε`";
* `others_lower`: "For `i ≠ j`, two triangle inequalities give
  `d(a, c_i) ≥ d(c_i, c_j) − d(c_j, x) − d(x, a) ≥ r + γ − ε`";
* `unique_nearest`: "The second lower bound exceeds the first upper bound by at least `γ − 2ε ≥ γ/2 > 0`.
  Therefore `c_j` is the unique nearest anchor", for `4ε ≤ γ`: `2 d(a, c_j) + γ ≤ 2 d(a, c_i)`;
* `same_label`: "Samples carrying the same label at errors `ε` and `ε'` are within `ε + ε'` of one another".
-/

namespace LeanProofs.IPRA.Analysis.ClusterTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Along a path whose edges have length at most `δ`, the distance after `m` steps is at most `m δ`. -/
theorem path_bound (D : ℕ → PTm n) (δ : PTm n) (h0 : Γ ⊢[PRAAx] le (D 0) zero)
    (hstep : ∀ k, Γ ⊢[PRAAx] le (D (k + 1)) (D k + δ)) (m : ℕ) : Γ ⊢[PRAAx] le (D m) (num m * δ) := by
  induction m with
  | zero => ipra_le sl h0 using push_cast; ring
  | succ m ih =>
    have hm := hstep m
    ipra_le sl hm + sl ih using push_cast; ring

/-- The uniform bound: at most `M` edges (`M = v − 1`, or `2N − 1`). -/
theorem path_bound_le (D : ℕ → PTm n) (δ : PTm n) (h0 : Γ ⊢[PRAAx] le (D 0) zero)
    (hstep : ∀ k, Γ ⊢[PRAAx] le (D (k + 1)) (D k + δ)) {m M : ℕ} (hm : m ≤ M) :
    Γ ⊢[PRAAx] le (D m) (num M * δ) := by
  obtain ⟨e, rfl⟩ : ∃ e, M = m + e := ⟨M - m, by omega⟩
  have h := path_bound D δ h0 hstep m
  ipra_le sl h + (e : Groth (Q Γ)) * 𝔟 δ using push_cast; ring

/-- `d(a, c_j) ≤ r + ε`. -/
theorem nearest_upper {dacj dax dxcj r ε : PTm n} (htri : Γ ⊢[PRAAx] le dacj (dax + dxcj))
    (hx : Γ ⊢[PRAAx] le dxcj r) (ha : Γ ⊢[PRAAx] le dax ε) : Γ ⊢[PRAAx] le dacj (r + ε) := by
  ipra_le sl htri + sl hx + sl ha

/-- `r + γ ≤ d(a, c_i) + ε` for another anchor `c_i`. -/
theorem others_lower {dcc daci dax dxcj r γ ε : PTm n} (hsep : Γ ⊢[PRAAx] le (num 2 * r + γ) dcc)
    (htri : Γ ⊢[PRAAx] le dcc (daci + dax + dxcj)) (hx : Γ ⊢[PRAAx] le dxcj r)
    (ha : Γ ⊢[PRAAx] le dax ε) : Γ ⊢[PRAAx] le (r + γ) (daci + ε) := by
  ipra_le sl hsep + sl htri + sl hx + sl ha

/-- The assigned anchor is the unique nearest one, with margin `γ/2`. -/
theorem unique_nearest {dacj daci r γ ε : PTm n} (hup : Γ ⊢[PRAAx] le dacj (r + ε))
    (hlow : Γ ⊢[PRAAx] le (r + γ) (daci + ε)) (hε : Γ ⊢[PRAAx] le (num 4 * ε) γ) :
    Γ ⊢[PRAAx] le (num 2 * dacj + γ) (num 2 * daci) := by
  ipra_le 2 * sl hup + 2 * sl hlow + sl hε

/-- Two samples with the same label are within `ε + ε'`. -/
theorem same_label {daa dax da'x ε ε' : PTm n} (htri : Γ ⊢[PRAAx] le daa (dax + da'x))
    (ha : Γ ⊢[PRAAx] le dax ε) (ha' : Γ ⊢[PRAAx] le da'x ε') : Γ ⊢[PRAAx] le daa (ε + ε') := by
  ipra_le sl htri + sl ha + sl ha'

end LeanProofs.IPRA.Analysis.ClusterTransport
