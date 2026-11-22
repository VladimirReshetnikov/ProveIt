import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Core.OrderCertificates

/-!
# The Lipschitz estimate of the tent partition of unity

Packet: `foundations/ipra_abstract_analysis_2026-11-20`, `sections/topology.tex`, Lemma `lem:tent-partition`: for
an `r/2`-net `c_0, …, c_{n−1}`, the tent weights `w_i(x) = max(0, r − d(x, c_i))`, `W = ∑ w_i` and
`λ_i = w_i/W` satisfy `∑_i |λ_i(x) − λ_i(y)| ≤ (4n/r) d(x, y)`. The proof: `|w_i(x) − w_i(y)| ≤ d(x, y)`,
`|W(x) − W(y)| ≤ n d(x, y)`, then
`|λ_i(x) − λ_i(y)| ≤ |w_i(x) − w_i(y)|/W(x) + w_i(y)|W(y) − W(x)|/(W(x)W(y))`, summed, with `W(x) ≥ r/2`.

Over natural numerators, for a list of rows `(u_i, u'_i) = (w_i(x), w_i(y))` of any length `n` with the
1-Lipschitz bounds `u_i ≤ u'_i + d`, `u'_i ≤ u_i + d`, `W = ∑ u_i`, `W' = ∑ u'_i`:

* `shift_xy`, `shift_yx`: `W ≤ W' + n d` and `W' ≤ W + n d`;
* `row_bound`: `|u W' − u' W| ≤ d W' + u' f` whenever `|W − W'| ≤ f` (the add-and-subtract step cleared of
  `W W'`);
* `sum_bound`: `∑_i |u_i W' − u'_i W| ≤ n d W' + f W'`;
* `tent_lipschitz`: if `r ≤ 2W` then `r ∑_i |u_i W' − u'_i W| ≤ 4 n d W W'`, i.e.
  `∑_i |λ_i(x) − λ_i(y)| ≤ 4nd/r`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Topology.TentPartition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `W(x) = ∑ u_i`. -/
def Wx : List (PTm n × PTm n) → PTm n
  | [] => zero
  | p :: ps => p.1 + Wx ps

/-- `W(y) = ∑ u'_i`. -/
def Wy : List (PTm n × PTm n) → PTm n
  | [] => zero
  | p :: ps => p.2 + Wy ps

/-- `∑_i |u_i A − u'_i B|`. -/
def sumAd (A B : PTm n) : List (PTm n × PTm n) → PTm n
  | [] => zero
  | p :: ps => ad (p.1 * A) (p.2 * B) + sumAd A B ps

theorem shift_xy (L : List (PTm n × PTm n)) (d : PTm n) (h : ∀ p ∈ L, Γ ⊢[PRAAx] le p.1 (p.2 + d)) :
    Γ ⊢[PRAAx] le (Wx L) (Wy L + num L.length * d) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le zero (zero + num 0 * d)
    ipra_le 0
  | cons p ps ih =>
    show Γ ⊢[PRAAx] le (p.1 + Wx ps) ((p.2 + Wy ps) + num (ps.length + 1) * d)
    have hp := h p List.mem_cons_self
    have hs := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    ipra_le sl hp + sl hs using
      push_cast; ring

theorem shift_yx (L : List (PTm n × PTm n)) (d : PTm n) (h : ∀ p ∈ L, Γ ⊢[PRAAx] le p.2 (p.1 + d)) :
    Γ ⊢[PRAAx] le (Wy L) (Wx L + num L.length * d) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le zero (zero + num 0 * d)
    ipra_le 0
  | cons p ps ih =>
    show Γ ⊢[PRAAx] le (p.2 + Wy ps) ((p.1 + Wx ps) + num (ps.length + 1) * d)
    have hp := h p List.mem_cons_self
    have hs := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    ipra_le sl hp + sl hs using
      push_cast; ring

/-- One row: `|u A − u' B| ≤ d A + u' f` when `|u − u'| ≤ d` and `|A − B| ≤ f`. -/
theorem row_bound {u u' A B d f : PTm n} (hu : Γ ⊢[PRAAx] le u (u' + d)) (hu' : Γ ⊢[PRAAx] le u' (u + d))
    (hA : Γ ⊢[PRAAx] le A (B + f)) (hB : Γ ⊢[PRAAx] le B (A + f)) :
    Γ ⊢[PRAAx] le (ad (u * A) (u' * B)) (d * A + u' * f) := by
  refine ad_le_of ?_ ?_
  · ipra_le 𝔟 A * sl hu + 𝔟 u' * sl hA
  · ipra_le 𝔟 A * sl hu' + 𝔟 u' * sl hB

/-- `∑_i |u_i A − u'_i B| ≤ n d A + f ∑_i u'_i`. -/
theorem sum_bound (L : List (PTm n × PTm n)) {A B d f : PTm n}
    (h1 : ∀ p ∈ L, Γ ⊢[PRAAx] le p.1 (p.2 + d)) (h2 : ∀ p ∈ L, Γ ⊢[PRAAx] le p.2 (p.1 + d))
    (hA : Γ ⊢[PRAAx] le A (B + f)) (hB : Γ ⊢[PRAAx] le B (A + f)) :
    Γ ⊢[PRAAx] le (sumAd A B L) (num L.length * d * A + f * Wy L) := by
  induction L with
  | nil =>
    show Γ ⊢[PRAAx] le zero (num 0 * d * A + f * zero)
    ipra_le 0
  | cons p ps ih =>
    show Γ ⊢[PRAAx] le (ad (p.1 * A) (p.2 * B) + sumAd A B ps)
      (num (ps.length + 1) * d * A + f * (p.2 + Wy ps))
    have hr := row_bound (h1 p List.mem_cons_self) (h2 p List.mem_cons_self) hA hB
    have hs := ih (fun q hq => h1 q (List.mem_cons_of_mem _ hq)) (fun q hq => h2 q (List.mem_cons_of_mem _ hq))
    ipra_le sl hr + sl hs using
      push_cast; ring

/-- `lem:tent-partition`: `∑_i |λ_i(x) − λ_i(y)| ≤ 4nd/r`, cleared of `r W W'`. -/
theorem tent_lipschitz (L : List (PTm n × PTm n)) {d r : PTm n}
    (h1 : ∀ p ∈ L, Γ ⊢[PRAAx] le p.1 (p.2 + d)) (h2 : ∀ p ∈ L, Γ ⊢[PRAAx] le p.2 (p.1 + d))
    (hr : Γ ⊢[PRAAx] le r (num 2 * Wx L)) :
    Γ ⊢[PRAAx] le (r * sumAd (Wy L) (Wx L) L) (num 4 * num L.length * d * (Wx L * Wy L)) := by
  have hs := sum_bound L h1 h2 (shift_yx L d h2) (shift_xy L d h1)
  ipra_le 𝔟 (sumAd (Wy L) (Wx L) L) * sl hr + 2 * 𝔟 (Wx L) * sl hs

end LeanProofs.IPRA.Topology.TentPartition
