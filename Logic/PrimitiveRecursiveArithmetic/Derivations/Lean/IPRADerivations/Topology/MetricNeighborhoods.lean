import IPRADerivations.Core.OrderCertificates

/-!
# Neighbourhood comparisons: compact-open sandwich, evaluation, currying, metrization

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, the finite triangle-inequality
cores, cleared for natural terms (distances `d(·,·)` as hypotheses `le` with their triangle inequalities):

* `thm:compact-open-cube` (`eq:compact-open-sandwich`, in units `e = ε/4`):
  `sandwich_inner`, "If `d_∞(f, g) < ε/4`, then for `x ∈ C_j`, `d(g(x), f(p_j)) ≤ d(g(x), f(x)) + d(f(x), f(p_j))
  < ε/2`"; `sandwich_outer`, "`d(f(x), g(x)) < ε/4 + ε/2 = 3ε/4`" (so `< ε` with a uniform margin);
  `margin_ball`, the general condition `[C, U]` with a supplied margin `δ`: `B_∞(f, δ) ⊆ [C, U]`;
* `prop:metric-evaluation` (`evaluation`): `d(f(x), g(y)) ≤ d(f(x), f(y)) + d(f(y), g(y)) ≤ 2 h` for two
  half-bounds `h`;
* `thm:metric-currying`, the converse direction (`currying`): `d(H(x, z), H(x', z')) ≤ 2 h` from the slice
  distance and the common slice modulus;
* `thm:coordinate-metrization`, the inverse neighbourhood transformation (`metrization_inverse`):
  `|u_i(x) − u_i(y)| ≤ 2^{i+1} D`, `2^N D < ε` and `i + 1 ≤ N` give `|u_i(x) − u_i(y)| < ε`.
-/

namespace LeanProofs.IPRA.Topology.MetricNeighborhoods

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {gx fx fp e : PTm n}

/-- `d(g(x), f(x)) < e` and `d(f(x), f(p)) ≤ e` give `d(g(x), f(p)) < 2e` (`ε/2` in units `e = ε/4`). -/
theorem sandwich_inner {dgf dff dgp : PTm n} (htri : Γ ⊢[PRAAx] le dgp (dgf + dff))
    (h₁ : Γ ⊢[PRAAx] le (succ dgf) e) (h₂ : Γ ⊢[PRAAx] le dff e) :
    Γ ⊢[PRAAx] le (succ dgp) (num 2 * e) := by
  ipra_le sl htri + sl h₁ + sl h₂

/-- `d(g(x), f(p)) < 2e` and `d(f(x), f(p)) ≤ e` give `d(f(x), g(x)) < 3e`, hence `< 4e = ε`. -/
theorem sandwich_outer {dfg dgp dfp : PTm n} (htri : Γ ⊢[PRAAx] le dfg (dfp + dgp))
    (h₁ : Γ ⊢[PRAAx] le (succ dgp) (num 2 * e)) (h₂ : Γ ⊢[PRAAx] le dfp e) :
    (Γ ⊢[PRAAx] le (succ dfg) (num 3 * e)) ∧ (Γ ⊢[PRAAx] le (succ dfg) (num 4 * e)) := by
  refine ⟨?_, ?_⟩
  · ipra_le sl htri + sl h₁ + sl h₂
  · ipra_le sl htri + sl h₁ + sl h₂ + 𝔟 e

/-- A supplied margin: `d(f(x), g(x)) < δ` and `B(f(x), δ) ⊆ U` put `g(x)` in `U`. -/
theorem margin_ball (U : PTm n → Fm PTm n) {d δ gx' : PTm n} (hd : Γ ⊢[PRAAx] le (succ d) δ)
    (hU : Γ ⊢[PRAAx] le (succ d) δ ⟶ U gx') : Γ ⊢[PRAAx] U gx' :=
  .impE hU hd

/-- `prop:metric-evaluation`: `d(f(x), g(y)) ≤ 2 h`. -/
theorem evaluation {dfxgy dfxfy dfygy h : PTm n} (htri : Γ ⊢[PRAAx] le dfxgy (dfxfy + dfygy))
    (h₁ : Γ ⊢[PRAAx] le dfxfy h) (h₂ : Γ ⊢[PRAAx] le dfygy h) : Γ ⊢[PRAAx] le dfxgy (num 2 * h) := by
  ipra_le sl htri + sl h₁ + sl h₂

/-- `thm:metric-currying`, converse: `d(H(x, z), H(x', z')) ≤ 2 h`. -/
theorem currying {dH dslice dmod h : PTm n} (htri : Γ ⊢[PRAAx] le dH (dslice + dmod))
    (h₁ : Γ ⊢[PRAAx] le dslice h) (h₂ : Γ ⊢[PRAAx] le dmod h) : Γ ⊢[PRAAx] le dH (num 2 * h) := by
  ipra_le sl htri + sl h₁ + sl h₂

/-- `2^a D ≤ 2^{a+m} D`. -/
theorem pow_mono_D (D : PTm n) (a : ℕ) : ∀ m, Γ ⊢[PRAAx] le (num (2 ^ a) * D) (num (2 ^ (a + m)) * D)
  | 0 => le_refl _
  | m + 1 => by
    have ih := pow_mono_D D a m
    show Γ ⊢[PRAAx] le (num (2 ^ a) * D) (num (2 ^ (a + m + 1)) * D)
    ipra_le sl ih + 2 ^ (a + m) * 𝔟 D using push_cast; ring

/-- `thm:coordinate-metrization`, inverse transformation: `c_i ≤ 2^{i+1} D`, `2^N D < ε`, `i + 1 ≤ N` give
`c_i < ε`. -/
theorem metrization_inverse {c D ε : PTm n} {i N : ℕ} (hi : i + 1 ≤ N)
    (hc : Γ ⊢[PRAAx] le c (num (2 ^ (i + 1)) * D)) (hD : Γ ⊢[PRAAx] le (succ (num (2 ^ N) * D)) ε) :
    Γ ⊢[PRAAx] le (succ c) ε := by
  obtain ⟨m, rfl⟩ : ∃ m, N = i + 1 + m := ⟨N - (i + 1), by omega⟩
  have hm := pow_mono_D (Γ := Γ) D (i + 1) m
  ipra_le sl hc + sl hD + sl hm

end LeanProofs.IPRA.Topology.MetricNeighborhoods
