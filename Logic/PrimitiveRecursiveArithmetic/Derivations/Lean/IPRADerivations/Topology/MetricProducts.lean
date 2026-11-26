import IPRADerivations.Topology.MetricUrysohn

/-!
# Weighted product metrics and local-gap Urysohn separation

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, cleared of the dyadic
denominators and stated for natural terms:

* `thm:weighted-product`, `thm:countable-net-product` ("The finite geometric sum gives
  `∑_{i=N}^{L−1} 2^{−i−1} ≤ 2^{−N}`"): for coordinate distances `d_i ≤ Q`, the Horner form
  `H_0 = 0`, `H_{j+1} = 2 H_j + d_{N+j}` (that is `2^j ∑_{i<j} 2^{−i−1} d_{N+i}`) satisfies `H_j + Q ≤ 2^j Q`
  (`tail_bound`), i.e. `∑_{i<j} 2^{−i−1} d_{N+i} ≤ (1 − 2^{−j}) Q`; with the outer weight `2^{−N}` this is the
  certified tail `D − D_N ≤ 2^{−N}` (`eq:product-tail`), and with `Q = 2^{−k−2}` on the first `k + 2`
  coordinates it is the net error of the countable product;
* `eq:coordinate-bound` (`2^{−i−1} d_i(x_i, y_i) ≤ D(x, y)`): `2^{j−1−i} d_{N+i} ≤ H_j` for `i < j`
  (`coord_bound`);
* `prop:local-urysohn` ("Since `a + b` is `2`-Lipschitz, `a(y) + b(y) ≥ δ_x − 2d(x, y) ≥ δ_x/2`"):
  `local_gap` (`δ ≤ s' + 2d`), `half_gap` (`4d ≤ δ` gives `δ ≤ 2 s'`), and `local_lipschitz`, the cleared
  estimate `|u(x) − u(y)| ≤ 2 d/δ`: `δ a s' ≤ δ a' s + 2 s s' d` and symmetrically.
-/

namespace LeanProofs.IPRA.Topology.MetricProducts

open_ipra
open LeanProofs.IPRA.Topology.MetricUrysohn (numerator_upper numerator_lower)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The weighted product metric -/

/-- The Horner form `H_j = ∑_{i<j} 2^{j−1−i} d_{N+i}`. -/
def horner (d : ℕ → PTm n) (N : ℕ) : ℕ → PTm n
  | 0 => zero
  | j + 1 => num 2 * horner d N j + d (N + j)

/-- `H_j + Q ≤ 2^j Q`: the finite geometric tail. -/
theorem tail_bound {d : ℕ → PTm n} {Q : PTm n} (hd : ∀ i, Γ ⊢[PRAAx] le (d i) Q) (N : ℕ) :
    ∀ j, Γ ⊢[PRAAx] le (horner d N j + Q) (num (2 ^ j) * Q)
  | 0 => by
    show Γ ⊢[PRAAx] le (zero + Q) (num 1 * Q)
    ipra_le 0
  | j + 1 => by
    have ih := tail_bound hd N j
    have h := hd (N + j)
    show Γ ⊢[PRAAx] le (num 2 * horner d N j + d (N + j) + Q) (num (2 ^ (j + 1)) * Q)
    ipra_le 2 * sl ih + sl h using push_cast; ring

/-- `eq:coordinate-bound`: `2^{j−1−i} d_{N+i} ≤ H_j` for `i < j`. -/
theorem coord_bound (d : ℕ → PTm n) (N : ℕ) :
    ∀ j i, i < j → (Γ ⊢[PRAAx] le (num (2 ^ (j - 1 - i)) * d (N + i)) (horner d N j))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | j + 1, i, h => by
    show Γ ⊢[PRAAx] le (num (2 ^ (j + 1 - 1 - i)) * d (N + i)) (num 2 * horner d N j + d (N + j))
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hi | rfl
    · have ih := coord_bound d N j i hi
      obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - i - 1, by omega⟩
      rw [show i + 1 + m + 1 - 1 - i = m + 1 by omega]
      rw [show i + 1 + m - 1 - i = m by omega] at ih
      ipra_le 2 * sl ih + 𝔟 (d (N + (i + 1 + m))) using push_cast; ring
    · rw [show i + 1 - 1 - i = 0 by omega]
      ipra_le 2 * 𝔟 (horner d N i) using push_cast; ring

/-! ## Local-gap Urysohn separation -/

variable {a b a' b' d δ : PTm n}

/-- `δ ≤ a + b` and 1-Lipschitz `a`, `b` give `δ ≤ a' + b' + 2 d`. -/
theorem local_gap (ha : Γ ⊢[PRAAx] le a (a' + d)) (hb : Γ ⊢[PRAAx] le b (b' + d))
    (hδ : Γ ⊢[PRAAx] le δ (a + b)) : Γ ⊢[PRAAx] le δ (a' + b' + num 2 * d) := by
  ipra_le sl ha + sl hb + sl hδ

/-- `4 d ≤ δ` gives `δ ≤ 2 (a' + b')`. -/
theorem half_gap (ha : Γ ⊢[PRAAx] le a (a' + d)) (hb : Γ ⊢[PRAAx] le b (b' + d))
    (hδ : Γ ⊢[PRAAx] le δ (a + b)) (h4 : Γ ⊢[PRAAx] le (num 4 * d) δ) :
    Γ ⊢[PRAAx] le δ (num 2 * (a' + b')) := by
  have g := local_gap ha hb hδ
  ipra_le 2 * sl g + sl h4

/-- `prop:local-urysohn`, cleared: `δ a s' ≤ δ a' s + 2 s s' d` and `δ a' s ≤ δ a s' + 2 s s' d`. -/
theorem local_lipschitz (ha : Γ ⊢[PRAAx] le a (a' + d)) (ha' : Γ ⊢[PRAAx] le a' (a + d))
    (hb : Γ ⊢[PRAAx] le b (b' + d)) (hb' : Γ ⊢[PRAAx] le b' (b + d))
    (hδ : Γ ⊢[PRAAx] le δ (a + b)) (h4 : Γ ⊢[PRAAx] le (num 4 * d) δ) :
    (Γ ⊢[PRAAx] le (δ * (a * (a' + b'))) (δ * (a' * (a + b)) + num 2 * ((a + b) * (a' + b')) * d)) ∧
    (Γ ⊢[PRAAx] le (δ * (a' * (a + b))) (δ * (a * (a' + b')) + num 2 * ((a + b) * (a' + b')) * d)) := by
  have hu := numerator_upper ha hb'
  have hl := numerator_lower ha' hb
  have hh := half_gap ha hb hδ h4
  refine ⟨?_, ?_⟩
  · ipra_le 𝔟 δ * sl hu + (𝔟 a + 𝔟 b) * 𝔟 d * sl hh
  · ipra_le 𝔟 δ * sl hl + (𝔟 a + 𝔟 b) * 𝔟 d * sl hh

end LeanProofs.IPRA.Topology.MetricProducts
