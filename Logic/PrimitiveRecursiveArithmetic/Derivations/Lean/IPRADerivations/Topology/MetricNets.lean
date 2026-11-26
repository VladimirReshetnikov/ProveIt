import IPRADerivations.Topology.MetricProducts
import IPRADerivations.Foundations.FiniteObservations.MetricKernel

/-!
# Product nets, completion transport, image nets and finite Urysohn data

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/04_metric.tex`, the finite cores, cleared
for natural terms (distances and precisions as terms, denominators cleared):

* `thm:finite-metric-product` ("Finite products of explicit nets"): the maximum `join a b = b + (a ∸ b)` and
  its finite fold `joinL` (`d_max`), with `le_joinL` and `joinL_le` ("Every coordinate distance to the
  resulting tuple is at most `2^{-k}`, so their maximum is at most `2^{-k}`"); and the mixed-radix index of
  the selected tuple, `idx_lt`: digits `σ_i < M_i` give an index below the size `∏ M_i`;
* `thm:product-completion` ("Transport of supplied completion procedures"): `coord_cauchy`, "Product Cauchy
  data with modulus `m` furnish coordinate-`i` Cauchy data with modulus `k ↦ m(k + i + 1)`" from
  `d_i ≤ 2^{i+1} D`; and `completion_rate`, the partial sum and the tail each at most `2^{-k-2}` give
  `D(x_n, z) ≤ 2^{-k-1}`;
* `prop:image-nets` ("Uniform images preserve nets"), `image_net`: the modulus applied to the selected net
  point;
* `cor:finite-metric-urysohn` ("Finite rational metric sets"): `meet_shift` and `min_shift`, "Each
  distance-to-a-point function is `1`-Lipschitz; taking a finite minimum preserves that bound", and
  `urysohn_gap`, "`δ ≤ d(p, q) ≤ d(p, x) + d(x, q) = a(x) + b(x)`".
-/

namespace LeanProofs.IPRA.Topology.MetricNets

open_ipra
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right meet_le_left
  meet_le_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The maximum metric of a finite product -/

/-- The maximum of two terms. -/
def join (a b : PTm n) : PTm n := b + monus a b

theorem le_join_left (a b : PTm n) : Γ ⊢[PRAAx] le a (join a b) := by
  refine .orE (le_total a b) ?_ ?_
  · have h : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    show (le a b :: Γ) ⊢[PRAAx] le a (b + monus a b)
    ipra_le sl h + 𝔟 (monus a b)
  · have h : (le b a :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
    have e := natEq (eq_add_of_le h)
    show (le b a :: Γ) ⊢[PRAAx] le a (b + monus a b)
    ipra_le 0 with e

theorem le_join_right (a b : PTm n) : Γ ⊢[PRAAx] le b (join a b) := by
  show Γ ⊢[PRAAx] le b (b + monus a b)
  ipra_le 𝔟 (monus a b)

theorem join_le {a b c : PTm n} (ha : Γ ⊢[PRAAx] le a c) (hb : Γ ⊢[PRAAx] le b c) :
    Γ ⊢[PRAAx] le (join a b) c := by
  refine .orE (le_total a b) ?_ ?_
  · have h0 : (le a b :: Γ) ⊢[PRAAx] monus a b ≐ zero := Prf.hyp0
    have e := natEq h0
    have hb' := hb.wk (ψ := le a b)
    show (le a b :: Γ) ⊢[PRAAx] le (b + monus a b) c
    ipra_le sl hb' with e
  · have h : (le b a :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
    have e := natEq (eq_add_of_le h)
    have ha' := ha.wk (ψ := le b a)
    show (le b a :: Γ) ⊢[PRAAx] le (b + monus a b) c
    ipra_le sl ha' with e

/-- The maximum of a finite list (`d_max` of the coordinate distances). -/
def joinL : List (PTm n) → PTm n
  | [] => zero
  | a :: L => join a (joinL L)

/-- Every coordinate distance is at most the maximum. -/
theorem le_joinL : (L : List (PTm n)) → (a : PTm n) → a ∈ L → (Γ ⊢[PRAAx] le a (joinL L))
  | [], _, h => absurd h (by simp)
  | b :: L, a, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_join_left _ _
    · exact le_trans (le_joinL L a h') (le_join_right _ _)

/-- If every coordinate distance is at most `e`, so is their maximum. -/
theorem joinL_le {e : PTm n} : (L : List (PTm n)) → (∀ a ∈ L, Γ ⊢[PRAAx] le a e) →
    (Γ ⊢[PRAAx] le (joinL L) e)
  | [], _ => by
    show Γ ⊢[PRAAx] le zero e
    ipra_le 𝔟 e
  | a :: L, h => join_le (h a (List.mem_cons_self ..)) (joinL_le L fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The mixed-radix index of a tuple of digits `(σ_i, M_i)`. -/
def idx : List (PTm n × PTm n) → PTm n
  | [] => zero
  | p :: L => p.1 + p.2 * idx L

/-- The size `∏ M_i` of the product net. -/
def size : List (PTm n × PTm n) → PTm n
  | [] => succ zero
  | p :: L => p.2 * size L

/-- Digits `σ_i < M_i` give an index below the size of the product net. -/
theorem idx_lt : (L : List (PTm n × PTm n)) → (∀ p ∈ L, Γ ⊢[PRAAx] le (succ p.1) p.2) →
    (Γ ⊢[PRAAx] le (succ (idx L)) (size L))
  | [], _ => le_refl _
  | p :: L, h => by
    have ih := idx_lt L fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hs : Γ ⊢[PRAAx] le (succ p.1) p.2 := h p (List.mem_cons_self ..)
    show Γ ⊢[PRAAx] le (succ (p.1 + p.2 * idx L)) (p.2 * size L)
    ipra_le 𝔟 p.2 * sl ih + sl hs

/-! ## Completion transport -/

/-- Coordinate Cauchy data from product Cauchy data: `d_i ≤ 2^{i+1} D` and `2^{k+i+1} D ≤ U` give
`2^k d_i ≤ U`. -/
theorem coord_cauchy {d D U : PTm n} (i k : ℕ) (hc : Γ ⊢[PRAAx] le d (num (2 ^ (i + 1)) * D))
    (hD : Γ ⊢[PRAAx] le (num (2 ^ (k + i + 1)) * D) U) : Γ ⊢[PRAAx] le (num (2 ^ k) * d) U := by
  ipra_le 2 ^ k * sl hc + sl hD using push_cast; ring

/-- The product convergence rate: partial sum and tail each at most `E` give `D(x_n, z) ≤ 2E`. -/
theorem completion_rate {Dn P T E : PTm n} (hD : Γ ⊢[PRAAx] le Dn (P + T)) (hP : Γ ⊢[PRAAx] le P E)
    (hT : Γ ⊢[PRAAx] le T E) : Γ ⊢[PRAAx] le Dn (num 2 * E) := by
  ipra_le sl hD + sl hP + sl hT

/-! ## Images of nets -/

/-- The modulus applied to the selected net point: `d(x, p) ≤ δ → d(f x, f p) ≤ ε` and `d(x, p) ≤ δ`. -/
theorem image_net {dxp δ dfx ε : PTm n} (hmod : Γ ⊢[PRAAx] le dxp δ ⟶ le dfx ε) (hnet : Γ ⊢[PRAAx] le dxp δ) :
    Γ ⊢[PRAAx] le dfx ε :=
  .impE hmod hnet

/-! ## Finite rational metric sets -/

/-- A minimum of two `1`-Lipschitz quantities is `1`-Lipschitz. -/
theorem meet_shift {a b a' b' D : PTm n} (ha : Γ ⊢[PRAAx] le a (D + a')) (hb : Γ ⊢[PRAAx] le b (D + b')) :
    Γ ⊢[PRAAx] le (meet a b) (D + meet a' b') := by
  refine .orE (le_total a' b') ?_ ?_
  · have h : (le a' b' :: Γ) ⊢[PRAAx] le a' b' := Prf.hyp0
    have hm : (le a' b' :: Γ) ⊢[PRAAx] le (meet a b) a := meet_le_left a b
    have ha' := ha.wk (ψ := le a' b')
    ipra_le sl hm + sl ha' with natEq (meet_left h)
  · have h : (le b' a' :: Γ) ⊢[PRAAx] le b' a' := Prf.hyp0
    have hm : (le b' a' :: Γ) ⊢[PRAAx] le (meet a b) b := meet_le_right a b
    have hb' := hb.wk (ψ := le b' a')
    ipra_le sl hm + sl hb' with natEq (meet_right h)

/-- The minimum of the first components (`a(x) = min_p d(x, p)`). -/
def minX : List (PTm n × PTm n) → PTm n
  | [] => zero
  | [p] => p.1
  | p :: q :: L => meet p.1 (minX (q :: L))

/-- The minimum of the second components (`a(y) = min_p d(y, p)`). -/
def minY : List (PTm n × PTm n) → PTm n
  | [] => zero
  | [p] => p.2
  | p :: q :: L => meet p.2 (minY (q :: L))

/-- "taking a finite minimum preserves that bound": `d(x, p) ≤ D + d(y, p)` for every `p` gives
`a(x) ≤ D + a(y)`. -/
theorem min_shift {D : PTm n} : (L : List (PTm n × PTm n)) → (∀ p ∈ L, Γ ⊢[PRAAx] le p.1 (D + p.2)) →
    (Γ ⊢[PRAAx] le (minX L) (D + minY L))
  | [], _ => by
    show Γ ⊢[PRAAx] le zero (D + zero)
    ipra_le 𝔟 D
  | [p], h => h p (List.mem_cons_self ..)
  | p :: q :: L, h =>
    meet_shift (h p (List.mem_cons_self ..)) (min_shift (q :: L) fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- The gap of the finite Urysohn data: `δ ≤ d(p, q) ≤ a(x) + b(x)` at minimizing `p`, `q`. -/
theorem urysohn_gap {δ dpq a b : PTm n} (hδ : Γ ⊢[PRAAx] le δ dpq) (htri : Γ ⊢[PRAAx] le dpq (a + b)) :
    Γ ⊢[PRAAx] le δ (a + b) := by
  ipra_le sl hδ + sl htri

end LeanProofs.IPRA.Topology.MetricNets
