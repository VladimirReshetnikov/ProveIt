import IPRADerivations.Topology.BarycentricMesh
import IPRADerivations.Core.CertificateTactics

/-!
# The exact Euler polygons: norm bounds, stability and segment clearance

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Lemmas
`lem:ode-polybound`, `lem:ode-stability` and `lem:ode-clearance`, as iPRA derivations (norms of the signed
Euler array as natural terms cleared of denominators, with the triangle and product bounds of the vector norm
supplied as derived inequalities; the clearance polynomial as integer terms):

* `euler_norm`, `euler_bound` (`lem:ode-polybound`): "Induction in `eq:exact-euler` gives
  `‖X_{n,j}‖ ≤ (1 + K/n)^j U ≤ G U`": from `n ‖X_{j+1}‖ ≤ (n + K) ‖X_j‖`, `n^j ‖X_j‖ ≤ (n + K)^j U`, and
  `‖X_j‖ ≤ G U` when `(n + K)^j ≤ G n^j` (`lem:ode-growth`, `Analysis/OdeGrowth`);
* `interp_bound`: "An interpolated value is a convex combination of its two endpoint values, so it has the
  same bound";
* `acc`, `acc_le`, `stability_coeff`, `stability_bound` (`lem:ode-stability`): "the norm error satisfies
  `e_{j+1} ≤ (1 + K/n) e_j + η G U/n`, `e_0 = 0`. Iteration gives `e_j ≤ G (η G U)`": with `c = η G U`,
  `n^{j+1} e_j ≤ a_j c` for the numerals `a_0 = 0`, `a_{j+1} = (n + K) a_j + n^{j+1}`, and `a_j ≤ j (n + K)^j`;
  (the initial-data stability `‖X_n(v) − X_n(w)‖ ≤ G ‖v − w‖` is `euler_bound` for the difference array);
* `clear_mid`, `clear_left`, `clear_right` (`lem:ode-clearance`): for the distance polynomial
  `f(t) = A + 2Dt + Et²` at `t = p/q`, homogenized as `F = A q² + 2D p q + E p²`: "completing the square gives
  `f(t) − f(−D/E) = E (t + D/E)² ≥ 0`", "`f(t) − f(0) = t(2D + Et) ≥ 0`" for `D ≥ 0`, and
  "`f(t) − f(1) = (t − 1)(2D + E(t + 1)) ≥ 0`" for `D ≤ −E`, `t ≤ 1`.
-/

namespace LeanProofs.IPRA.Analysis.EulerPolygon

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.BarycentricMesh (mul_cancel_le num_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The norm of the Euler array -/

/-- `N^j ‖X_j‖ ≤ (N + K)^j U`. -/
theorem euler_norm (x : ℕ → PTm n) (N K : ℕ) (U : PTm n) (h0 : Γ ⊢[PRAAx] le (x 0) U)
    (hstep : ∀ j, Γ ⊢[PRAAx] le (num N * x (j + 1)) (num (N + K) * x j)) (j : ℕ) :
    Γ ⊢[PRAAx] le (num (N ^ j) * x j) (num ((N + K) ^ j) * U) := by
  induction j with
  | zero => ipra_le sl h0 using push_cast; ring
  | succ j ih =>
    have hj := hstep j
    ipra_le (N : Groth (Q Γ)) ^ j * sl hj + ((N + K : ℕ) : Groth (Q Γ)) * sl ih using push_cast; ring

/-- `‖X_j‖ ≤ G U` when `(N + K)^j ≤ G N^j`. -/
theorem euler_bound (x : ℕ → PTm n) {N K G : ℕ} (hN : 1 ≤ N) (U : PTm n) (h0 : Γ ⊢[PRAAx] le (x 0) U)
    (hstep : ∀ j, Γ ⊢[PRAAx] le (num N * x (j + 1)) (num (N + K) * x j)) (j : ℕ)
    (hG : (N + K) ^ j ≤ G * N ^ j) : Γ ⊢[PRAAx] le (x j) (num G * U) := by
  have h := euler_norm x N K U h0 hstep j
  obtain ⟨c, hc⟩ : ∃ c, G * N ^ j = (N + K) ^ j + c := ⟨_, (Nat.add_sub_cancel' hG).symm⟩
  have hc' := congrArg (Nat.cast : ℕ → Groth (Q Γ)) hc
  push_cast at hc'
  refine mul_cancel_le (num_pos (Nat.one_le_pow _ _ hN)) (c := num (N ^ j)) ?_
  ipra_le sl h + (c : Groth (Q Γ)) * 𝔟 U using (push_cast; linear_combination Groth.ι (Q.mk Γ U) * hc')

/-- An interpolated value has the bound of its endpoints: `(r + r') ‖X(t)‖ ≤ r' ‖X_j‖ + r ‖X_{j+1}‖`. -/
theorem interp_bound {r r' xt a b Y : PTm n} (hx : Γ ⊢[PRAAx] le ((r + r') * xt) (r' * a + r * b))
    (ha : Γ ⊢[PRAAx] le a Y) (hb : Γ ⊢[PRAAx] le b Y) : Γ ⊢[PRAAx] le ((r + r') * xt) ((r + r') * Y) := by
  ipra_le sl hx + 𝔟 r' * sl ha + 𝔟 r * sl hb

/-! ## Coefficient stability -/

/-- `a_0 = 0`, `a_{j+1} = (N + K) a_j + N^{j+1}`. -/
def acc (N K : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (N + K) * acc N K j + N ^ (j + 1)

theorem acc_le (N K : ℕ) : ∀ j, acc N K j ≤ j * (N + K) ^ j
  | 0 => Nat.le_refl _
  | j + 1 => by
    have ih := acc_le N K j
    have hp : N ^ (j + 1) ≤ (N + K) ^ (j + 1) := Nat.pow_le_pow_left (Nat.le_add_right N K) _
    calc (N + K) * acc N K j + N ^ (j + 1) ≤ (N + K) * (j * (N + K) ^ j) + (N + K) ^ (j + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ ih) hp
      _ = (j + 1) * (N + K) ^ (j + 1) := by ring

/-- `N^{j+1} e_j ≤ a_j c` from `e_0 = 0` and `N e_{j+1} ≤ (N + K) e_j + c`. -/
theorem stability_coeff (e : ℕ → PTm n) (N K : ℕ) (c : PTm n) (h0 : Γ ⊢[PRAAx] le (e 0) zero)
    (hstep : ∀ j, Γ ⊢[PRAAx] le (num N * e (j + 1)) (num (N + K) * e j + c)) (j : ℕ) :
    Γ ⊢[PRAAx] le (num (N ^ (j + 1)) * e j) (num (acc N K j) * c) := by
  induction j with
  | zero =>
    show Γ ⊢[PRAAx] le (num (N ^ (0 + 1)) * e 0) (num 0 * c)
    ipra_le (N : Groth (Q Γ)) * sl h0 using push_cast; ring
  | succ j ih =>
    have hj := hstep j
    show Γ ⊢[PRAAx] le (num (N ^ (j + 1 + 1)) * e (j + 1)) (num ((N + K) * acc N K j + N ^ (j + 1)) * c)
    ipra_le (N : Groth (Q Γ)) ^ (j + 1) * sl hj + ((N + K : ℕ) : Groth (Q Γ)) * sl ih using push_cast; ring

/-- `e_j ≤ G c` when `a_j ≤ G N^{j+1}` (for `j ≤ N` and `(N + K)^j ≤ G N^j`, by `acc_le`). -/
theorem stability_bound (e : ℕ → PTm n) {N K G : ℕ} (hN : 1 ≤ N) (c : PTm n)
    (h0 : Γ ⊢[PRAAx] le (e 0) zero)
    (hstep : ∀ j, Γ ⊢[PRAAx] le (num N * e (j + 1)) (num (N + K) * e j + c)) (j : ℕ)
    (hG : acc N K j ≤ G * N ^ (j + 1)) : Γ ⊢[PRAAx] le (e j) (num G * c) := by
  have h := stability_coeff e N K c h0 hstep j
  obtain ⟨d, hd⟩ : ∃ d, G * N ^ (j + 1) = acc N K j + d := ⟨_, (Nat.add_sub_cancel' hG).symm⟩
  have hd' := congrArg (Nat.cast : ℕ → Groth (Q Γ)) hd
  push_cast at hd'
  refine mul_cancel_le (num_pos (Nat.one_le_pow _ _ hN)) (c := num (N ^ (j + 1))) ?_
  ipra_le sl h + (d : Groth (Q Γ)) * 𝔟 c using (push_cast; linear_combination Groth.ι (Q.mk Γ c) * hd')

/-! ## Segment clearance -/

/-- Completing the square: `E F − (E A − D²) q² = (E p + D q)²`, so `E F ≥ (E A − D²) q²`. -/
theorem clear_mid (A D E p q : ZT n) :
    Γ ⊢[PRAAx] zle ((E * A - D * D) * (q * q))
      (E * (A * (q * q) + ZT.natLit 2 * D * (p * q) + E * (p * p))) := by
  ipra_zle (ZT.toZ Γ (E * p + D * q) ^ 2)

/-- The minimum at the left end: `D ≥ 0` gives `F ≥ A q²` for `p, q ≥ 0`. -/
theorem clear_left {A D E p q : ZT n} (hD : Γ ⊢[PRAAx] zle (ZT.natLit 0) D)
    (hE : Γ ⊢[PRAAx] zle (ZT.natLit 0) E) (hp : Γ ⊢[PRAAx] zle (ZT.natLit 0) p)
    (hq : Γ ⊢[PRAAx] zle (ZT.natLit 0) q) :
    Γ ⊢[PRAAx] zle (A * (q * q)) (A * (q * q) + ZT.natLit 2 * D * (p * q) + E * (p * p)) := by
  ipra_zle 2 * zsl hD * (zsl hp * zsl hq) + zsl hE * (zsl hp * zsl hp)

/-- The minimum at the right end: `D ≤ −E` gives `F(p, q) ≥ F(q, q)` for `p ≤ q`, `q ≥ 0`. -/
theorem clear_right {A D E p q : ZT n} (hDE : Γ ⊢[PRAAx] zle D (-E)) (hE : Γ ⊢[PRAAx] zle (ZT.natLit 0) E)
    (hpq : Γ ⊢[PRAAx] zle p q) (hq : Γ ⊢[PRAAx] zle (ZT.natLit 0) q) :
    Γ ⊢[PRAAx] zle ((A + ZT.natLit 2 * D + E) * (q * q))
      (A * (q * q) + ZT.natLit 2 * D * (p * q) + E * (p * p)) := by
  ipra_zle zsl hpq * (2 * zsl hDE * zsl hq + zsl hE * zsl hpq)

end LeanProofs.IPRA.Analysis.EulerPolygon
