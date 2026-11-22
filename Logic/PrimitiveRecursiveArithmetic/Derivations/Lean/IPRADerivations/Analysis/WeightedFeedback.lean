import IPRADerivations.Analysis.WeightedRowContraction
import IPRADerivations.Probability.ClipLaws
import IPRADerivations.Core.Gcd

/-!
# Vector-valued weighted feedback certificates

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/03_feedback.tex`, Section "Cyclic
quantitative contracts from finite weighted certificates", for a fixed dimension `m`, natural entries
`a_{ij}`, natural weights `w_i` and a map `T` on vectors of terms with

* the certificate `2 ∑_j a_{ij} w_j ≤ w_i` (`eq:half-certificate`), domain preservation (`eq:T-domain`) and the
  gain contract `|T_i x − T_i y| ≤ ∑_j a_{ij} |x_j − y_j|` on the domain (`eq:T-gain`), bundled as `Cert`:

* `contract_scaled` (`lem:weighted-contraction`, "if `|x_j − y_j| ≤ r w_j` for every `j` … then
  `|T_i(x) − T_i(y)| ≤ (r/2) w_i`"), in cleared form with a multiplier `s`:
  `s |x_j − y_j| ≤ r w_j` for all `j` gives `2 s |T_i x − T_i y| ≤ r w_i`;
* `orbit_dom`, `orbit_inc` (`thm:feedback-name`, `eq:feedback-inc`): the orbit `x₀ = c`, `x_{k+1} = T x_k` stays
  in the domain and `2^k |x_{k+1,i} − x_{k,i}| ≤ B w_i`;
* `orbit_tail` (`eq:feedback-tail`, cleared): `2^{k+j} |x_{k+j,i} − x_{k,i}| + 2 B w_i ≤ 2^{j+1} B w_i`;
* `name_bound` (the primitive-recursive name `X(k) = x_{k+c₀}` with `2^{c₀} ≥ 2BW`):
  `2^k |X_i(ℓ) − X_i(k)| ≤ 1` for `k ≤ ℓ`, after cancelling the power of two (`cancel_pow`);
* `residual_bound` ("`T(X(k)) − X(k)` tends to zero with the explicit bound `B 2^{−(k+c₀)} w_i`");
* `box_invariant` ("An invariant box can itself be supplied by a finite certificate"): `|x_j − c_j| ≤ R w_j`
  and `2 |T_i c − c_i| ≤ R w_i` give `|T_i x − c_i| ≤ R w_i`.
-/

namespace LeanProofs.IPRA.Analysis.WeightedFeedback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le)
open LeanProofs.IPRA.Probability.BayesEvents (wsum_mul wsum_zero)
open LeanProofs.IPRA.Analysis.WeightedRowContraction (row_domination half_contract_row)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ClipLaws (ad_triangle)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The half certificate, domain preservation and the gain contract. -/
structure Cert (Γ : List (Fm PTm n)) (a : Fin m → Fin m → PTm n) (w : Fin m → PTm n)
    (T : (Fin m → PTm n) → Fin m → PTm n) (D : (Fin m → PTm n) → Prop) : Prop where
  half : ∀ i, Prf PRAAx Γ (le (two * wsum (a i) w (List.finRange m)) (w i))
  dom : ∀ x, D x → D (T x)
  gain : ∀ x y, D x → D y → ∀ i,
    Prf PRAAx Γ (le (ad (T x i) (T y i)) (wsum (a i) (fun j => ad (x j) (y j)) (List.finRange m)))

variable {a : Fin m → Fin m → PTm n} {w : Fin m → PTm n} {T : (Fin m → PTm n) → Fin m → PTm n}
  {D : (Fin m → PTm n) → Prop}

/-- `lem:weighted-contraction`, cleared: `s |x_j − y_j| ≤ r w_j` for all `j` gives `2 s |T_i x − T_i y| ≤ r w_i`. -/
theorem contract_scaled (C : Cert Γ a w T D) {x y : Fin m → PTm n} (hx : D x) (hy : D y) {s r : PTm n}
    (h : ∀ j, Γ ⊢[PRAAx] le (s * ad (x j) (y j)) (r * w j)) (i : Fin m) :
    Γ ⊢[PRAAx] le (two * (s * ad (T x i) (T y i))) (r * w i) := by
  have g := C.gain x y hx hy i
  have e := natEq (wsum_mul (Γ := Γ) (a i) (fun j => ad (x j) (y j)) s (List.finRange m))
  have hg : Γ ⊢[PRAAx] le (s * ad (T x i) (T y i))
      (wsum (a i) (fun j => s * ad (x j) (y j)) (List.finRange m)) := by
    ipra_le 𝔟 s * sl g with e
  exact half_contract_row (a i) w (fun j => s * ad (x j) (y j)) (List.finRange m) (fun j _ => h j) (C.half i) hg

/-- The orbit `x₀ = c`, `x_{k+1} = T x_k`. -/
def orbit (T : (Fin m → PTm n) → Fin m → PTm n) (c : Fin m → PTm n) : ℕ → Fin m → PTm n
  | 0 => c
  | k + 1 => T (orbit T c k)

theorem orbit_dom (C : Cert Γ a w T D) {c : Fin m → PTm n} (hc : D c) : ∀ k, D (orbit T c k)
  | 0 => hc
  | k + 1 => C.dom _ (orbit_dom C hc k)

/-- `eq:feedback-inc`: `2^k |x_{k+1,i} − x_{k,i}| ≤ B w_i`. -/
theorem orbit_inc (C : Cert Γ a w T D) {c : Fin m → PTm n} (hc : D c) {B : PTm n}
    (hB : ∀ i, Γ ⊢[PRAAx] le (ad (T c i) (c i)) (B * w i)) :
    ∀ k i, Γ ⊢[PRAAx] le (num (2 ^ k) * ad (orbit T c (k + 1) i) (orbit T c k i)) (B * w i)
  | 0, i => by
    have h := hB i
    show Γ ⊢[PRAAx] le (num 1 * ad (T c i) (c i)) (B * w i)
    ipra_le sl h
  | k + 1, i => by
    have h := contract_scaled C (orbit_dom C hc (k + 1)) (orbit_dom C hc k) (s := num (2 ^ k)) (r := B)
      (fun j => orbit_inc C hc hB k j) i
    show Γ ⊢[PRAAx] le (num (2 ^ (k + 1)) * ad (T (orbit T c (k + 1)) i) (T (orbit T c k) i)) (B * w i)
    ipra_le sl h using push_cast; ring

/-- `eq:feedback-tail`, cleared: `2^{k+j} |x_{k+j,i} − x_{k,i}| + 2 B w_i ≤ 2^{j+1} B w_i`. -/
theorem orbit_tail (C : Cert Γ a w T D) {c : Fin m → PTm n} (hc : D c) {B : PTm n}
    (hB : ∀ i, Γ ⊢[PRAAx] le (ad (T c i) (c i)) (B * w i)) (k : ℕ) :
    ∀ j i, Γ ⊢[PRAAx] le (num (2 ^ (k + j)) * ad (orbit T c (k + j) i) (orbit T c k i) + num 2 * (B * w i))
      (num (2 ^ (j + 1)) * (B * w i))
  | 0, i => by
    have h0 : Γ ⊢[PRAAx] le (ad (orbit T c k i) (orbit T c k i)) zero :=
      ad_le_of (by ipra_le 0) (by ipra_le 0)
    show Γ ⊢[PRAAx] le (num (2 ^ k) * ad (orbit T c k i) (orbit T c k i) + num 2 * (B * w i))
      (num (2 ^ 1) * (B * w i))
    ipra_le 2 ^ k * sl h0 using push_cast; ring
  | j + 1, i => by
    have tri := ad_triangle (Γ := Γ) (orbit T c (k + j + 1) i) (orbit T c (k + j) i) (orbit T c k i)
    have inc := orbit_inc C hc hB (k + j) i
    have ih := orbit_tail C hc hB k j i
    show Γ ⊢[PRAAx] le (num (2 ^ (k + j + 1)) * ad (orbit T c (k + j + 1) i) (orbit T c k i) + num 2 * (B * w i))
      (num (2 ^ (j + 1 + 1)) * (B * w i))
    ipra_le 2 ^ (k + j + 1) * sl tri + 2 * sl inc + 2 * sl ih using push_cast; ring

/-- Cancelling a power of two. -/
theorem cancel_pow {x y : PTm n} : ∀ p, (Γ ⊢[PRAAx] le (num (2 ^ p) * x) (num (2 ^ p) * y)) →
    (Γ ⊢[PRAAx] le x y)
  | 0, h => by
    show Γ ⊢[PRAAx] le x y
    have h' : Γ ⊢[PRAAx] le (num 1 * x) (num 1 * y) := h
    ipra_le sl h'
  | p + 1, h => by
    have h' : Γ ⊢[PRAAx] le (num (2 ^ p) * (num 2 * x)) (num (2 ^ p) * (num 2 * y)) := by
      ipra_le sl h using push_cast; ring
    have h2 : Γ ⊢[PRAAx] le (succ (num 1) * x) (succ (num 1) * y) := cancel_pow p h'
    exact mul_le_cancel h2

/-- The name `X(k) = x_{k+c₀}`: `2^k |X_i(ℓ) − X_i(k)| ≤ 1` for `k ≤ ℓ`, when `2 B W ≤ 2^{c₀}`, `w_i ≤ W`. -/
theorem name_bound (C : Cert Γ a w T D) {c : Fin m → PTm n} (hc : D c) {B W : PTm n}
    (hB : ∀ i, Γ ⊢[PRAAx] le (ad (T c i) (c i)) (B * w i)) (hw : ∀ i, Γ ⊢[PRAAx] le (w i) W) {c₀ : ℕ}
    (hc₀ : Γ ⊢[PRAAx] le (num 2 * (B * W)) (num (2 ^ c₀))) {k ℓ : ℕ} (hkl : k ≤ ℓ) (i : Fin m) :
    Γ ⊢[PRAAx] le (num (2 ^ k) * ad (orbit T c (ℓ + c₀) i) (orbit T c (k + c₀) i)) (num 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = k + j := ⟨ℓ - k, by omega⟩
  have t := orbit_tail C hc hB (k + c₀) j i
  rw [show k + c₀ + j = k + j + c₀ by omega] at t
  have hwi := hw i
  have hBw : Γ ⊢[PRAAx] le (B * w i) (B * W) := by ipra_le 𝔟 B * sl hwi
  refine cancel_pow (j + c₀) ?_
  have : Γ ⊢[PRAAx] le (num (2 ^ (j + c₀)) * (num (2 ^ k) * ad (orbit T c (k + j + c₀) i) (orbit T c (k + c₀) i)))
      (num (2 ^ (j + c₀)) * num 1) := by
    ipra_le sl t + 2 ^ j * sl hc₀ + 2 * 2 ^ j * sl hBw + 2 * 𝔟 B * 𝔟 (w i) using push_cast; ring
  exact this

/-- The residual of the name: `2^{k+c₀} |T_i(X(k)) − X_i(k)| ≤ B w_i`. -/
theorem residual_bound (C : Cert Γ a w T D) {c : Fin m → PTm n} (hc : D c) {B : PTm n}
    (hB : ∀ i, Γ ⊢[PRAAx] le (ad (T c i) (c i)) (B * w i)) (k c₀ : ℕ) (i : Fin m) :
    Γ ⊢[PRAAx] le (num (2 ^ (k + c₀)) * ad (T (orbit T c (k + c₀)) i) (orbit T c (k + c₀) i)) (B * w i) :=
  orbit_inc C hc hB (k + c₀) i

/-- The invariant box: `|x_j − c_j| ≤ R w_j` for all `j` and `2 |T_i c − c_i| ≤ R w_i` give
`|T_i x − c_i| ≤ R w_i`. -/
theorem box_invariant (C : Cert Γ a w T D) {x c : Fin m → PTm n} (hx : D x) (hc : D c) {R : PTm n}
    (hbox : ∀ j, Γ ⊢[PRAAx] le (ad (x j) (c j)) (R * w j))
    (hcen : ∀ i, Γ ⊢[PRAAx] le (two * ad (T c i) (c i)) (R * w i)) (i : Fin m) :
    Γ ⊢[PRAAx] le (ad (T x i) (c i)) (R * w i) := by
  have hc' := contract_scaled C hx hc (s := num 1) (r := R) (fun j => by have := hbox j; ipra_le sl this) i
  have tri := ad_triangle (Γ := Γ) (T x i) (T c i) (c i)
  have hci := hcen i
  have two_le : Γ ⊢[PRAAx] le (two * ad (T x i) (c i)) (two * (R * w i)) := by
    ipra_le sl hc' + sl hci + 2 * sl tri
  exact mul_le_cancel (d' := one) two_le

end LeanProofs.IPRA.Analysis.WeightedFeedback
