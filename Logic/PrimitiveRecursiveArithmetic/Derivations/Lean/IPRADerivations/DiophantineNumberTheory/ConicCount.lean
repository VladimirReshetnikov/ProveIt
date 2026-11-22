import IPRADerivations.DiophantineNumberTheory.AperyWronskian

/-!
# The counting estimates of a pointed conic

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:conic-count`:
`N_q(B) ≤ 4KB` (`B ≥ 1`) and `B ≤ 16A N_q(B)` (`B ≥ A`). The proof's arithmetic, with the counts as natural
numbers supplied by the bijection of `thm:conic-param` and the height bounds of `thm:conic-height`:

* `canonical_pairs`: "The number of all nonzero integer pairs in the box `[−S, S]²` is `4S² + 4S`. Exactly one
  element in each pair `{v, −v}` has its first nonzero coordinate positive. Thus there are at most `2S² + 2S ≤ 4S²`
  canonical primitive pairs": `(4S² + 4S) = 2(2S² + 2S)` and `2S² + 2S ≤ 4S²` for `S ≥ 1`;
* `count_upper`: with `S = ⌊√(KB)⌋ ≥ 1` (`S² ≤ KB`) and `N_q ≤ 2S² + 2S`, `N_q ≤ 4KB`;
* `count_lower`: "Maximality of `N` gives `B < A(N+1)² ≤ 4AN² ≤ 16A N_q(B)`": from `B < A(N+1)²`, `N ≥ 1` and
  `N² ≤ 4 N_q` (`lem:conic-coprime-count`, `4G(N) ≥ N²`, with `G(N) ≤ N_q`), `B ≤ 16 A N_q`;
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The canonical pairs of the box: half of `4S² + 4S`, and at most `4S²` for `S ≥ 1`. -/
theorem canonical_pairs {S : PTm n} (hS : Γ ⊢[PRAAx] le one S) :
    (Γ ⊢[PRAAx] num 4 * S * S + num 4 * S ≐ num 2 * (num 2 * S * S + num 2 * S)) ∧
    (Γ ⊢[PRAAx] le (num 2 * S * S + num 2 * S) (num 4 * S * S)) := by
  refine ⟨by apply deriveNat; ipra_simps; ring, ?_⟩
  ipra_le 2 * 𝔟 S * sl hS

/-- `N_q ≤ 2S² + 2S`, `S² ≤ KB`, `S ≥ 1` give `N_q ≤ 4KB`. -/
theorem count_upper {Nq S K B : PTm n} (hS : Γ ⊢[PRAAx] le one S) (hSq : Γ ⊢[PRAAx] le (S * S) (K * B))
    (hN : Γ ⊢[PRAAx] le Nq (num 2 * S * S + num 2 * S)) : Γ ⊢[PRAAx] le Nq (num 4 * K * B) := by
  ipra_le sl hN + 2 * 𝔟 S * sl hS + 4 * sl hSq

/-- `B < A(N+1)²`, `N ≥ 1`, `N² ≤ 4 N_q` give `B ≤ 16 A N_q`. -/
theorem count_lower {B A N Nq : PTm n} (hN : Γ ⊢[PRAAx] le one N)
    (hmax : Γ ⊢[PRAAx] lt B (A * (succ N * succ N))) (hG : Γ ⊢[PRAAx] le (N * N) (num 4 * Nq)) :
    Γ ⊢[PRAAx] le B (num 16 * A * Nq) := by
  have hm : Γ ⊢[PRAAx] le (succ B) (A * (succ N * succ N)) := hmax
  -- `(N+1)² ≤ 4N²` for `N ≥ 1`
  ipra_le sl hm + 1 + 𝔟 A * (3 * 𝔟 N + 1) * sl hN + 4 * 𝔟 A * sl hG

end LeanProofs.IPRA.DiophantineNumberTheory.ConicCount
