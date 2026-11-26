import IPRADerivations.AnalyticNumberTheory.PNTThresholds
import IPRADerivations.Core.Header

/-!
# The arithmetic of one finite contraction (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:one-step` and
§"Integer thresholds and the modulus". The integer parts of the step, cleared of denominators
(`q = p + 1`, `H̄ = 1024q`, `D = 2^{20}q³`, `S = 2^{18}`, `T_j` as in `PNTThresholds`):

* `threshold_hbar`, `threshold_D` ("putting `s = log P_j` and `t = log x`, (con:recurrence) bounds both
  `8(s + H̄)` and `D(8s + S)` from above, with a spare unit"): `s ≤ 2T_j` gives `8(s + H̄) + 1 ≤ T_{j+1}` and
  `D(8s + S) + 1 ≤ T_{j+1}` — the step thresholds `con:step-threshold` at every `t ≥ T_{j+1}`;
* `block_count` ("`b ≥ (t/2 − s)/H − 1 ≥ 3t/(8H) − 1 ≥ t/(4H) ≥ t/(4H̄)`. Here `s ≤ t/8` and
  `t ≥ 8H̄ ≥ 8H` were used"): `8s ≤ t`, `8H̄ ≤ t`, `H ≤ H̄` give `2tH + 8H̄s + 8H̄H ≤ 4H̄t`, i.e.
  `(t/2 − s)/H − 1 ≥ t/(4H̄)`;
* `delta_identity` ("`a − 1/(4H̄ · 64q²) … = a − 4δ`"): `4 · (4H̄ · 64q²) = D`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PNTOneStep

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds (Dq Tt T_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `s ≤ 2T_j` gives `8(s + H̄) + 1 ≤ T_{j+1}`. -/
theorem threshold_hbar {j p s : PTm n} (hs : Γ ⊢[PRAAx] le s (num 2 * Tt j p)) :
    Γ ⊢[PRAAx] le (succ (num 8 * (s + num 1024 * succ p))) (Tt (succ j) p) := by
  have e := natEq (T_succ (Γ := Γ) j p)
  ipra_le 8 * sl hs + 8192 * (𝔞 p + 1) +
      1048576 * (𝔞 p + 1) ^ 3 * (16 * 𝔞 (Tt j p) + 262144) with e

/-- `s ≤ 2T_j` gives `D(8s + S) + 1 ≤ T_{j+1}`. -/
theorem threshold_D {j p s : PTm n} (hs : Γ ⊢[PRAAx] le s (num 2 * Tt j p)) :
    Γ ⊢[PRAAx] le (succ (Dq p * (num 8 * s + num 262144))) (Tt (succ j) p) := by
  have e := natEq (T_succ (Γ := Γ) j p)
  ipra_le 8 * (1048576 * (𝔞 p + 1) ^ 3) * sl hs + 16 * (𝔞 (Tt j p) + 1024 * (𝔞 p + 1)) with e

/-- The block count: `8s ≤ t`, `8H̄ ≤ t`, `H ≤ H̄` give `(t/2 − s)/H − 1 ≥ t/(4H̄)`, cleared. -/
theorem block_count {t s H Hb : PTm n} (h8s : Γ ⊢[PRAAx] le (num 8 * s) t)
    (h8H : Γ ⊢[PRAAx] le (num 8 * Hb) t) (hH : Γ ⊢[PRAAx] le H Hb) :
    Γ ⊢[PRAAx] le (num 2 * t * H + num 8 * Hb * s + num 8 * Hb * H) (num 4 * Hb * t) := by
  ipra_le 𝔞 Hb * sl h8s + 3 * 𝔞 t * sl hH + 𝔞 H * sl h8H

/-- `1/(4H̄ · 64q²) = 4δ`: `4 · (4H̄ · 64q²) = D`. -/
theorem delta_identity (p : PTm n) :
    Γ ⊢[PRAAx] num 4 * (num 4 * (num 1024 * succ p) * (num 64 * (succ p * succ p))) ≐ Dq p := by
  ipra_ring

end LeanProofs.IPRA.AnalyticNumberTheory.PNTOneStep
