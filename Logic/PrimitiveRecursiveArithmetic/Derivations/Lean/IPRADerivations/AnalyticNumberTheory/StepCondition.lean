import IPRADerivations.AnalyticNumberTheory.OneStepDecrement

/-!
# The integer step condition from the block count (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"Their number `b` satisfies `b ≥ (t/2 − s)/H − 1 ≥ … ≥ t/(4H̄)` … `|r(t)| ≤ a − 4δ + (8s + S)/t ≤ a − 3δ`."
The condition `OneStepDecrement.DecC` on the dyadic exponents of the step (`2^μ` the first block start, `B`
blocks of exponent length `P = 2h`, `x ≤ 2^T`, the unknown region `m < 2^σ`) follows from

* `μ ≥ PB`, `μ ≥ 1`, `T ≤ 2μ + 2`, `σ + 1 ≤ σ₀ + P` (the blocks fill the upper half of the exponents);
* `576 D P ≤ A²` (the deficit per block, `A²/D` in units of `1/P`, beats the decrement cost);
* `Lin + Cst ≤ A² P B`, `B ≥ 1` (enough blocks: `B` grows linearly in `T`);
* `1600 D ≤ Z`, `A ≥ 1` (the block error terms `D₂ + x/D₁` are small).

`step_core` is the slack certificate of the quadratic inequality in `B` (checked by elimination), `decc_of`
absorbs the block error, `decc_bound` combines them.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.StepCondition

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.OneStepDecrement (DecW DecC)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias mul_le2 := Common.mul_le_mul

/-- The linear coefficient: `3A² + 1152DP(P + σ₀ + 1) + 768D²P(σ₀ + P) + 1845312D²P`. -/
abbrev DecLin (D A P s0 : PTm n) : PTm n :=
  num 3 * (A * A) + num 1152 * (D * P) * (P + s0 + one) + num 768 * (D * D) * P * (s0 + P) +
    num 1845312 * (D * D) * P

/-- The constant: `576D c² + 96DA + 768D² c(σ₀ + P) + 384D² + 48D²(38444c + 11070)`, `c = P + σ₀ + 1`. -/
abbrev DecCst (D A P s0 : PTm n) : PTm n :=
  num 576 * D * ((P + s0 + one) * (P + s0 + one)) + num 96 * (D * A) +
    num 768 * (D * D) * (P + s0 + one) * (s0 + P) + num 384 * (D * D) +
    num 48 * (D * D) * (num 38444 * (P + s0 + one) + num 11070)

/-- The quadratic inequality `2W + 3A²B ≤ 2A²Bμ`. -/
theorem step_core {D A B P μ T s s0 : PTm n} (hμ : Γ ⊢[PRAAx] le (P * B) μ)
    (hTV : Γ ⊢[PRAAx] le T (two * (P * B + (P + s0 + one)))) (hs : Γ ⊢[PRAAx] le (succ s) (s0 + P))
    (hAP : Γ ⊢[PRAAx] le (num 576 * D * P) (A * A))
    (hB : Γ ⊢[PRAAx] le (DecLin D A P s0 + DecCst D A P s0) (A * A * P * B)) (hB1 : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le (two * DecW D A T s + num 3 * (A * A) * B) (num 2 * (A * A) * B * μ) := by
  have hTT := mul_le2 hTV hTV
  have hTs := mul_le2 hTV hs
  ipra_le 2 * 𝔞 A * 𝔞 A * 𝔞 B * sl hμ + 144 * 𝔞 D * sl hTT + 384 * 𝔞 D * 𝔞 D * sl hTs +
    922656 * 𝔞 D * 𝔞 D * sl hTV + 𝔞 P * 𝔞 B * 𝔞 B * sl hAP + 𝔞 B * sl hB +
    (576 * 𝔞 D * (𝔞 P + 𝔞 s0 + 1) * (𝔞 P + 𝔞 s0 + 1) + 96 * 𝔞 D * 𝔞 A +
      768 * 𝔞 D * 𝔞 D * (𝔞 P + 𝔞 s0 + 1) * (𝔞 s0 + 𝔞 P) + 384 * 𝔞 D * 𝔞 D +
      48 * 𝔞 D * 𝔞 D * (38444 * (𝔞 P + 𝔞 s0 + 1) + 11070)) * sl hB1

/-- The block error is absorbed once `Z ≥ 1600 D`. -/
theorem decc_of {D A B μ T s Z : PTm n}
    (hG : Γ ⊢[PRAAx] le (two * DecW D A T s + num 3 * (A * A) * B) (num 2 * (A * A) * B * μ))
    (hZ : Γ ⊢[PRAAx] le (num 1600 * D) Z) (hA1 : Γ ⊢[PRAAx] le one A) (hT : Γ ⊢[PRAAx] le T (two * μ + two))
    (hμ1 : Γ ⊢[PRAAx] le one μ) : Γ ⊢[PRAAx] DecC D A B T s μ Z := by
  ipra_le 𝔞 Z * sl hG + 𝔞 A * 𝔞 B * 𝔞 A * 𝔞 μ * sl hZ + 1600 * 𝔞 A * 𝔞 B * 𝔞 D * 𝔞 μ * sl hA1 +
    400 * 𝔞 A * 𝔞 B * 𝔞 D * sl hT + 800 * 𝔞 A * 𝔞 B * 𝔞 D * sl hμ1

/-- The step condition from the block count. -/
theorem decc_bound {D A B P μ T s s0 Z : PTm n} (hμ : Γ ⊢[PRAAx] le (P * B) μ)
    (hμu : Γ ⊢[PRAAx] le μ (P * B + P + s0)) (hT : Γ ⊢[PRAAx] le T (two * μ + two))
    (hs : Γ ⊢[PRAAx] le (succ s) (s0 + P)) (hAP : Γ ⊢[PRAAx] le (num 576 * D * P) (A * A))
    (hB : Γ ⊢[PRAAx] le (DecLin D A P s0 + DecCst D A P s0) (A * A * P * B)) (hB1 : Γ ⊢[PRAAx] le one B)
    (hZ : Γ ⊢[PRAAx] le (num 1600 * D) Z) (hA1 : Γ ⊢[PRAAx] le one A) (hμ1 : Γ ⊢[PRAAx] le one μ) :
    Γ ⊢[PRAAx] DecC D A B T s μ Z := by
  have hTV : Γ ⊢[PRAAx] le T (two * (P * B + (P + s0 + one))) := by ipra_le sl hT + 2 * sl hμu
  exact decc_of (step_core hμ hTV hs hAP hB hB1) hZ hA1 hT hμ1

end LeanProofs.IPRA.AnalyticNumberTheory.StepCondition

export_ipra AnalyticNumberTheory.StepCondition (mul_le2)
