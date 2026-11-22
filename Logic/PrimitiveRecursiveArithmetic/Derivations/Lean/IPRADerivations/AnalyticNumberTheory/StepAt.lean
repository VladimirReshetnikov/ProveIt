import IPRADerivations.AnalyticNumberTheory.StepParams

/-!
# One contraction step at a point (`pnt_ipra_constructive_2026-11-14`, Lemma `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:one-step`, with
every parameter a primitive-recursive function of `x` and of the stage data `(D, A, σ₀)`:

* the half length `H₀ = ⌊24D/A⌋ + 2` (`h0_spec`: `3A² + 384D² ≤ 16DAH₀` for `1 ≤ A ≤ 4D`), the block exponent
  `h = 2H₀ + 1` and its doubling `P = 2h`;
* the exponents `μ, B, σ` of `StepParams`, the chain end `E = 2^μ (2^{2h})^B` and the stage start `Y = 2^σ`,
  so that `E Y = 2^ℓ < x ≤ 2^{ℓ+1} = 2E Y` (`ℓ = λ(x) − 1`).

`step_at`: if the stage bound `D|ψ(m) − Fm| ≤ AFm` holds for `2^{σ₀} ≤ m ≤ x`, then
`D|ψ(x) − Fx| + 3Fx ≤ AFx`, under `2σ₀ + 1 ≤ ℓ`, `576DP ≤ A²`, `1600D ≤ 2^{σ₀}`, the block count
`Lin + Cst ≤ A²PB` (`StepCondition`) and size conditions on the mesh `K` and the factorial denominator `F = L!`.
The auxiliary `stage_mono` (a stage bound from `Y` holds from any `Y' ≥ Y`) and `ux_pos` (`u_x ≥ 1`) are used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.StepAt

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.Doubling (S_pow2_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw' u_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (one_le_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (Stage)
open LeanProofs.IPRA.AnalyticNumberTheory.OneStepDecrement (one_step_decrement)
open LeanProofs.IPRA.AnalyticNumberTheory.StepCondition (DecLin DecCst decc_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell muP BP sgP clog_pos clog_bracket params_spec)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Parameters -/

/-- `H₀ = ⌊24D/A⌋ + 2`. -/
abbrev H0q (D A : PTm n) : PTm n := quo (num 24 * D) A + two
/-- `h = 2H₀ + 1`. -/
abbrev hq (D A : PTm n) : PTm n := two * H0q D A + one
/-- `P = 2h`. -/
abbrev Pq (D A : PTm n) : PTm n := hq D A + hq D A

theorem h0_spec {D A : PTm n} (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * D))) :
    Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (D * D)) (num 16 * (D * (A * H0q D A))) := by
  have dm := div_mod_at (Γ := Γ) (x := num 24 * D) (y := A) (c := pred A) (pos_of_one_le hA1)
  have e := natEq (Prf.andE₁ dm)
  have hr := Prf.andE₂ dm
  ipra_le 16 * 𝔞 D * sl hr + 16 * 𝔞 D + 3 * 𝔞 A * sl hA4 + 4 * 𝔞 D * 𝔞 A with 16 * 𝔞 D * e

theorem one_le_Pq (D A : PTm n) : Γ ⊢[PRAAx] le one (Pq D A) := by
  ipra_le 4 * 𝔞 (quo (num 24 * D) A) + 9

/-! ## Auxiliary facts -/

/-- A stage bound from `Y` holds from every `Y' ≥ Y`. -/
theorem stage_mono {x Y Y' D A K L : PTm n} (hY : Γ ⊢[PRAAx] le Y Y') (h : Γ ⊢[PRAAx] Stage x Y D A K L) :
    Γ ⊢[PRAAx] Stage x Y' D A K L := by
  have hY' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift Y) (Syn.shift Y') := by simpa [Fm.shift, Syn.shift] using hY.shift
  refine .allI (.impI (.impI ?_))
  exact Prf.impE (Prf.impE h.allOpen.wk.wk (.hyp (by simp))) (le_trans hY'.wk.wk Prf.hyp0)

/-- `u_x ≥ 1` for `x ≥ 2` once `F ≥ 4K + 2`. -/
theorem ux_pos {x K F : PTm n} (hK : Γ ⊢[PRAAx] le one K) (h2 : Γ ⊢[PRAAx] le two x)
    (hF : Γ ⊢[PRAAx] le (num 4 * K + two) F) : Γ ⊢[PRAAx] le one (U x K F) := by
  have p := S_pow2_lower F one hK
  have hKT : Γ ⊢[PRAAx] le K (K * pw two one) := by
    have q := le_scale K (one_le_pw' (le_succ_self (Γ := Γ) one) one)
    ipra_le sl q
  have e := natEq (eq_add_of_le (S_mono F hKT))
  have e2 := natEq (pw_one (Γ := Γ) (two : PTm n))
  have hu2 : Γ ⊢[PRAAx] le (two * one) (two * U (pw two one) K F) := by
    ipra_le sl p + sl hF with 2 * e + 2 * 𝔞 K * e2
  have h2' : Γ ⊢[PRAAx] le (pw two one) x := le_congr (pw_one two).eqSymm (.eqRefl _) h2
  exact le_trans (mul_le_cancel (d' := one) hu2) (u_mono K F h2')

/-! ## The step at `x` -/

theorem step_at {x s0 D A K L : PTm n} (h2x : Γ ⊢[PRAAx] le two x) (hs0 : Γ ⊢[PRAAx] le one s0)
    (hl : Γ ⊢[PRAAx] le (two * s0 + one) (ell x))
    (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K) (hL4 : Γ ⊢[PRAAx] le (K * Q4 x) L)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hxL : Γ ⊢[PRAAx] le x L) (hxK : Γ ⊢[PRAAx] le x K) (hNN : Γ ⊢[PRAAx] le (K * pw x x) L)
    (hF : Γ ⊢[PRAAx] le (two * x) (fact L)) (h2K : Γ ⊢[PRAAx] le (two * (K * x)) (fact L))
    (hF4 : Γ ⊢[PRAAx] le (num 4 * K + two) (fact L))
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * D))) (hD1 : Γ ⊢[PRAAx] le one D)
    (hAP : Γ ⊢[PRAAx] le (num 576 * D * Pq D A) (A * A)) (hZ : Γ ⊢[PRAAx] le (num 1600 * D) (pw two s0))
    (hB : Γ ⊢[PRAAx] le (DecLin D A (Pq D A) s0 + DecCst D A (Pq D A) s0) (A * A * Pq D A * BP x s0 (Pq D A)))
    (hB1 : Γ ⊢[PRAAx] le one (BP x s0 (Pq D A))) (hst : Γ ⊢[PRAAx] Stage x (pw two s0) D A K L) :
    Γ ⊢[PRAAx] le (D * absd (Psi wt x (pairT K (fact L))) (fact L * x) + num 3 * (fact L * x)) (A * (fact L * x)) := by
  have sp := params_spec hs0 (one_le_Pq D A) hl
  have hms := Prf.andE₁ sp
  have hμ := Prf.andE₁ (Prf.andE₁ (Prf.andE₂ sp))
  have hμu := Prf.andE₂ (Prf.andE₁ (Prf.andE₂ sp))
  have hT1 := Prf.andE₁ (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sp)))
  have hsσ := Prf.andE₂ (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sp)))
  have hsP := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sp)))
  have esp := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sp)))
  have br := clog_bracket h2x
  have hlt := Prf.andE₁ br
  have hle := Prf.andE₂ br
  have h12 : Γ ⊢[PRAAx] le one two := le_succ_self one
  have p2 : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le h12
  -- the chain end `E = 2^μ (2^{2h})^B = 2^{μ + PB}`
  have eE : Γ ⊢[PRAAx] pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A)) ≐
      pw two (muP x + Pq D A * BP x s0 (Pq D A)) :=
    (congrMul (.eqRefl _) (pw_mul two _ _)).eqTrans (pw_add two _ _).eqSymm
  have eEY : Γ ⊢[PRAAx] pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A)) * pw two (sgP x s0 (Pq D A)) ≐
      pw two (ell x) :=
    (congrMul eE (.eqRefl _)).eqTrans ((pw_add two _ _).eqSymm.eqTrans (congrAp2 powF esp (.eqRefl _)))
  have eEY1 : Γ ⊢[PRAAx] pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A)) *
      pw two (succ (sgP x s0 (Pq D A))) ≐ pw two (succ (ell x)) := by
    have a := natEq (pw_succ (Γ := Γ) two (sgP x s0 (Pq D A)))
    have b := natEq (pw_succ (Γ := Γ) two (ell x))
    have c := natEq eEY
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (pw two (muP x)) * 𝔞 (pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A))) * a - b + 2 * c
  have hE1 : Γ ⊢[PRAAx] le one (pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A))) :=
    one_le_mul (one_le_pw' h12 _) (one_le_pw' (one_le_pw' h12 _) _)
  have pE := pos_of_one_le hE1
  have hσ1 : Γ ⊢[PRAAx] le one (pw two (sgP x s0 (Pq D A))) := one_le_pw' h12 _
  have hEl : Γ ⊢[PRAAx] le (pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A))) (pw two (ell x)) := by
    have q := le_scale (pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A))) hσ1
    have c := natEq eEY
    ipra_le sl q with c
  have hlx := le_of_lt hlt
  have hEx := le_trans hEl hlx
  have hZl : Γ ⊢[PRAAx] le (pw two s0 * (pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A)))) x := by
    have q := le_scale (pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A))) (pw_le_exp p2 hsσ)
    have c := natEq eEY
    ipra_le sl q + sl hlx with c
  have hμl : Γ ⊢[PRAAx] le (muP x) (ell x) := by
    have c := natEq esp
    ipra_le (4 * 𝔞 (quo (num 24 * D) A) + 10) * 𝔞 (BP x s0 (Pq D A)) + 𝔞 (sgP x s0 (Pq D A)) with c
  have hμx := le_trans (pw_le_exp p2 hμl) hlx
  have hcl : Γ ⊢[PRAAx] clog x ≐ succ (ell x) := pos_of_one_le (clog_pos h2x)
  have hTc : Γ ⊢[PRAAx] le (clog x) (two * muP x + two) := le_congr hcl.eqSymm (.eqRefl _) hT1
  have hμ1 := le_trans hs0 hms
  have hC := decc_bound (D := D) (A := A) hμ hμu hTc hsP hAP hB hB1 hZ hA1 hμ1
  have h2Kμ : Γ ⊢[PRAAx] le (two * (K * pw two (muP x))) (fact L) := by
    have q := le_scale (two * K) hμx
    ipra_le sl q + sl h2K
  refine one_step_decrement (M := pred (pw two (muP x) * pw (pw two (hq D A + hq D A)) (BP x s0 (Pq D A))))
    (Y := pw two (sgP x s0 (Pq D A))) (h := hq D A) (H0 := H0q D A) (T := clog x) (s := sgP x s0 (Pq D A))
    (Z := pw two s0) (le_trans h12 h2x) hK hx4 hL4 hP hKx (le_congr pE (.eqRefl _) hEx)
    (le_congr (congrMul pE (.eqRefl _)) (.eqRefl _) (le_congr eEY.eqSymm (.eqRefl _) hlx))
    (stage_mono (pw_le_exp p2 hsσ) hst) (le_congr (.eqRefl _) pE (le_refl _)) hxL hxK hNN hA1 hA4
    (h0_spec hA1 hA4) (le_refl _) hF ?_ (le_congr (.eqRefl _) (congrMul pE (.eqRefl _)) (le_congr (.eqRefl _) eEY1.eqSymm hle))
    (le_congr (congrMul (.eqRefl _) pE) (.eqRefl _) hZl) (pw_le_exp p2 hms) h2Kμ hC (one_le_pw' h12 s0) hD1
    (ux_pos hK h2x hF4)
  exact Prf.andE₁ (clog_spec x)

end LeanProofs.IPRA.AnalyticNumberTheory.StepAt
