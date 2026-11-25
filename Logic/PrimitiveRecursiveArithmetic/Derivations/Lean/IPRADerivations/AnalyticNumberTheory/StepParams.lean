import IPRADerivations.AnalyticNumberTheory.StepCondition
import IPRADerivations.AnalyticNumberTheory.ZetaFiniteContract
import IPRADerivations.Core.LinearCombination

/-!
# The dyadic exponents of one contraction step (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"There is no need to decide a floor of a real number: when `x = e^t` is rational, the permitted blocks are found
by the rational test `(e^s Q^{mi})² ≤ x`." Here every choice is a primitive-recursive function of `x`, through
the ceiling binary logarithm `λ = ZetaFiniteContract.clog x`:

* `ℓ = λ − 1`, so `2^ℓ < x ≤ 2^{ℓ+1}` for `x ≥ 2` (`clog_bracket`);
* `μ = ⌊ℓ/2⌋` (the first block starts at `2^μ ≈ √x`), `B = ⌊(ℓ − μ − σ₀)/P⌋` blocks of exponent length `P`, and
  the remainder `σ = ℓ − μ − PB ∈ [σ₀, σ₀ + P)` (the stage start of the step, `2^σ ≥ 2^{σ₀}`).

`params_spec` collects the facts used by `StepCondition.decc_bound` and `OneStepDecrement.one_step_decrement`:
`PB ≤ μ ≤ PB + P + σ₀`, `λ ≤ 2μ + 2`, `σ₀ ≤ σ`, `σ + 1 ≤ σ₀ + P` and the exact split `μ + PB + σ = ℓ`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.StepParams

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec clog_least)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The binary logarithm bracket -/

/-- `λ(x) ≥ 1` for `x ≥ 2`. -/
theorem clog_pos {x : PTm n} (h : Γ ⊢[PRAAx] le two x) : Γ ⊢[PRAAx] le one (clog x) := by
  refine .orE (lt_or_le (clog x) one) ?_ Prf.hyp0
  have hz : (lt (clog x) one :: Γ) ⊢[PRAAx] le (clog x) zero := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have hc : (lt (clog x) one :: Γ) ⊢[PRAAx] clog x ≐ zero := (monus_zero _).eqSymm.eqTrans hz
  have hp : (lt (clog x) one :: Γ) ⊢[PRAAx] le x one :=
    le_congr (.eqRefl _) ((congrAp2 powF hc (.eqRefl two)).eqTrans (pw_zero two)) (Prf.andE₁ (clog_spec x))
  exact lt_irrefl one _ (le_trans h.wk hp)

/-- `ℓ = λ − 1`. -/
abbrev ell (x : PTm n) : PTm n := pred (clog x)

/-- `2^ℓ < x ≤ 2^{ℓ+1}`. -/
theorem clog_bracket {x : PTm n} (h : Γ ⊢[PRAAx] le two x) :
    Γ ⊢[PRAAx] lt (pw two (ell x)) x ⋏ le x (pw two (succ (ell x))) := by
  have hp := pos_of_one_le (clog_pos h)
  have hl : Γ ⊢[PRAAx] lt (ell x) (clog x) := le_congr (.eqRefl _) hp.eqSymm (le_refl _)
  exact .andI (clog_least hl) (le_congr (.eqRefl _) (congrAp2 powF hp (.eqRefl two)) (Prf.andE₁ (clog_spec x)))

/-! ## The exponents -/

/-- `μ = ⌊ℓ/2⌋`. -/
abbrev muP (x : PTm n) : PTm n := quo (ell x) two

/-- `B = ⌊(ℓ − μ − σ₀)/P⌋`. -/
abbrev BP (x s0 P : PTm n) : PTm n := quo (monus (monus (ell x) (muP x)) s0) P

/-- `σ = ℓ − μ − PB`. -/
abbrev sgP (x s0 P : PTm n) : PTm n := monus (monus (ell x) (muP x)) (P * BP x s0 P)

/-- The exponent facts, for `σ₀ ≥ 1`, `P ≥ 1` and `2σ₀ + 1 ≤ ℓ`. -/
theorem params_spec {x s0 P : PTm n} (hs0 : Γ ⊢[PRAAx] le one s0) (hP : Γ ⊢[PRAAx] le one P)
    (hl : Γ ⊢[PRAAx] le (two * s0 + one) (ell x)) :
    Γ ⊢[PRAAx] le s0 (muP x) ⋏ (le (P * BP x s0 P) (muP x) ⋏ le (muP x) (P * BP x s0 P + P + s0)) ⋏
      ((le (succ (ell x)) (two * muP x + two) ⋏ le s0 (sgP x s0 P)) ⋏
        (le (succ (sgP x s0 P)) (s0 + P) ⋏ muP x + P * BP x s0 P + sgP x s0 P ≐ ell x)) := by
  have d1 := div_mod_at (Γ := Γ) (x := ell x) (y := two) (c := one) (.eqRefl _)
  have e1 := natEq (Prf.andE₁ d1)
  have r1 := Prf.andE₂ d1
  have hμl : Γ ⊢[PRAAx] le (muP x) (ell x) := by ipra_le 𝔞 (muP x) + 𝔞 (rem (ell x) two) with e1
  have f1 := natEq (eq_add_of_le hμl)
  have hm2 : Γ ⊢[PRAAx] le (two * s0) (two * muP x) := by ipra_le sl hl + sl r1 with e1
  have hms : Γ ⊢[PRAAx] le s0 (muP x) := mul_le_cancel (d' := one) hm2
  have hs : Γ ⊢[PRAAx] le s0 (monus (ell x) (muP x)) := by ipra_le sl hms + 𝔞 (rem (ell x) two) with f1 - e1
  have f2 := natEq (eq_add_of_le hs)
  have d2 := div_mod_at (Γ := Γ) (x := monus (monus (ell x) (muP x)) s0) (y := P) (c := pred P) (pos_of_one_le hP)
  have e2 := natEq (Prf.andE₁ d2)
  have r2 := Prf.andE₂ d2
  have hPB : Γ ⊢[PRAAx] le (P * BP x s0 P) (monus (ell x) (muP x)) := by
    ipra_le 𝔞 s0 + 𝔞 (rem (monus (monus (ell x) (muP x)) s0) P) with f2 + e2
  have f3 := natEq (eq_add_of_le hPB)
  refine .andI hms (.andI (.andI ?_ ?_) (.andI (.andI ?_ ?_) (.andI ?_ ?_)))
  · ipra_le sl hs0 + sl r1 + 𝔞 (rem (monus (monus (ell x) (muP x)) s0) P) with f1 - e1 + f2 + e2
  · ipra_le sl r2 + 𝔞 (rem (ell x) two) + 1 with f1 - e1 + f2 + e2
  · ipra_le sl r1 with e1
  · ipra_le 𝔞 (rem (monus (monus (ell x) (muP x)) s0) P) with f2 + e2 - f3
  · ipra_le sl r2 with f2 + e2 - f3
  · ipra_lc -f1 - f3

end LeanProofs.IPRA.AnalyticNumberTheory.StepParams
