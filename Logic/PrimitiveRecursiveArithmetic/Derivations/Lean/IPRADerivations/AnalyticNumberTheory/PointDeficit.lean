import IPRADerivations.AnalyticNumberTheory.AbsDiff
import IPRADerivations.Core.Header

/-!
# The pointwise deficit inequalities (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:deficit`:
"For `−a ≤ z ≤ a/2` one has `a − |z| ≥ (a + z)/3`", "the inequality `a − |z| ≥ (a − z)/3` for `−a/2 ≤ z ≤ a`", and,
on a stretch where `|r| < a/2`, `a − |r| ≥ a/2`. With `z = r(m) = (ψ(m) − Fm)/(Fm)`, `a = A/D`, values `P = ψ(m)`,
`Q = Fm`, and the deficit term `g = AQ ∸ D|P − Q|` (cleared of denominators):

* `def_lo`: `D|P − Q| ≤ AQ` and `2D(P ∸ Q) ≤ AQ` give `AQ + DP ≤ 3g + DQ`;
* `def_hi`: `D|P − Q| ≤ AQ` and `2D(Q ∸ P) ≤ AQ` give `AQ + DQ ≤ 3g + DP`;
* `def_mid`: `2D|P − Q| ≤ AQ` gives `AQ ≤ 2g`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PointDeficit

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The deficit term `AQ ∸ D|P − Q|`. -/
abbrev dg (A D P Q : PTm n) : PTm n := monus (A * Q) (D * absd P Q)

/-- `|P − Q| = P ∸ Q` when `Q ≤ P`, and `= Q ∸ P` when `P ≤ Q`. -/
theorem absd_ge {P Q : PTm n} (h : Γ ⊢[PRAAx] le Q P) : Γ ⊢[PRAAx] absd P Q ≐ monus P Q :=
  (congrAdd (.eqRefl _) h).eqTrans (add_zero _)

theorem absd_le' {P Q : PTm n} (h : Γ ⊢[PRAAx] le P Q) : Γ ⊢[PRAAx] absd P Q ≐ monus Q P :=
  (congrAdd h (.eqRefl _)).eqTrans (zero_add _)

/-- `D|P − Q| ≤ AQ`, `2D(P ∸ Q) ≤ AQ` ⟹ `AQ + DP ≤ 3g + DQ`. -/
theorem def_lo {A D P Q : PTm n} (hs : Γ ⊢[PRAAx] le (D * absd P Q) (A * Q))
    (hh : Γ ⊢[PRAAx] le (two * (D * monus P Q)) (A * Q)) :
    Γ ⊢[PRAAx] le (A * Q + D * P) (num 3 * dg A D P Q + D * Q) := by
  have eg := natEq (eq_add_of_le hs)
  refine .orE (le_total Q P) ?_ ?_
  · have ea := natEq (absd_ge (Γ := ((le Q P) :: Γ)) Prf.hyp0)
    have ep := natEq (eq_add_of_le (Prf.hyp0 : ((le Q P) :: Γ) ⊢[PRAAx] le Q P))
    have hh' := hh.wk (ψ := le Q P)
    have eg' := natEq (eq_add_of_le (hs.wk (ψ := le Q P)))
    ipra_le 2 * sl hh' with 3 * eg' + 3 * 𝔞 D * ea + 𝔞 D * ep
  · have ea := natEq (absd_le' (Γ := ((le P Q) :: Γ)) Prf.hyp0)
    have ep := natEq (eq_add_of_le (Prf.hyp0 : ((le P Q) :: Γ) ⊢[PRAAx] le P Q))
    have hs' := hs.wk (ψ := le P Q)
    have eg' := natEq (eq_add_of_le hs')
    ipra_le 2 * sl hs' with 3 * eg' + 𝔞 D * ea - 𝔞 D * ep

/-- `D|P − Q| ≤ AQ`, `2D(Q ∸ P) ≤ AQ` ⟹ `AQ + DQ ≤ 3g + DP`. -/
theorem def_hi {A D P Q : PTm n} (hs : Γ ⊢[PRAAx] le (D * absd P Q) (A * Q))
    (hh : Γ ⊢[PRAAx] le (two * (D * monus Q P)) (A * Q)) :
    Γ ⊢[PRAAx] le (A * Q + D * Q) (num 3 * dg A D P Q + D * P) := by
  refine .orE (le_total Q P) ?_ ?_
  · have ea := natEq (absd_ge (Γ := ((le Q P) :: Γ)) Prf.hyp0)
    have ep := natEq (eq_add_of_le (Prf.hyp0 : ((le Q P) :: Γ) ⊢[PRAAx] le Q P))
    have hs' := hs.wk (ψ := le Q P)
    have eg' := natEq (eq_add_of_le hs')
    ipra_le 2 * sl hs' with 3 * eg' + 𝔞 D * ea - 𝔞 D * ep
  · have ea := natEq (absd_le' (Γ := ((le P Q) :: Γ)) Prf.hyp0)
    have ep := natEq (eq_add_of_le (Prf.hyp0 : ((le P Q) :: Γ) ⊢[PRAAx] le P Q))
    have hh' := hh.wk (ψ := le P Q)
    have eg' := natEq (eq_add_of_le (hs.wk (ψ := le P Q)))
    ipra_le 2 * sl hh' with 3 * eg' + 3 * 𝔞 D * ea + 𝔞 D * ep

/-- `2D|P − Q| ≤ AQ` ⟹ `AQ ≤ 2g`. -/
theorem def_mid {A D P Q : PTm n} (hm : Γ ⊢[PRAAx] le (two * (D * absd P Q)) (A * Q)) :
    Γ ⊢[PRAAx] le (A * Q) (two * dg A D P Q) := by
  have hs : Γ ⊢[PRAAx] le (D * absd P Q) (A * Q) := by ipra_le sl hm + 𝔞 D * 𝔞 (absd P Q)
  have eg := natEq (eq_add_of_le hs)
  ipra_le sl hm with 2 * eg

end LeanProofs.IPRA.AnalyticNumberTheory.PointDeficit
