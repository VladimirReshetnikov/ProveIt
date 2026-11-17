import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.SumOrder

/-!
# Removing an auxiliary error from a rational comparison

Packet: `stirling_ipra`, Lemma `lem:gap`. A rational comparison `u ≤ v` with common denominator
`D` is the integer comparison `U ≤ V` of the numerators, and an auxiliary error `B 2^{−k}` with
`B D ≤ C` becomes `U 2^k ≤ V 2^k + C`. The lemma needs only the single instance `k = C`:

* `gap_of`: if `C < 2^k` and `U 2^k ≤ V 2^k + C`, then `U ≤ V`;
* `gap` (`lem:gap`): if `U 2^C ≤ V 2^C + C`, then `U ≤ V`, using `C < 2^C`;
* `gap_all`: the same from the hypothesis for every `k` (`∀ k, U 2^k ≤ V 2^k + C`), instantiated
  at `k = C`.

The case split is on the decidable comparison `V < U ∨ U ≤ V` of natural numbers.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GapRemoval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem gap_contra {U V C k : PTm n} (hk : Γ ⊢[PRAAx] lt C (pw two k)) (hVU : Γ ⊢[PRAAx] lt V U)
    (h : Γ ⊢[PRAAx] le (U * pw two k) (V * pw two k + C)) : Γ ⊢[PRAAx] le U V := by
  have hk' : Γ ⊢[PRAAx] le (succ C) (pw two k) := hk
  have hVU' : Γ ⊢[PRAAx] le (succ V) U := hVU
  have l₁ : Γ ⊢[PRAAx] le (succ (V * pw two k + C)) (V * pw two k + pw two k) :=
    le_congr (add_succ _ _) (.eqRefl _) (add_le_add₂ (le_refl (V * pw two k)) hk')
  have l₂ : Γ ⊢[PRAAx] le (V * pw two k + pw two k) (U * pw two k) :=
    le_congr (show Γ ⊢[PRAAx] succ V * pw two k ≐ V * pw two k + pw two k by apply deriveNat; ipra_simps; ring)
      (.eqRefl _) (le_mul_mono hVU' (le_refl (pw two k)))
  have c : Γ ⊢[PRAAx] lt (V * pw two k + C) (V * pw two k + C) := le_trans (le_trans l₁ l₂) h
  exact lt_irrefl _ _ c

/-- If `C < 2^k` and `U 2^k ≤ V 2^k + C`, then `U ≤ V`. -/
theorem gap_of {U V C k : PTm n} (hk : Γ ⊢[PRAAx] lt C (pw two k))
    (h : Γ ⊢[PRAAx] le (U * pw two k) (V * pw two k + C)) : Γ ⊢[PRAAx] le U V :=
  .orE (lt_or_le V U) (gap_contra hk.wk Prf.hyp0 h.wk) Prf.hyp0

/-- `lem:gap`: `U 2^C ≤ V 2^C + C` gives `U ≤ V`. -/
theorem gap {U V C : PTm n} (h : Γ ⊢[PRAAx] le (U * pw two C) (V * pw two C + C)) : Γ ⊢[PRAAx] le U V :=
  gap_of (lt_pw (le_refl two) C) h

/-- `lem:gap`, from the hypothesis for every `k`. -/
theorem gap_all {U V C : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (le (Syn.shift U * pw two (var 0)) (Syn.shift V * pw two (var 0) + Syn.shift C))) :
    Γ ⊢[PRAAx] le U V := by
  have hC := Prf.allE C h
  simp only [subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_shift,
    Syn.inst_succ, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hC
  exact gap (by simpa using hC)

end LeanProofs.IPRA.Analysis.GapRemoval
