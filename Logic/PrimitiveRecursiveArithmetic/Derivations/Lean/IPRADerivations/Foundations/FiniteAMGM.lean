import IPRADerivations.Analysis.Optimization.WeightedAMGM
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The finite arithmetic–geometric mean inequality

Packet: `geometry/isoperimetric_ipra_constructive_2026-11-15`, `report/hypercube.tex`, Lemma
"Finite AM–GM": "For nonnegative rational numbers `x_1, …, x_m`, `m ≥ 1`,
`∏_{j=1}^{m} x_j ≤ ((x_1 + ⋯ + x_m)/m)^m`." It is also the "finite AM–GM lemma" of
`analysis/bohr_mollerup_ipra_2026-11-15` and the step "Finite arithmetic–geometric mean gives
`(e_j/C)^C ≥ q^{jC}`. Since nonnegative rational powers are order-reflecting, `e_j ≥ C q^j`" of
`lem:box-product` (`report/euclidean.tex`).

For a family `y(j, x)` given by an arbitrary body and `m = N + 1` values, cleared of the
denominator `m` (and of a common denominator of the values, by homogeneity):

* `amgm_step`: one more value;
* `finite_amgm`: `m^m · ∏_{j<m} y_j ≤ (Σ_{j<m} y_j)^m`;
* `amgm_sum`: if `q^m ≤ ∏_{j<m} y_j` then `m q ≤ Σ_{j<m} y_j` (the order-reflecting form, without
  roots).

The packet pads the list to a power of two (`Geometry/HypercubeSplit.amgm2`, `amgm4` are the
first two levels of its tree). Here one value is added at a time: from `m^m P ≤ S^m`, the
inequality `(m + 1)^{m+1} S^m y ≤ m^m (S + y)^{m+1}` (`Analysis/WeightedAMGM.one_step`, AM–GM for
`m` copies of `S/m` and one `y`) gives `(m + 1)^{m+1} P y ≤ (S + y)^{m+1}` after cancelling
`m^m`. The equality case is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteAMGM

open_ipra
open LeanProofs.IPRA.Analysis.WeightedAMGM (one_step)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_lt_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Family

variable (y : PTm 2)

theorem prod_succ'' (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF y) (succ N) x ≐ ap2 (prodF y) N x * inst2 y N x :=
  prod_succ y N x

/-- One more value. -/
theorem amgm_step {N x : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw (succ N) (succ N) * ap2 (prodF y) (succ N) x)
      (pw (ap2 (sumF y) (succ N) x) (succ N))) :
    Γ ⊢[PRAAx] le (pw (succ (succ N)) (succ (succ N)) * ap2 (prodF y) (succ (succ N)) x)
      (pw (ap2 (sumF y) (succ (succ N)) x) (succ (succ N))) := by
  have s₂ := one_step (Γ := Γ) (n₀ := N) (X := ap2 (sumF y) (succ N) x)
    (v := inst2 y (succ N) x)
  have s₁ := mul_le_mul_right (pw (succ (succ N)) (succ (succ N)) * inst2 y (succ N) x) ih
  have tot : Γ ⊢[PRAAx]
      le (pw (succ N) (succ N) * ap2 (prodF y) (succ N) x *
          (pw (succ (succ N)) (succ (succ N)) * inst2 y (succ N) x))
        (pw (succ N) (succ N) *
          pw (ap2 (sumF y) (succ N) x + inst2 y (succ N) x) (succ (succ N))) :=
    le_trans s₁ (le_congr (by ipra_ring) (.eqRefl _) s₂)
  have hpos := pw_pos' (Γ := Γ) (p := succ N) (congrSucc (pred_succ N).eqSymm) (succ N)
  have big : Γ ⊢[PRAAx]
      le (succ (pred (pw (succ N) (succ N))) *
          (pw (succ (succ N)) (succ (succ N)) * ap2 (prodF y) (succ (succ N)) x))
        (succ (pred (pw (succ N) (succ N))) *
          pw (ap2 (sumF y) (succ (succ N)) x) (succ (succ N))) := by
    refine le_congr ?_ (congrMul hpos (congrPw (sum_succ' y (succ N) x).eqSymm (.eqRefl _))) tot
    ipra_lc (𝔞 (pw (succ (succ N)) (succ (succ N))) * 𝔞 (ap2 (prodF y) (succ N) x) * 𝔞 (inst2 y (succ N) x)) * natEq hpos -
      ((𝔞 (pred (pw (succ N) (succ N))) + 1) * 𝔞 (pw (succ (succ N)) (succ (succ N)))) * natEq (prod_succ'' (Γ := Γ) y (succ N) x)
  exact mul_le_cancel big

/-- The induction formula of `finite_amgm`; variable `0 = N`. -/
abbrev amgmF (x : PTm n) : Fm PTm (n + 1) :=
  le (pw (succ (var 0)) (succ (var 0)) * ap2 (prodF y) (succ (var 0)) (Syn.shift x))
    (pw (ap2 (sumF y) (succ (var 0)) (Syn.shift x)) (succ (var 0)))

/-- Finite AM–GM for `m = N + 1` values: `m^m ∏_{j<m} y_j ≤ (Σ_{j<m} y_j)^m`. -/
theorem finite_amgm (N x : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ N) (succ N) * ap2 (prodF y) (succ N) x)
      (pw (ap2 (sumF y) (succ N) x) (succ N)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (amgmF y x) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · have b : Γ ⊢[PRAAx] le (pw (succ zero) (succ zero) * ap2 (prodF y) (succ zero) x)
          (pw (ap2 (sumF y) (succ zero) x) (succ zero)) := by
        have e₂ := natEq ((prod_succ'' (Γ := Γ) y zero x).eqTrans
          (congrMul (prod_zero y x) (.eqRefl _)))
        have e₃ := natEq ((pw_one (Γ := Γ) (ap2 (sumF y) (succ zero) x)).eqTrans
          (sum_singleton y x))
        refine le_of_eq_add (d := zero) ?_
        ipra_lc e₃ - 𝔞 (ap2 (prodF y) (succ zero) x) * natEq (pw_one (Γ := Γ) (succ zero)) - e₂
      simpa using b
    · have st : (amgmF y x :: Γ.map Fm.shift) ⊢[PRAAx]
          le (pw (succ (succ (var 0))) (succ (succ (var 0))) *
              ap2 (prodF y) (succ (succ (var 0))) (Syn.shift x))
            (pw (ap2 (sumF y) (succ (succ (var 0))) (Syn.shift x)) (succ (succ (var 0)))) :=
        amgm_step y Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE N hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- The order-reflecting form: `q^m ≤ ∏_{j<m} y_j` gives `m q ≤ Σ_{j<m} y_j`. -/
theorem amgm_sum {N x q : PTm n}
    (h : Γ ⊢[PRAAx] le (pw q (succ N)) (ap2 (prodF y) (succ N) x)) :
    Γ ⊢[PRAAx] le (succ N * q) (ap2 (sumF y) (succ N) x) := by
  refine .orE (lt_or_le (ap2 (sumF y) (succ N) x) (succ N * q)) ?_ Prf.hyp0
  have strict := pw_lt_pw N (Prf.hyp0 (Γ := Γ)
    (φ := lt (ap2 (sumF y) (succ N) x) (succ N * q)))
  have upper : (lt (ap2 (sumF y) (succ N) x) (succ N * q) :: Γ) ⊢[PRAAx]
      le (pw (succ N * q) (succ N)) (pw (ap2 (sumF y) (succ N) x) (succ N)) :=
    le_congr (pw_mul_base (succ N) q (succ N)).eqSymm (.eqRefl _)
      (le_trans (le_mul_mono (le_refl _) h.wk) (finite_amgm y N x))
  exact le_lt_absurd _ upper strict

end Family

end LeanProofs.IPRA.Foundations.FiniteAMGM
