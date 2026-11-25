import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The comparison-sorting lower bound and the interpolated median

Packet: `probability/median_ipra_constructive_proofs`, Section "Sorting lower bound" and
Theorem `thm:interpolated`.

* `fact_pos`: `1 ≤ N!`;
* `pw_fact`: `m^k ≤ (m + k)!`, the last `k` factors of `(m + k)!` being at least `m`;
* `fact_double`: `m^m ≤ (2m)!`;
* `sorting_bound`: a decision tree of depth `d` sorting `2m` distinct inputs has `(2m)! ≤ 2^d`;
  if moreover `2^r ≤ m`, then `r m ≤ d` (with `r = ⌊log₂ m⌋` this is `Ω(n log n)`);
* `interpolated` (`thm:interpolated`): for `N = i + j + k`, the two forms
  `m − w/2 + w (N/2 − i)/j` and `m + (w/2)(k − i)/j` of the interpolated median agree, in the
  subtraction-free cleared form
  `2jm + wN + wi = 2jm + wk + jw + 2wi`;
* `interpolated_example`: the packet's example `i = 22`, `j = 33`, `k = 45`, `m = 3`, `w = 1`
  gives `3 + 23/66 = 221/66`.

The counting of decision-tree leaves is the hypothesis `(2m)! ≤ 2^d`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.SortingBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (pw_two_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `N!`. -/
abbrev fct (x : PTm n) : PTm n := ap2 factF x zero

alias le_one_succ := Common.one_le_succ

/-- Variable: `0 = x`. -/
private abbrev fpF : Fm PTm 1 := le one (ap2 factF (var 0) zero)

private theorem fp₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fpF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact le_congr (.eqRefl _) (fact_zero _).eqSymm (le_refl _)
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact le_congr (by ipra_ring) (fact_succ _ _).eqSymm (le_mul_mono Prf.hyp0 (le_one_succ _))

/-- `1 ≤ N!`. -/
theorem fact_pos (x : PTm n) : Γ ⊢[PRAAx] le one (fct x) := by
  have h := inst (Γ := Γ) fp₀ (![x] : Fin 1 → PTm n)
  simpa using h

/-- Variables: `0 = k`, `1 = m`. -/
private abbrev pfF : Fm PTm 2 := le (pw (var 1) (var 0)) (ap2 factF (var 1 + var 0) zero)

private theorem pf₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] pfF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact le_congr (pw_zero _).eqSymm (congrAp2 factF (add_zero _).eqSymm (.eqRefl _)) (fact_pos _)
  · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_congr (pw_succ _ _).eqSymm
      ((congrAp2 factF (add_succ _ _) (.eqRefl _)).eqTrans (fact_succ _ _)).eqSymm ?_
    exact le_mul_mono Prf.hyp0 (le_of_eq_add (d := succ (var 0)) (by ipra_ring))

/-- `m^k ≤ (m + k)!`. -/
theorem pw_fact (m k : PTm n) : Γ ⊢[PRAAx] le (pw m k) (fct (m + k)) := by
  have h := inst (Γ := Γ) pf₀ (![k, m] : Fin 2 → PTm n)
  simpa using h

/-- `m^m ≤ (2m)!`. -/
theorem fact_double (m : PTm n) : Γ ⊢[PRAAx] le (pw m m) (fct (m + m)) := pw_fact m m

/-- A sorting decision tree of depth `d` on `2m` inputs has `(2m)! ≤ 2^d`; if `2^r ≤ m`, then
`r m ≤ d`. -/
theorem sorting_bound {d m r : PTm n} (hd : Γ ⊢[PRAAx] le (fct (m + m)) (pw two d))
    (hr : Γ ⊢[PRAAx] le (pw two r) m) : Γ ⊢[PRAAx] le (r * m) d := by
  have chain : Γ ⊢[PRAAx] le (pw two (r * m)) (pw two d) :=
    le_trans (le_congr (pw_mul two r m) (.eqRefl _) (pw_le_pw m hr)) (le_trans (fact_double m) hd)
  refine .orE (lt_or_le d (r * m)) ?_ Prf.hyp0
  exact lt_irrefl (pw two d) _ (lt_of_lt_of_le (pw_two_lt Prf.hyp0) chain.wk)

/-- `thm:interpolated`, cleared of `2j`: for `N = i + j + k`,
`2jm − jw + w(N − 2i) = 2jm + w(k − i)`, written `2jm + wN + wi = 2jm + wk + jw + 2wi`. -/
theorem interpolated {N i j k m w : PTm n} (h : Γ ⊢[PRAAx] N ≐ i + j + k) :
    Γ ⊢[PRAAx] two * j * m + w * N + w * i ≐ two * j * m + w * k + j * w + w * i + w * i := by
  ipra_lc 𝔞 w * natEq h

/-- The packet's example: `3 · 66 + (45 − 22) = 221`, i.e. `m_int = 221/66`. -/
theorem interpolated_example :
    Γ ⊢[PRAAx] (num 3 : PTm n) * num 66 + monus (num 45) (num 22) ≐ num 221 := by
  have e : Γ ⊢[PRAAx] (num 45 : PTm n) ≐ num 22 + num 23 := by apply deriveNat; ipra_simps; norm_num
  refine (congrAdd (.eqRefl _) ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _))).eqTrans ?_
  apply deriveNat; ipra_simps; norm_num

end LeanProofs.IPRA.Probability.SortingBound
