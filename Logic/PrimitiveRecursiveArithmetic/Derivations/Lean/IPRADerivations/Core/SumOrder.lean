import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.LinearCombination

/-!
# Comparing sums with different parameters

* `add_le_add₂`: `a ≤ b` and `c ≤ d` give `a + c ≤ b + d`;
* `sum_le_params`: if `f(i, x) ≤ g(i, y)` for `i < N`, then
  `∑_{i<N} f(i, x) ≤ ∑_{i<N} g(i, y)`. Unlike `Analysis/PowerSums.sum_le`, the two sums may read
  different parameters, which is what is needed to compare one body at two thresholds.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem add_le_add₂ {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a + c) (b + d) := by
  refine le_of_eq_add (d := monus b a + monus d c) ?_
  ipra_lc natEq (eq_add_of_le h₁) + natEq (eq_add_of_le h₂)

/-- Sums of pointwise smaller bodies are smaller, with possibly different parameters. -/
theorem sum_le_params (f g : PTm 2) (x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (sumF f) (var 0) (Syn.shift x)) (ap2 (sumF g) (var 0) (Syn.shift y))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simpa using .impI (le_congr (sum_zero (Γ := le zero N :: Γ) f x).eqSymm
        (sum_zero (Γ := le zero N :: Γ) g y).eqSymm (le_refl _))
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have hf := h.allOpen
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ le (ap2 (sumF f) (var 0) (Syn.shift x)) (ap2 (sumF g) (var 0) (Syn.shift y))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      exact le_congr (sum_succ' f (var 0) _).eqSymm (sum_succ' g (var 0) _).eqSymm
        (add_le_add₂ (Prf.impE Prf.hyp1 hle) (Prf.impE hf.wk.wk Prf.hyp0))
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

end LeanProofs.IPRA
