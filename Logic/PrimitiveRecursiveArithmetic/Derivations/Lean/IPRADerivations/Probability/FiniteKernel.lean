import IPRADerivations.Probability.TowerCommonDen
import IPRADerivations.Probability.SignedParts

/-!
# The coded finite kernel: evaluator and natural-weight presentations

Packet: `probability/expected_value_ipra_2026-11-16`, Lemma `lem:pr-evaluator` and Theorem
`thm:weighted-average`.

* `pr_evaluator` (`lem:pr-evaluator`): the expectation numerator `Ew(X) = ∑_{i<M} w_i X_i` and the
  total `W` are primitive-recursive terms, and equality and order between two expectations
  `Ew(X)/W` and `Ev(Y)/V` are quantifier-free after clearing the positive denominators:
  `Ew(X) V ≐ Ev(Y) W` and `Ew(X) V ≤ Ev(Y) W` are `QF` formulas.
* `weighted_average` (`thm:weighted-average`, the converse): a finite rational probability vector
  `p_i = a_i / b_i` (`b_i ≥ 1`) with `∑ p_i = 1`, cleared over the common denominator
  `D = ∏_{j<M} b_j` as `∑_i a_i (D / b_i) = D`, has the natural-weight presentation
  `w_i = a_i (D / b_i)`: `W = ∑ w_i = D` and `w_i b_i = a_i W`, i.e. `p_i = w_i / W`
  (`TowerCommonDen.common_den`). The forward direction (`p_i = w_i/W ≥ 0`, `∑ p_i = 1`,
  `E[X] = ∑ p_i X_i`) is the definition of the cleared expectation.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.FiniteKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul')
open LeanProofs.IPRA.Probability.TowerCommonDen (common_den)
open LeanProofs.IPRA.Probability.SignedParts (sbq inst2_sbq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `lem:pr-evaluator`: cross-multiplied comparisons of two expectations are quantifier-free. -/
theorem pr_evaluator (w X v Y : PTm 2) (M x N y : PTm n) :
    (Ew w X M x * Wt v N y ≐ Ew v Y N y * Wt w M x).QF ∧
      (le (Ew w X M x * Wt v N y) (Ew v Y N y * Wt w M x)).QF :=
  ⟨trivial, le_QF _ _⟩

/-- The presenting weights `w_i = a_i (D / b_i)`, `D = ∏_{j < fst z} b_j`, over `0 = i`, `1 = z = ⟨M, x⟩`. -/
abbrev wB (a b : PTm 2) : PTm 2 := sbq a * quo (ap2 (prodF b) (fstT (var 1)) (sndT (var 1))) (sbq b)

theorem wB_at (a b : PTm 2) (i M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (wB a b) i (pairT M x) ≐ inst2 a i x * quo (ap2 (prodF b) M x) (inst2 b i x) := by
  rw [inst2_mul', inst2_sbq]
  have e : inst2 (quo (ap2 (prodF b) (fstT (var 1)) (sndT (var 1))) (sbq b)) i (pairT M x) =
      quo (ap2 (prodF b) (fstT (pairT M x)) (sndT (pairT M x))) (inst2 b i (sndT (pairT M x))) := by
    simp only [inst2, sbq, subst_ap2, subst_fstT, subst_sndT, Syn.subst_subst, Syn.subst_var]
    congr 1
    congr 1; funext k; fin_cases k <;> simp
  rw [e]
  exact congrMul (congrInst2 a (.eqRefl _) (snd_pair _ _))
    (congrAp2 quoF (congrAp2 (prodF b) (fst_pair _ _) (snd_pair _ _)) (congrInst2 b (.eqRefl _) (snd_pair _ _)))

/-- `thm:weighted-average`, converse: if `∑_i a_i (D / b_i) = D` (`∑ a_i / b_i = 1`), the weights
`w_i = a_i (D / b_i)` have total `W = D` and present `p_i = a_i / b_i = w_i / W`: `w_i b_i = a_i W`. -/
theorem weighted_average (a b : PTm 2) {M x : PTm n}
    (hb : Γ.map Fm.shift ⊢[PRAAx] inst2 b (var 0) (Syn.shift x) ≐ succ (pred (inst2 b (var 0) (Syn.shift x))))
    (hs : Γ ⊢[PRAAx] ap2 (sumF (wB a b)) M (pairT M x) ≐ ap2 (prodF b) M x) {i : PTm n} (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] (ap2 (sumF (wB a b)) M (pairT M x) ≐ ap2 (prodF b) M x) ⋏
      (inst2 (wB a b) i (pairT M x) * inst2 b i x ≐ inst2 a i x * ap2 (sumF (wB a b)) M (pairT M x)) :=
  .andI hs ((congrMul (wB_at a b i M x) (.eqRefl _)).eqTrans
    ((common_den a b hb hi).eqTrans (congrMul (.eqRefl _) hs.eqSymm)))

end LeanProofs.IPRA.Probability.FiniteKernel
