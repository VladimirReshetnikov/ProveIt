import IPRADerivations.Core.Fubini
import IPRADerivations.Core.LinearCombination

/-!
# Square sums by L-shaped layers

Reusable: for a body `a(i, j, x)`, the sum over the square `i, j < M` is the sum of its L-shaped layers,

  `∑_{i<M} ∑_{j<M} a(i, j) = ∑_{b<M} (∑_{i<b} a(i, b) + ∑_{j<b} a(b, j) + a(b, b))`

(`square_layers`), by induction on `M`: the square of side `M + 1` adds the column `j = M` below the
diagonal, the row `i = M` left of it, and the corner (`square_step`). The square sum is
`∑_{i<M} oB a (i, ⟨M, x⟩)` with the row sums of `Core/Fubini`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

namespace SquareLayers

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The layer `∑_{i<b} a(i, b) + ∑_{j<b} a(b, j) + a(b, b)`, over `0 = b`, `1 = x`. -/
def LB (a : PTm 3) : PTm 2 :=
  ap2 (sumF (colB a)) (var 0) (pairT (var 0) (var 1)) + ap2 (sumF (rowB a)) (var 0) (pairT (var 0) (var 1)) +
    Syn.subst ![var 0, var 0, var 1] a

theorem inst2_LB (a : PTm 3) (b x : PTm n) :
    inst2 (LB a) b x = ap2 (sumF (colB a)) b (pairT b x) + ap2 (sumF (rowB a)) b (pairT b x) + inst3 a b b x := by
  simp only [inst2, LB, PTm.subst_add, subst_ap2, subst_pairT, Syn.subst_var, inst3, Syn.subst_subst]
  simp
  refine congrArg (fun t => _ + t) (congrArg (fun σ => Syn.subst σ a) ?_)
  funext k; fin_cases k <;> simp

/-- The square of side `M`. -/
abbrev Sq (a : PTm 3) (M x : PTm n) : PTm n := ap2 (sumF (oB a)) M (pairT M x)

/-- One layer: `Sq (M + 1) = Sq M + L(M)`. -/
theorem square_step (a : PTm 3) (M x : PTm n) :
    Γ ⊢[PRAAx] Sq a (succ M) x ≐ Sq a M x + inst2 (LB a) M x := by
  rw [inst2_LB]
  -- rows below `M` gain one column
  have s₂ : Γ ⊢[PRAAx] ap2 (sumF (oB a)) M (pairT (succ M) x) ≐
      ap2 (sumF (addBody (oB a) (colB a))) M (pairT M x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_oB, inst2_oB, inst2_colB, shift_pairT, shift_pairT, shift_succ'']
    refine (congrAp2 (sumF (rowB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((sum_succ' _ _ _).eqTrans ?_)
    rw [inst2_rowB]
    exact congrAdd (congrAp2 (sumF (rowB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
      (congrInst3 a (fst_pair _ _) (.eqRefl _) (snd_pair _ _) |>.eqTrans
        (congrInst3 a (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqSymm)
  -- the new row `i = M`
  have s₄ : Γ ⊢[PRAAx] inst2 (oB a) M (pairT (succ M) x) ≐
      ap2 (sumF (rowB a)) M (pairT M x) + inst3 a M M x := by
    rw [inst2_oB]
    refine (congrAp2 (sumF (rowB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((sum_succ' _ _ _).eqTrans (congrAdd (.eqRefl _) ?_))
    rw [inst2_rowB]
    exact congrInst3 a (fst_pair _ _) (.eqRefl _) (snd_pair _ _)
  ipra_lc natEq (sum_succ' (Γ := Γ) (oB a) M (pairT (succ M) x)) + natEq s₂ +
    natEq (sum_add (Γ := Γ) (oB a) (colB a) M (pairT M x)) + natEq s₄

/-- Variables: `0 = M`, `1 = x`. -/
private abbrev layersF (a : PTm 3) : Fm PTm 2 :=
  ap2 (sumF (oB a)) (var 0) (pairT (var 0) (var 1)) ≐ ap2 (sumF (LB a)) (var 0) (var 1)

private theorem layers₀ (a : PTm 3) : ([] : List (Fm PTm 2)) ⊢[PRAAx] layersF a := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero]
    exact (sum_zero _ _).eqTrans (sum_zero _ _).eqSymm
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact (square_step a (var 0) (var 1)).eqTrans
      ((congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (sum_succ' _ _ _).eqSymm)

/-- `∑_{i<M} ∑_{j<M} a(i, j, x) = ∑_{b<M} L(b, x)`. -/
theorem square_layers (a : PTm 3) (M x : PTm n) :
    Γ ⊢[PRAAx] Sq a M x ≐ ap2 (sumF (LB a)) M x := by
  have h := inst (Γ := Γ) (layers₀ a) (![M, x] : Fin 2 → PTm n)
  simpa using h

end SquareLayers

end LeanProofs.IPRA
