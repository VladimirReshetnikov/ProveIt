import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.BarnesInteger
import IPRADerivations.AnalyticNumberTheory.EtaSchedule
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# A lower-growth witness for the integer Barnes sequence

The finite superfactorial defining `barnes (4*m)` contains the block
`(3*m)!, …, (4*m-1)!`. For positive `m`, each factor in this block is at
least `(2*m)^m` by the factorial shift inequality. The resulting integer
witness is the cleared product estimate underlying the lower-growth
argument in Section 10 of the Barnes G paper.
-/

namespace LeanProofs.IPRA.Analysis.BarnesIntegerGrowth

open_ipra
open BarnesInteger (barnes barnes_pos barnes_succ facB)
open Products (fact)
open LeanProofs.IPRA.Common (mul_le_mul mul_one_right one_le_of_pos pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.EtaSchedule (fact_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

private abbrev blockLaw (a t : PTm n) : Fm PTm n :=
  le (pw (fact a) t) (barnes (a+t))

private theorem block_base (a : PTm n) : Γ ⊢[PRAAx] blockLaw a zero :=
  le_congr (pw_zero _).eqSymm
    (congrAp2 (prodF facB) (add_zero a) (.eqRefl zero)).eqSymm
    (one_le_of_pos (barnes_pos a))

private theorem block_step (a t : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (ih : Γ ⊢[PRAAx] blockLaw a t) : Γ ⊢[PRAAx] blockLaw a (succ t) := by
  have hp := one_le_of_pos (pw_pos' (pos_of_one_le ha) t)
  have hf : Γ ⊢[PRAAx] le (fact a) (fact (a+t)) :=
    le_trans
      (le_congr (mul_one_right _) (.eqRefl _)
        (mul_le_mul (le_refl (fact a)) hp))
      (fact_shift a t)
  have hstep : Γ ⊢[PRAAx] barnes (a+succ t) ≐ barnes (a+t)*fact (a+t) :=
    (congrAp2 (prodF facB) (add_succ a t) (.eqRefl zero)).eqTrans (barnes_succ (a+t))
  exact le_congr (pw_succ (fact a) t).eqSymm hstep.eqSymm (mul_le_mul ih hf)

/-- Every factor of the last `t` terms of `barnes (a+t)` is at least `a!`. -/
theorem factorial_block (a t : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le (pw (fact a) t) (barnes (a+t)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by
    simpa [Fm.shift, Syn.shift, one] using ha.shift
  have all : Γ ⊢[PRAAx] .all (blockLaw (Syn.shift a) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [blockLaw, subst_le, subst_ap2, PTm.subst_add, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] using block_base a
    · simp only [blockLaw, subst_le, subst_ap2, PTm.subst_add, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      exact block_step (Syn.shift a) (var 0) hs.wk Prf.hyp0
  simpa only [blockLaw, subst_le, subst_ap2, PTm.subst_add, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] using all.allE t

/-- The block of factorials from `3*m` through `4*m-1` yields the tiled witness. -/
theorem tiled_lower (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (pw (two*m) (m*m)) (barnes (num 4*m)) := by
  let a := two*m+m
  have ha : Γ ⊢[PRAAx] le one a := le_trans hm (le_add_left m (two*m))
  have hf : Γ ⊢[PRAAx] le (pw (two*m) m) (fact a) :=
    le_trans
      (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right _ (one_le_of_pos (fact_pos (two*m)))))
      (fact_shift (two*m) m)
  have endEq : Γ ⊢[PRAAx] a+m ≐ num 4*m := by dsimp [a]; ipra_ring
  exact le_congr (pw_mul (two*m) m m) (congrAp2 (prodF facB) endEq (.eqRefl zero))
    (le_trans (pw_le_pw m hf) (factorial_block a m ha))

/-- A lower witness with the smaller base `m` at the next index. -/
theorem witness_lower (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (pw m (m*m)) (barnes (succ (num 4*m))) := by
  let N := num 4*m
  have base : Γ ⊢[PRAAx] le m (two*m) := le_of_eq_add (d := m) (by ipra_ring)
  have next : Γ ⊢[PRAAx] le (barnes N) (barnes (succ N)) :=
    le_congr (mul_one_right _) (barnes_succ N).eqSymm
      (mul_le_mul (le_refl (barnes N)) (one_le_of_pos (fact_pos N)))
  exact le_trans (pw_le_pw (m*m) base) (le_trans (tiled_lower m hm) next)

theorem barnes_integer_tiled_lower_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (let m := var 0; le one m ⟶ le (pw (two*m) (m*m)) (barnes (num 4*m))) :=
  closeUniv 1 (.impI (tiled_lower _ Prf.hyp0))

theorem barnes_integer_witness_lower_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (let m := var 0; le one m ⟶ le (pw m (m*m)) (barnes (succ (num 4*m)))) :=
  closeUniv 1 (.impI (witness_lower _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.BarnesIntegerGrowth
