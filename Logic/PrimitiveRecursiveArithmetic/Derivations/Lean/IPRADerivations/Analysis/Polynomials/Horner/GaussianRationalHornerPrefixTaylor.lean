import IPRADerivations.Analysis.Polynomials.GaussianShrinkingPolynomialTail

/-!
# Exact shrinking Taylor tails for an original Horner prefix

The stored coefficient list may be longer than the evaluated polynomial.
The finite conservation identity uses the actual Horner count, while its
norm bound uses the original full coefficient mass. No false exact list
length premise is needed when the zero constant of P has been dropped.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHornerPrefixTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (horner hornerF qadd qmul)
open GaussianRationalPowerExpansion (conservationLeft remaining remaining_zero remaining_succ remaining_before partialSum prefix_zero prefix_succ)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalReciprocal (power power_zero power_succ bound_congr)
open GaussianFiniteLogarithmCompositionTail (highPart)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianEuclideanDistanceName (fraction)
open RationalArgmin (rationalLE)
open GaussianCoefficientL1 (coefficientNorm)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def conservationLaw (C N w m : PTm n) : Fm PTm n := le m (succ N) ⟶
  conservationLeft C N w m ≐ horner C w (succ N)
@[simp] theorem subst_conservationLaw {l : ℕ} (σ : Fin n → PTm l) (C N w m : PTm n) :
    (conservationLaw C N w m).subst σ = conservationLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ w) (Syn.subst σ m) := by
  simp [conservationLaw]

theorem conservation_zero (C N w : PTm n) : Γ ⊢[PRAAx]
    conservationLeft C N w zero ≐ horner C w (succ N) :=
  (qadd_congr (qmul_congr (congrAp3 hornerF (remaining_zero N) (.eqRefl _) (.eqRefl _)) (power_zero w))
    (prefix_zero C N w)).eqTrans
    ((qadd_congr (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)) (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.horner_canonical _ _ _)))

theorem conservation_step (C N w m : PTm n) (hm : Γ ⊢[PRAAx] le m N)
    (ih : Γ ⊢[PRAAx] conservationLeft C N w m ≐ horner C w (succ N)) : Γ ⊢[PRAAx]
    conservationLeft C N w (succ m) ≐ horner C w (succ N) := by
  have oldH : Γ ⊢[PRAAx] horner C w (remaining N m) ≐
      qadd (qmul (horner C w (monus N m)) w) (GaussianBalancedRadiusSyntax.coefficient C N m) :=
    (congrAp3 hornerF (remaining_before N m hm) (.eqRefl _) (.eqRefl _)).eqTrans
      (GaussianRationalHorner.horner_succ C w (monus N m))
  have oldExchange := (qadd_congr (qmul_congr oldH (.eqRefl _)) (.eqRefl _)).eqTrans
    (GaussianRationalSumAlgebra.horner_sum_exchange (horner C w (monus N m)) w
      (GaussianBalancedRadiusSyntax.coefficient C N m) (power w m) (partialSum C N w m))
  have newExchange : Γ ⊢[PRAAx] conservationLeft C N w (succ m) ≐
      qadd (qmul (horner C w (monus N m)) (qmul (power w m) w))
        (qadd (partialSum C N w m) (GaussianOffDominantTerms.term C N w m)) :=
    qadd_congr (qmul_congr (congrAp3 hornerF (remaining_succ N m) (.eqRefl _) (.eqRefl _))
      (power_succ w m)) (prefix_succ C N w m hm)
  exact newExchange.eqTrans (oldExchange.eqSymm.eqTrans ih)

/-- Original guarded atomic QF induction, with arbitrary stored list length. -/
theorem conservation (C N w m : PTm n) (hm : Γ ⊢[PRAAx] le m (succ N)) : Γ ⊢[PRAAx]
    conservationLeft C N w m ≐ horner C w (succ N) := by
  have all : Γ ⊢[PRAAx] .all (conservationLaw (Syn.shift C) (Syn.shift N) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_conservationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (conservation_zero C N w).wk
    · simp only [subst_conservationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact conservation_step _ _ _ _ ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] conservationLaw C N w m := by
    simpa only [subst_conservationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m
  exact .impE rule hm

theorem tail_identity (C N d w : PTm n) (hd : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    qsub (horner C w (succ N)) (partialSum C N w (succ d)) ≐ highPart C N d w := by
  have split := conservation C N w (succ d) ((succ_monus_succ _ _).eqTrans hd)
  have form : Γ ⊢[PRAAx] conservationLeft C N w (succ d) ≐
      qadd (highPart C N d w) (partialSum C N w (succ d)) :=
    qadd_congr (qmul_congr (congrAp3 hornerF (remaining_succ N d) (.eqRefl _) (.eqRefl _)) (.eqRefl _)) (.eqRefl _)
  exact (GaussianRationalSyntheticDivision.qsub_congr (split.eqSymm.eqTrans form) (.eqRefl _)).eqTrans
    (GaussianReciprocalHorner.qsub_add_cancel _ _ (GaussianRationalHorner.qmul_canonical _ _))

theorem original_prefix_tail (C N d w A B a b : PTm n)
    (hCount : Γ ⊢[PRAAx] le (succ N) (length C)) (hd : Γ ⊢[PRAAx] le d N)
    (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le a b)
    (hNorm : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (fraction A B))
    (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (horner C w (succ N)) (partialSum C N w (succ d))
      (A*pw a (succ d)) (B*pw b (succ d)) := by
  have headBound := GaussianRationalUnitDiskHornerNorm.unit_prefix_bound C w (monus N d) A B hB hNorm
    (GaussianShrinkingPolynomialTail.shrinking_disk_unit w a b hb hab hw)
    (le_trans (GaussianMonicResidualRadius.monus_le_left N d) (le_trans (le_succ_self N) hCount))
  have bound := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB (GaussianFactorBudget.power_positive b (succ d) hb)
    headBound (GaussianRationalReciprocal.bounded_power w a b (succ d) hb hw)
  exact bound_congr (tail_identity C N d w hd).eqSymm (.eqRefl _) (.eqRefl _) bound

theorem actual_original_horner_prefix_shrinking_taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (succ (var 1)) (length (var 0)) ⟶ le (var 2) (var 1) ⟶ le one (var 5) ⟶ le one (var 7) ⟶
      le (var 6) (var 7) ⟶ rationalLE (coefficientNorm (var 0)) (fraction (var 4) (var 5)) ⟶
      bounded (var 3) (var 6) (var 7) ⟶
      distanceBounded (horner (var 0) (var 3) (succ (var 1))) (partialSum (var 0) (var 1) (var 3) (succ (var 2)))
        (var 4*pw (var 6) (succ (var 2))) (var 5*pw (var 7) (succ (var 2)))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (original_prefix_tail _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk.wk Prf.hyp1.wk.wk.wk.wk
      Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))))

end LeanProofs.IPRA.Analysis.GaussianRationalHornerPrefixTaylor
