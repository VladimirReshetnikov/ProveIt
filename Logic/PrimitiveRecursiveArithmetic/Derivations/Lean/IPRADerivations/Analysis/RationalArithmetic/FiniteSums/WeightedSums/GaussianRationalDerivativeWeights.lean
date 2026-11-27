import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalVariableHornerBudget
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerExpansion
import IPRADerivations.Foundations.BoundedSyntaxBackwardInduction

/-!
# Exact coefficient-dependent derivative weights of the actual Horner budget

The original descending coefficient order is retained. An actual bounded
natural sum reads each original cleared coefficient with its numerical
power/degree weight. Guarded QF prefixSum conservation identifies that sum
with the actual paired Horner derivative budget. No weighted identity or
slope estimate is a premise, and no power is cancelled.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianRationalDerivativeWeights

open_ipra
open GaussianRationalVariableHornerBudget (coefficient size variation size_zero variation_zero size_succ variation_succ denominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (C N U i : PTm n) : PTm n := monus N i*coefficient C i*pw U (pred (monus N i))
def data (C N U : PTm n) : PTm n := pairT C (pairT N U)
def body : PTm 2 := weight (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def prefixSum (C N U k : PTm n) : PTm n := ap2 (sumF body) k (data C N U)
def total (C N U : PTm n) : PTm n := prefixSum C N U N

def conservation (C N U k : PTm n) : PTm n :=
  pw U (monus (succ N) k)*variation C U k+
    monus (succ N) k*pw U (monus N k)*size C U k
def prefixLaw (C N U k : PTm n) : Fm PTm n := le k N ⟶ prefixSum C N U k ≐ conservation C N U k
ipra_subst weight
ipra_subst data
@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (C N U k : PTm n) :
    Syn.subst σ (prefixSum C N U k) = prefixSum (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ k) := by simp [prefixSum]
ipra_subst total
ipra_subst conservation
ipra_subst prefixLaw

theorem weight_congr {C D N K U V i j : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ K)
    (hU : Γ ⊢[PRAAx] U ≐ V) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] weight C N U i ≐ weight D K V j := by
  ipra_congr (weight (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hC, hN, hU, hi]
theorem body_at (C N U i : PTm n) : Γ ⊢[PRAAx] inst2 body i (data C N U) ≐ weight C N U i := by
  simp only [body,inst2,subst_weight,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact weight_congr (fst_pair _ _) (snd_pair _ _).fstE
    (snd_pair _ _).sndE (.eqRefl _)
theorem prefix_zero (C N U : PTm n) : Γ ⊢[PRAAx] prefixSum C N U zero ≐ zero := sum_zero _ _
theorem prefix_succ (C N U k : PTm n) : Γ ⊢[PRAAx] prefixSum C N U (succ k) ≐ prefixSum C N U k+weight C N U k :=
  (sum_succ' body k (data C N U)).eqTrans (congrAdd (.eqRefl _) (body_at C N U k))

theorem conservation_zero (C N U : PTm n) : Γ ⊢[PRAAx] conservation C N U zero ≐ zero := by
  have b := natEq (size_zero (Γ := Γ) C U)
  have v := natEq (variation_zero (Γ := Γ) C U)
  apply deriveNat
  unfold conservation
  ipra_simps
  rw [b,v]
  ring

theorem conservation_step (C N U k : PTm n) (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx]
    conservation C N U (succ k) ≐ conservation C N U k+weight C N U k := by
  have old : Γ ⊢[PRAAx] monus (succ N) k ≐ succ (monus N k) :=
    GaussianRationalPowerExpansion.remaining_before N k (le_of_lt hk)
  have next : Γ ⊢[PRAAx] monus (succ N) (succ k) ≐ monus N k := succ_monus_succ _ _
  have rest := LeanProofs.IPRA.Foundations.BoundedSyntaxBackwardInduction.reverse_successor N k hk
  have predRest : Γ ⊢[PRAAx] pred (monus N k) ≐ monus N (succ k) :=
    (congrPred rest.eqSymm).eqTrans (pred_succ _)
  have powerOld := natEq ((congrAp2 powF old (.eqRefl U)).eqTrans (pw_succ U (monus N k)))
  have powerNext := natEq (congrAp2 powF next (.eqRefl U))
  have powerRest := natEq ((congrAp2 powF rest.eqSymm (.eqRefl U)).eqTrans (pw_succ U (monus N (succ k))))
  have powerPred := natEq (congrAp2 powF predRest (.eqRefl U))
  have oldValue := natEq old
  have b := natEq (size_succ (Γ := Γ) C U k)
  have v := natEq (variation_succ (Γ := Γ) C U k)
  apply deriveNat
  unfold conservation weight
  ipra_simps
  simp only [powerOld,powerNext,powerPred,powerRest,oldValue,natEq next,natEq rest.eqSymm,b,v]
  ring

theorem prefix_conservation (C N U k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    prefixSum C N U k ≐ conservation C N U k := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift U) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI ((prefix_zero C N U).eqTrans (conservation_zero C N U).eqSymm)
    · refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift N) :: prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift U) (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] prefixSum (Syn.shift C) (Syn.shift N) (Syn.shift U) (var 0) ≐
          conservation (Syn.shift C) (Syn.shift N) (Syn.shift U) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      exact (prefix_succ _ _ _ _).eqTrans ((congrAdd ih (.eqRefl _)).eqTrans
        (conservation_step _ _ _ _ (Prf.hyp0 : Δ ⊢[PRAAx] _)).eqSymm)
  have rule : Γ ⊢[PRAAx] prefixLaw C N U k := by simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem terminal_remaining (N : PTm n) : Γ ⊢[PRAAx] monus (succ N) N ≐ one :=
  (congrMonus (succ_eq_add_one N) (.eqRefl N)).eqTrans (add_monus' one N)

theorem conservation_terminal (C N U : PTm n) : Γ ⊢[PRAAx] conservation C N U N ≐ variation C U (succ N) := by
  have low := natEq ((congrAp2 powF (monus_self (Γ := Γ) N) (.eqRefl U)).eqTrans (pw_zero U))
  have index := natEq (terminal_remaining (Γ := Γ) N)
  have step := natEq (variation_succ (Γ := Γ) C U N)
  apply deriveNat
  unfold conservation
  ipra_simps
  rw [natEq ((congrAp2 powF (terminal_remaining (Γ := Γ) N) (.eqRefl U)).eqTrans (pw_one U)),low,index,step]
  ring

theorem derivative_identity (C N U : PTm n) : Γ ⊢[PRAAx] variation C U (succ N) ≐ total C N U :=
  (conservation_terminal C N U).eqSymm.eqTrans (prefix_conservation C N U N (le_refl _)).eqSymm


theorem evaluation_bound (C N U z w p q : PTm n)
    (hLen : Γ ⊢[PRAAx] Foundations.SequenceComposition.length C ≐ succ N)
    (hz : Γ ⊢[PRAAx] GaussianRationalMetric.bounded z U one)
    (hw : Γ ⊢[PRAAx] GaussianRationalMetric.bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q)
    (hzw : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded z w p q) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (GaussianRationalHorner.evaluate C z) (GaussianRationalHorner.evaluate C w)
      (total C N U*p) (denominator C*q) :=
  GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (congrMul (derivative_identity C N U) (.eqRefl p)) (.eqRefl _)
      (GaussianRationalVariableHornerBudget.evaluation_bound C N U z w p q hLen hz hw hq hzw)

def output (C N U : PTm n) : PTm n := pairT (total C N U) (pairT (variation C U (succ N)) (denominator C))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N U : PTm n) : PTm n := ap3 outputF C N U
ipra_subst output
ipra_subst run
theorem program_at (C N U : PTm n) : Γ ⊢[PRAAx] run C N U ≐ output C N U := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,U]
theorem returned_total (C N U : PTm n) : Γ ⊢[PRAAx] fstT (run C N U) ≐ total C N U :=
  (program_at C N U).fstE
theorem returned_variation (C N U : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N U)) ≐ variation C U (succ N) :=
  (congrFst (congrSnd (program_at C N U))).eqTrans (snd_pair _ _).fstE
theorem returned_denominator (C N U : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run C N U)) ≐ denominator C :=
  (congrSnd (congrSnd (program_at C N U))).eqTrans (snd_pair _ _).sndE
theorem returned_identity (C N U : PTm n) : Γ ⊢[PRAAx] fstT (run C N U) ≐ fstT (sndT (run C N U)) :=
  (returned_total C N U).eqTrans ((derivative_identity C N U).eqSymm.eqTrans (returned_variation C N U).eqSymm)

theorem actual_derivative_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inst2 body (var 3) (data (var 0) (var 1) (var 2)) ≐
      monus (var 1) (var 3)*coefficient (var 0) (var 3)*pw (var 2) (pred (monus (var 1) (var 3)))) :=
  closeUniv 4 (body_at _ _ _ _)
theorem actual_derivative_conservation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ prefixSum (var 0) (var 1) (var 2) (var 3) ≐ conservation (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (prefix_conservation _ _ _ _ Prf.hyp0))
theorem actual_derivative_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (variation (var 0) (var 2) (succ (var 1)) ≐ total (var 0) (var 1) (var 2)) :=
  closeUniv 3 (derivative_identity _ _ _)
theorem actual_derivative_lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (Foundations.SequenceComposition.length (var 0) ≐ succ (var 1) ⟶
      GaussianRationalMetric.bounded (var 3) (var 2) one ⟶ GaussianRationalMetric.bounded (var 4) (var 2) one ⟶
      le one (var 6) ⟶ GaussianRationalMetric.distanceBounded (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianRationalMetric.distanceBounded (GaussianRationalHorner.evaluate (var 0) (var 3))
        (GaussianRationalHorner.evaluate (var 0) (var 4)) (total (var 0) (var 1) (var 2)*var 5) (denominator (var 0)*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (evaluation_bound _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_derivative_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_derivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run (var 0) (var 1) (var 2)) ≐ fstT (sndT (run (var 0) (var 1) (var 2)))) ⋏
      sndT (sndT (run (var 0) (var 1) (var 2))) ≐ denominator (var 0)) :=
  closeUniv 3 (.andI (returned_identity _ _ _) (returned_denominator _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalDerivativeWeights
