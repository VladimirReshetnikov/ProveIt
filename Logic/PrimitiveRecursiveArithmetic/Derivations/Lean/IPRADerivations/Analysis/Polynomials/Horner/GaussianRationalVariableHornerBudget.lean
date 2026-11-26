import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerLipschitz
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNormalization
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual coefficient-dependent Horner size and variation budgets

One positive original common denominator clears the original coefficients.
An actual paired natural recursion accumulates size and derivative budgets.
Guarded QF inductions follow the existing Horner recursion; neither a
uniform coefficient bound nor a desired slope/output law is a premise.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianRationalVariableHornerBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (horner evaluate represents positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalNormalization (clearPoint)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (C : PTm n) : PTm n := GaussianRationalNormalization.denominator C
def coefficient (C i : PTm n) : PTm n := GaussianL1.norm1 (clearPoint C i)
def data (C U : PTm n) : PTm n := pairT C U
def stepBody : PTm 3 := pairT
  (sndT (var 2)*fstT (var 1)+coefficient (fstT (var 2)) (var 0))
  (sndT (var 2)*sndT (var 1)+fstT (var 1))
def stateF : PR 2 := rec2 (pairT zero zero : PTm 1) stepBody
def state (C U k : PTm n) : PTm n := ap2 stateF k (data C U)
def size (C U k : PTm n) : PTm n := fstT (state C U k)
def variation (C U k : PTm n) : PTm n := sndT (state C U k)
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (C : PTm n) : Syn.subst σ (denominator C) = denominator (Syn.subst σ C) := by simp [denominator]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (C i : PTm n) : Syn.subst σ (coefficient C i) = coefficient (Syn.subst σ C) (Syn.subst σ i) := by simp [coefficient]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C U : PTm n) : Syn.subst σ (data C U) = data (Syn.subst σ C) (Syn.subst σ U) := by simp [data]
@[simp] theorem subst_state {l : ℕ} (σ : Fin n → PTm l) (C U k : PTm n) : Syn.subst σ (state C U k) = state (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ k) := by simp [state]
@[simp] theorem subst_size {l : ℕ} (σ : Fin n → PTm l) (C U k : PTm n) : Syn.subst σ (size C U k) = size (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ k) := by simp [size]
@[simp] theorem subst_variation {l : ℕ} (σ : Fin n → PTm l) (C U k : PTm n) : Syn.subst σ (variation C U k) = variation (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ k) := by simp [variation]

theorem denominator_positive (C : PTm n) : Γ ⊢[PRAAx] le one (denominator C) := GaussianRationalNormalization.denominator_positive C
theorem coefficient_congr {C D i j : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hi : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx] coefficient C i ≐ coefficient D j := by
  ipra_congr (coefficient (var 0) (var 1) : PTm 2) with [hC, hi]

theorem state_zero (C U : PTm n) : Γ ⊢[PRAAx] state C U zero ≐ pairT zero zero := by
  simpa [state,stateF] using rec2_zero (Γ := Γ) (pairT zero zero : PTm 1) stepBody (data C U)
theorem state_succ (C U k : PTm n) : Γ ⊢[PRAAx] state C U (succ k) ≐
    pairT (U*size C U k+coefficient C k) (U*variation C U k+size C U k) := by
  have h := rec2_succ (Γ := Γ) (pairT zero zero : PTm 1) stepBody k (data C U)
  simp only [stepBody,subst_pairT,PTm.subst_add,PTm.subst_mul,subst_coefficient,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h
  exact h.eqTrans (congrPairT
    (congrAdd (congrMul (snd_pair _ _) (.eqRefl _)) (coefficient_congr (fst_pair _ _) (.eqRefl _)))
    (congrAdd (congrMul (snd_pair _ _) (.eqRefl _)) (.eqRefl _)))
theorem size_zero (C U : PTm n) : Γ ⊢[PRAAx] size C U zero ≐ zero :=
  (congrFst (state_zero C U)).eqTrans (fst_pair _ _)
theorem variation_zero (C U : PTm n) : Γ ⊢[PRAAx] variation C U zero ≐ zero :=
  (congrSnd (state_zero C U)).eqTrans (snd_pair _ _)
theorem size_succ (C U k : PTm n) : Γ ⊢[PRAAx] size C U (succ k) ≐ U*size C U k+coefficient C k :=
  (congrFst (state_succ C U k)).eqTrans (fst_pair _ _)
theorem variation_succ (C U k : PTm n) : Γ ⊢[PRAAx] variation C U (succ k) ≐ U*variation C U k+size C U k :=
  (congrSnd (state_succ C U k)).eqTrans (snd_pair _ _)
theorem variation_index_congr (C U : PTm n) {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx] variation C U k ≐ variation C U l :=
  congrSnd (congrAp2 stateF h (.eqRefl _))

theorem coefficient_represents (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    represents (entry C i) (clearPoint C i) (denominator C) := GaussianRationalNormalization.clearPoint_clearing C i _ hi (.eqRefl _)
theorem coefficient_bound (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    bounded (entry C i) (coefficient C i) (denominator C) := by
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (denominator_positive C) (denominator_positive C) (coefficient_represents C i hi)
  exact le_congr (by ipra_ring) (.eqRefl _)
    (mul_le_mul_right (denominator C*denominator C) (GaussianL1.normSq_le_norm1_square (clearPoint C i)))

def sizeLaw (C U w k : PTm n) : Fm PTm n := le k (length C) ⟶ bounded (horner C w k) (size C U k) (denominator C)
@[simp] theorem subst_sizeLaw {l : ℕ} (σ : Fin n → PTm l) (C U w k : PTm n) :
    (sizeLaw C U w k).subst σ = sizeLaw (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ w) (Syn.subst σ k) := by simp [sizeLaw]

theorem size_base (C U w : PTm n) : Γ ⊢[PRAAx] bounded (horner C w zero) (size C U zero) (denominator C) :=
  bound_congr (GaussianRationalHorner.horner_zero C w).eqSymm (size_zero C U).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero (denominator C) (denominator_positive C))
theorem size_step (C U w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hk : Γ ⊢[PRAAx] lt k (length C)) (ih : Γ ⊢[PRAAx] bounded (horner C w k) (size C U k) (denominator C)) : Γ ⊢[PRAAx]
    bounded (horner C w (succ k)) (size C U (succ k)) (denominator C) := by
  have product := bounded_product _ _ _ _ _ _ (denominator_positive C) (le_refl one) ih hw
  have product' := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] denominator C*one ≐ denominator C) product
  have sum := bounded_sum_same _ _ _ _ _ (denominator_positive C) product' (coefficient_bound C k hk)
  have value : Γ ⊢[PRAAx] size C U k*U+coefficient C k ≐ size C U (succ k) :=
    (by ipra_ring : Γ ⊢[PRAAx] size C U k*U+coefficient C k ≐ U*size C U k+coefficient C k).eqTrans (size_succ C U k).eqSymm
  exact bound_congr (GaussianRationalHorner.horner_succ C w k).eqSymm value (.eqRefl _) sum

theorem size_prefix (C U w k : PTm n) (hw : Γ ⊢[PRAAx] bounded w U one) (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    bounded (horner C w k) (size C U k) (denominator C) := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift U) one := by simpa [Fm.shift,Syn.shift,one] using hw.shift
  have all : Γ ⊢[PRAAx] .all (sizeLaw (Syn.shift C) (Syn.shift U) (Syn.shift w) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (size_base C U w).wk
    · simp only [subst_sizeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact size_step _ _ _ _ shifted.wk.wk Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] sizeLaw C U w k := by simpa only [subst_sizeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

def variationLaw (C U z w p q k : PTm n) : Fm PTm n := le k (length C) ⟶
  distanceBounded (horner C z k) (horner C w k) (variation C U k*p) (denominator C*q)
@[simp] theorem subst_variationLaw {l : ℕ} (σ : Fin n → PTm l) (C U z w p q k : PTm n) :
    (variationLaw C U z w p q k).subst σ = variationLaw (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ z) (Syn.subst σ w)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) := by simp [variationLaw]

theorem variation_base (C U z w p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    distanceBounded (horner C z zero) (horner C w zero) (variation C U zero*p) (denominator C*q) :=
  GaussianRationalDistanceOrder.distance_congr (GaussianRationalHorner.horner_zero C z).eqSymm
    (GaussianRationalHorner.horner_zero C w).eqSymm
    ((congrMul (variation_zero C U) (.eqRefl p)).eqTrans (zero_mul p)).eqSymm (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero _ _ (positive_product _ _ (denominator_positive C) hq))

theorem variation_step (C U z w p q k : PTm n) (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) (hk : Γ ⊢[PRAAx] lt k (length C))
    (ih : Γ ⊢[PRAAx] distanceBounded (horner C z k) (horner C w k) (variation C U k*p) (denominator C*q)) : Γ ⊢[PRAAx]
    distanceBounded (horner C z (succ k)) (horner C w (succ k)) (variation C U (succ k)*p) (denominator C*q) := by
  have positive := positive_product _ _ (denominator_positive (Γ := Γ) C) hq
  have first := bounded_product _ _ _ _ _ _ positive (le_refl one) ih hz
  have first' := bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] (denominator C*q)*one ≐ denominator C*q) first
  have second := bounded_product _ _ _ _ _ _ (denominator_positive C) hq (size_prefix C U w k hw (le_of_lt hk)) hzw
  have sum := bounded_sum_same _ _ _ _ _ positive first' second
  have value : Γ ⊢[PRAAx] (variation C U k*p)*U+size C U k*p ≐ variation C U (succ k)*p :=
    (by ipra_ring : Γ ⊢[PRAAx] (variation C U k*p)*U+size C U k*p ≐ (U*variation C U k+size C U k)*p).eqTrans
      (congrMul (variation_succ C U k).eqSymm (.eqRefl p))
  exact bound_congr (GaussianRationalHornerLipschitz.horner_query_difference_succ C z w k).eqSymm value (.eqRefl _) sum

theorem variation_prefix (C U z w p q k : PTm n) (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one)
    (hq : Γ ⊢[PRAAx] le one q) (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) (hk : Γ ⊢[PRAAx] le k (length C)) : Γ ⊢[PRAAx]
    distanceBounded (horner C z k) (horner C w k) (variation C U k*p) (denominator C*q) := by
  have zs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift U) one := by simpa [Fm.shift,Syn.shift,one] using hz.shift
  have ws : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift U) one := by simpa [Fm.shift,Syn.shift,one] using hw.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift q) := by simpa [Fm.shift,Syn.shift,one] using hq.shift
  have zw : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z) (Syn.shift w) (Syn.shift p) (Syn.shift q) := by simpa [Fm.shift,Syn.shift] using hzw.shift
  have all : Γ ⊢[PRAAx] .all (variationLaw (Syn.shift C) (Syn.shift U) (Syn.shift z) (Syn.shift w) (Syn.shift p) (Syn.shift q) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_variationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (variation_base C U z w p q hq).wk
    · simp only [subst_variationLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact variation_step _ _ _ _ _ _ _ zs.wk.wk ws.wk.wk qs.wk.wk zw.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] variationLaw C U z w p q k := by simpa only [subst_variationLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem evaluation_bound (C N U z w p q : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hz : Γ ⊢[PRAAx] bounded z U one) (hw : Γ ⊢[PRAAx] bounded w U one) (hq : Γ ⊢[PRAAx] le one q)
    (hzw : Γ ⊢[PRAAx] distanceBounded z w p q) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C z) (evaluate C w) (variation C U (succ N)*p) (denominator C*q) :=
  GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (congrMul (variation_index_congr C U hLen) (.eqRefl p)) (.eqRefl _)
    (variation_prefix C U z w p q (length C) hz hw hq hzw (le_refl _))

def output (C U k : PTm n) : PTm n := pairT (size C U k) (pairT (variation C U k) (denominator C))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C U k : PTm n) : PTm n := ap3 outputF C U k
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C U k : PTm n) :
    Syn.subst σ (output C U k) = output (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ k) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C U k : PTm n) :
    Syn.subst σ (run C U k) = run (Syn.subst σ C) (Syn.subst σ U) (Syn.subst σ k) := by simp [run]
theorem program_at (C U k : PTm n) : Γ ⊢[PRAAx] run C U k ≐ output C U k := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,U,k]
theorem returned_size (C U k : PTm n) : Γ ⊢[PRAAx] fstT (run C U k) ≐ size C U k :=
  (congrFst (program_at C U k)).eqTrans (fst_pair _ _)
theorem returned_variation (C U k : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C U k)) ≐ variation C U k :=
  (congrFst (congrSnd (program_at C U k))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem returned_denominator (C U k : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run C U k)) ≐ denominator C :=
  (congrSnd (congrSnd (program_at C U k))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem actual_coefficient_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶ bounded (entry (var 0) (var 1)) (coefficient (var 0) (var 1)) (denominator (var 0))) :=
  closeUniv 2 (.impI (coefficient_bound _ _ Prf.hyp0))
theorem actual_budget_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((state (var 0) (var 1) zero ≐ pairT zero zero) ⋏
      state (var 0) (var 1) (succ (var 2)) ≐
        pairT (var 1*size (var 0) (var 1) (var 2)+coefficient (var 0) (var 2))
          (var 1*variation (var 0) (var 1) (var 2)+size (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (state_zero _ _) (state_succ _ _ _))
theorem actual_variable_size_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 2) (var 1) one ⟶ le (var 3) (length (var 0)) ⟶
      bounded (horner (var 0) (var 2) (var 3)) (size (var 0) (var 1) (var 3)) (denominator (var 0))) :=
  closeUniv 4 (.impI (.impI (size_prefix _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_variable_variation_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 5) ⟶ bounded (var 2) (var 1) one ⟶ bounded (var 3) (var 1) one ⟶
      distanceBounded (var 2) (var 3) (var 4) (var 5) ⟶ le (var 6) (length (var 0)) ⟶
        distanceBounded (horner (var 0) (var 2) (var 6)) (horner (var 0) (var 3) (var 6))
          (variation (var 0) (var 1) (var 6)*var 4) (denominator (var 0)*var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (variation_prefix _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_variable_horner_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 1) ⟶ bounded (var 3) (var 2) one ⟶ bounded (var 4) (var 2) one ⟶
      le one (var 6) ⟶ distanceBounded (var 3) (var 4) (var 5) (var 6) ⟶
        distanceBounded (evaluate (var 0) (var 3)) (evaluate (var 0) (var 4))
          (variation (var 0) (var 2) (succ (var 1))*var 5) (denominator (var 0)*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (evaluation_bound _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_variable_budget_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_size_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (bounded (var 2) (var 1) one ⟶ le (var 3) (length (var 0)) ⟶
      bounded (horner (var 0) (var 2) (var 3)) (fstT (run (var 0) (var 1) (var 3))) (sndT (sndT (run (var 0) (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.impI (bound_congr (.eqRefl _) (returned_size _ _ _).eqSymm (returned_denominator _ _ _).eqSymm
    (size_prefix _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalVariableHornerBudget
