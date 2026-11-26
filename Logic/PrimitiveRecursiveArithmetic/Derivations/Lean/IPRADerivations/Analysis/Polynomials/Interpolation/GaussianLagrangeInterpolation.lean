import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalFiberRightInverse
import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianRationalGridCoefficientEquality
import IPRADerivations.Analysis.Polynomials.Elimination.Bivariate.GaussianBivariatePowerExpansion
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual finite Lagrange recovery on the numerical natural grid

The original observations are read at 0,...,N. Their actual Lagrange
cardinal coefficient sums form a computed coefficient buffer. Finite
sum interchange and the original cardinal evaluations establish its
grid values; the genuine finite-grid coefficient theorem then recovers
each original coefficient. No interpolation identity is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianLagrangeInterpolation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate qmul canonical)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalFiniteSum (sum sum_index_congr sum_congr_bounded)
open GaussianRationalFiniteGridIdentity (grid gridPoint grid_length grid_lookup grid_distinct)
open GaussianRationalLagrangeCardinals (inverseCoefficient)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (C N e : PTm n) : PTm n := pairT C (pairT N e)
def observation (C s : PTm n) : PTm n := evaluate C (gridPoint s)
def cell (C N e s : PTm n) : PTm n :=
  qmul (observation C s) (inverseCoefficient (grid N) e s)
def cellBody : PTm 2 := cell (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def coefficient (C N e : PTm n) : PTm n := sum cellBody (succ N) (data C N e)
def polynomialBody : PTm 2 := coefficient (fstT (var 1)) (sndT (var 1)) (monus (sndT (var 1)) (var 0))
def polynomial (C N : PTm n) : PTm n := sequence polynomialBody (succ N) (pairT C N)
def matrixCell (C N z e s : PTm n) : PTm n := qmul (power z e) (cell C N e s)
def matrixBody : PTm 3 := matrixCell (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (C N e : PTm n) :
    Syn.subst σ (data C N e) = data (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) := by simp [data]
@[simp] theorem subst_observation {l : ℕ} (σ : Fin n → PTm l) (C s : PTm n) :
    Syn.subst σ (observation C s) = observation (Syn.subst σ C) (Syn.subst σ s) := by simp [observation]
@[simp] theorem subst_cell {l : ℕ} (σ : Fin n → PTm l) (C N e s : PTm n) :
    Syn.subst σ (cell C N e s) = cell (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) (Syn.subst σ s) := by simp [cell]
@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (C N e : PTm n) :
    Syn.subst σ (coefficient C N e) = coefficient (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ e) := by simp [coefficient]
@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (C N : PTm n) :
    Syn.subst σ (polynomial C N) = polynomial (Syn.subst σ C) (Syn.subst σ N) := by simp [polynomial]
@[simp] theorem subst_matrixCell {l : ℕ} (σ : Fin n → PTm l) (C N z e s : PTm n) :
    Syn.subst σ (matrixCell C N z e s) = matrixCell (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ e) (Syn.subst σ s) := by simp [matrixCell]

theorem cell_congr {C D N M e f s t : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (hN : Γ ⊢[PRAAx] N ≐ M) (he : Γ ⊢[PRAAx] e ≐ f) (hs : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx]
    cell C N e s ≐ cell D M f t := by
  ipra_congr (cell (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hC, hN, he, hs]
theorem coefficient_congr {C D N M e f : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (hN : Γ ⊢[PRAAx] N ≐ M) (he : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx]
    coefficient C N e ≐ coefficient D M f := by
  ipra_congr (coefficient (var 0) (var 1) (var 2) : PTm 3) with [hC, hN, he]
theorem cell_body_at (C N e s : PTm n) : Γ ⊢[PRAAx] inst2 cellBody s (data C N e) ≐ cell C N e s := by
  simp only [cellBody,inst2,subst_cell,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact cell_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)
theorem polynomial_body_at (C N i : PTm n) : Γ ⊢[PRAAx]
    inst2 polynomialBody i (pairT C N) ≐ coefficient C N (monus N i) := by
  simp only [polynomialBody,inst2,subst_coefficient,PTm.subst_monus,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact coefficient_congr (fst_pair _ _) (snd_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _))
theorem polynomial_length (C N : PTm n) : Γ ⊢[PRAAx] length (polynomial C N) ≐ succ N := sequence_length _ _ _
theorem polynomial_lookup (C N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (polynomial C N) i ≐ coefficient C N (monus N i) :=
  (sequence_decode polynomialBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (polynomial_body_at _ _ _)
theorem polynomial_exponent (C N e : PTm n) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    entry (polynomial C N) (monus N e) ≐ coefficient C N e :=
  (polynomial_lookup _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    (coefficient_congr (.eqRefl _) (.eqRefl _) (GaussianRationalMonicReconstruction.complement _ _ he))

theorem matrix_body_at (C N z e s : PTm n) : Γ ⊢[PRAAx]
    inst3 matrixBody e s (data C N z) ≐ matrixCell C N z e s := by
  simp only [matrixBody,inst3,subst_matrixCell,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact qmul_congr (congrAp2 powerF (.eqRefl _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
    (cell_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _) (.eqRefl _))

theorem matrix_row (C N z e : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row matrixBody e (succ N) (data C N z) ≐ qmul (power z e) (coefficient C N e) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalFubini.rowBody matrixBody)
      (GaussianRationalFiniteSum.multiplyBody cellBody) (succ N) (pairT e (data C N z))
      (pairT (power z e) (data C N e)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data,GaussianRationalReciprocal.subst_power,subst_pairT,ConciseIPRA.PTm.subst_succ] using
      (GaussianRationalFubini.row_entry (Γ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) matrixBody _ _ _).eqTrans
        ((matrix_body_at _ _ _ _ _).eqTrans
          ((GaussianRationalFiniteSum.multiply_body_at cellBody _ _ _).eqTrans
            (qmul_congr (.eqRefl _) (cell_body_at _ _ _ _))).eqSymm)
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianRationalFiniteSum.sum_multiply _ _ _ _)

theorem evaluation_rows (C N z : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial C N) z ≐ GaussianRationalFubini.rowFirst matrixBody (succ N) (succ N) (data C N z) := by
  refine (GaussianBivariatePowerExpansion.evaluate_power_sum _ _ _ (polynomial_length C N)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have eqv : Δ ⊢[PRAAx] inst2 GaussianRationalPowerExpansion.termBody (var 0)
      (GaussianRationalPowerExpansion.data (polynomial (Syn.shift C) (Syn.shift N)) (Syn.shift N) (Syn.shift z)) ≐
      inst2 (GaussianRationalFubini.rowSumBody matrixBody) (var 0)
        (pairT (succ (Syn.shift N)) (data (Syn.shift C) (Syn.shift N) (Syn.shift z))) :=
    (GaussianRationalPowerExpansion.term_body_at _ _ _ _).eqTrans
      ((qmul_congr (polynomial_exponent _ _ _ bound) (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          ((matrix_row _ _ _ _).eqSymm.eqTrans (GaussianRationalFubini.row_sum_at matrixBody _ _ _).eqSymm)))
  simpa only [Δ,Syn.shift,subst_polynomial,GaussianRationalPowerExpansion.subst_data,subst_data,subst_pairT,ConciseIPRA.PTm.subst_succ] using eqv

theorem matrix_column (C N z s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column matrixBody s (succ N) (data C N z) ≐
      qmul (observation C s) (GaussianRationalLagrangeCardinals.coefficientEvaluation (grid N) s z) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalFubini.columnBody matrixBody)
      (GaussianRationalFiniteSum.multiplyBody GaussianRationalLagrangeCardinals.evaluationBody) (succ N)
      (pairT s (data C N z))
      (pairT (observation C s) (GaussianRationalLagrangeCardinals.evaluationData (grid N) s z)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
    have algebra : Δ ⊢[PRAAx] matrixCell (Syn.shift C) (Syn.shift N) (Syn.shift z) (var 0) (Syn.shift s) ≐
        qmul (observation (Syn.shift C) (Syn.shift s))
          (GaussianRationalLagrangeCardinals.coefficientTerm (grid (Syn.shift N)) (Syn.shift s) (Syn.shift z) (var 0)) :=
      (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
        ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
          (GaussianReciprocalHorner.qmul_associative _ _ _))
    have term : Δ ⊢[PRAAx] inst2 (GaussianRationalFubini.columnBody matrixBody) (var 0)
        (pairT (Syn.shift s) (data (Syn.shift C) (Syn.shift N) (Syn.shift z))) ≐
        inst2 (GaussianRationalFiniteSum.multiplyBody GaussianRationalLagrangeCardinals.evaluationBody) (var 0)
          (pairT (observation (Syn.shift C) (Syn.shift s))
            (GaussianRationalLagrangeCardinals.evaluationData (grid (Syn.shift N)) (Syn.shift s) (Syn.shift z))) :=
      (GaussianRationalFubini.column_entry matrixBody _ _ _).eqTrans ((matrix_body_at _ _ _ _ _).eqTrans
        (algebra.eqTrans ((GaussianRationalFiniteSum.multiply_body_at GaussianRationalLagrangeCardinals.evaluationBody _ _ _).eqTrans
          (qmul_congr (.eqRefl _) (GaussianRationalLagrangeCardinals.evaluation_body_at _ _ _ _))).eqSymm))
    simpa only [Δ,Syn.shift,subst_data,subst_observation,subst_pairT,GaussianRationalLagrangeCardinals.subst_evaluationData,
      GaussianRationalFiniteGridIdentity.subst_grid,ConciseIPRA.PTm.subst_succ] using term
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr _ (grid_length N).eqSymm (.eqRefl _)).eqTrans
      (GaussianRationalFiniteSum.sum_multiply _ _ _ _))

theorem column_grid (C N j s : PTm n) (hj : Γ ⊢[PRAAx] le j N) (hs : Γ ⊢[PRAAx] le s N) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column matrixBody s (succ N) (data C N (gridPoint j)) ≐
      qmul (GaussianRationalFiberVandermonde.delta j s) (observation C s) := by
  have jr : Γ ⊢[PRAAx] lt j (length (grid N)) :=
    lt_congr (.eqRefl _) (grid_length N).eqSymm ((succ_monus_succ _ _).eqTrans hj)
  have sr : Γ ⊢[PRAAx] lt s (length (grid N)) :=
    lt_congr (.eqRefl _) (grid_length N).eqSymm ((succ_monus_succ _ _).eqTrans hs)
  have cardinalValue : Γ ⊢[PRAAx] GaussianRationalLagrangeCardinals.coefficientEvaluation (grid N) s (gridPoint j) ≐
      GaussianRationalFiberVandermonde.delta j s :=
    (GaussianRationalLagrangeCardinals.coefficient_evaluation _ _ _ sr).eqTrans
      ((GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (grid_lookup N j ((succ_monus_succ _ _).eqTrans hj)).eqSymm).eqTrans
        (GaussianRationalLagrangeCardinals.cardinal_evaluation _ _ _ (grid_distinct N) sr jr))
  exact (matrix_column _ _ _ _).eqTrans ((qmul_congr (.eqRefl _) cardinalValue).eqTrans
    (GaussianRationalPowerAlgebra.qmul_commutative _ _))

def observationBody : PTm 2 := observation (var 1) (var 0)
theorem observation_body_at (C s : PTm n) : Γ ⊢[PRAAx] inst2 observationBody s C ≐ observation C s := by
  simp only [observationBody,inst2,subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact .eqRefl _

theorem interpolation_grid (C N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    evaluate (polynomial C N) (gridPoint j) ≐ observation C j := by
  have js : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hj.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalFubini.columnSumBody matrixBody)
      (GaussianRationalMatrixFiniteSums.deltaBody observationBody) (succ N)
      (pairT (succ N) (data C N (gridPoint j))) (pairT j C) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (GaussianRationalFubini.columnSumBody matrixBody) (var 0)
        (pairT (succ (Syn.shift N)) (data (Syn.shift C) (Syn.shift N) (gridPoint (Syn.shift j)))) ≐
        inst2 (GaussianRationalMatrixFiniteSums.deltaBody observationBody) (var 0) (pairT (Syn.shift j) (Syn.shift C)) :=
      (GaussianRationalFubini.column_sum_at matrixBody _ _ _).eqTrans
        ((column_grid _ _ _ _ js.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)).eqTrans
          ((GaussianRationalMatrixFiniteSums.delta_body_at observationBody _ _ _).eqTrans
            (qmul_congr (.eqRefl _) (observation_body_at _ _))).eqSymm)
    simpa only [Δ,Syn.shift,subst_pairT,subst_data,GaussianRationalFiniteGridIdentity.subst_gridPoint,ConciseIPRA.PTm.subst_succ] using e
  exact (evaluation_rows _ _ _).eqTrans ((GaussianRationalFubini.fubini matrixBody _ _ _).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
      ((GaussianRationalMatrixFiniteSums.sum_delta_canonical observationBody _ _ _
        ((succ_monus_succ _ _).eqTrans hj)
        (GaussianRationalHorner.canonical_congr (observation_body_at _ _) (GaussianRationalHorner.horner_canonical _ _ _))).eqTrans
          (observation_body_at _ _))))

theorem original_coefficient (C N e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    GaussianTranslatedNonconstant.recode (entry C (monus N e)) ≐ coefficient C N e := by
  have values : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual C (polynomial C N) N := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_polynomial,observation] using
      (interpolation_grid (Syn.shift C) (Syn.shift N) (var 0) Prf.hyp0).eqSymm
  exact (GaussianRationalGridCoefficientEquality.coefficient_recode_equal C (polynomial C N) N (monus N e)
    hC (polynomial_length C N) values (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      ((GaussianTranslatedNonconstant.recode_congr (polynomial_exponent C N e he)).eqTrans
        (GaussianTranslatedNonconstant.recode_eq _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem actual_finite_grid_Lagrange_coefficient_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (var 0) ≐ succ (var 1)) ⟶ le (var 2) (var 1) ⟶
      GaussianTranslatedNonconstant.recode (entry (var 0) (monus (var 1) (var 2))) ≐ coefficient (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_coefficient _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLagrangeInterpolation
