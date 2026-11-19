import IPRADerivations.Analysis.GaussianRationalFiniteProduct
import IPRADerivations.Foundations.RuntimeAdjacentPermutationSwap
import IPRADerivations.Analysis.GaussianPolynomialDeterminantTerms

/-!
# Actual adjacent Gaussian products and the original determinant fold

The shared numerical adjacent-position reader supplies the actual swapped
factor stream. Bounded prefix and suffix congruence, two literal recurrence
steps and Gaussian commutativity prove product equality with only the
legitimate adjacent-position guard. Raw factors remain inside qmul.

A separate genuine QF recurrence proof identifies the SAME existing
determinant scalarProduct with the generic product of its actual evaluated
factors. Every matrix, dimension, word, width, query, count and datum is
numerical. No table-shape, index-range, evaluator or product law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalAdjacentProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct
  (qprod product_zero product_succ product_index_congr product_canonical product_congr_bounded
    product_split product_singleton offset_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Reuse the shared actual tau reader; no second position-swap program. -/
def swapBody (t : PTm 2) : PTm 2 := Foundations.RuntimeAdjacentPermutationSwap.sumSwapBody t

theorem swap_body_at (t : PTm 2) (k i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (swapBody t) i (pairT k x) ≐ inst2 t (Foundations.RuntimeAdjacentPermutationSwap.tau k i) x :=
  Foundations.RuntimeAdjacentPermutationSwap.sum_swap_body_at t k i x

/-- Two raw factors are both under the actual normalizing multiplication. -/
theorem product_two (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx]
    qprod t two x ≐ qmul (inst2 t zero x) (inst2 t one x) :=
  (product_succ t one x).eqTrans ((qmul_congr (product_singleton t x) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _))

theorem product_prefix (t : PTm 2) (k x : PTm n) : Γ ⊢[PRAAx]
    qprod (swapBody t) k (pairT k x) ≐ qprod t k x := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT] using
    (swap_body_at (Γ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift) t (Syn.shift k) (var 0) (Syn.shift x)).eqTrans
      (congrInst2 t (Foundations.RuntimeAdjacentPermutationSwap.tau_before _ _ Prf.hyp0) (.eqRefl _))

theorem product_middle (t : PTm 2) (k x : PTm n) : Γ ⊢[PRAAx]
    qprod (offB (swapBody t)) two (pairT k (pairT k x)) ≐ qprod (offB t) two (pairT k x) := by
  have left := (offset_at (Γ := Γ) (swapBody t) k zero (pairT k x)).eqTrans
    ((swap_body_at t k (k+zero) x).eqTrans (congrInst2 t
      ((Foundations.RuntimeAdjacentPermutationSwap.tau_congr (.eqRefl _) (add_zero _)).eqTrans
        (Foundations.RuntimeAdjacentPermutationSwap.tau_left _)) (.eqRefl _)))
  have right := (offset_at (Γ := Γ) (swapBody t) k one (pairT k x)).eqTrans
    ((swap_body_at t k (k+one) x).eqTrans (congrInst2 t
      ((Foundations.RuntimeAdjacentPermutationSwap.tau_congr (.eqRefl _) (succ_eq_add_one _).eqSymm).eqTrans
        (Foundations.RuntimeAdjacentPermutationSwap.tau_right _)) (.eqRefl _)))
  have originalLeft := (offset_at (Γ := Γ) t k zero x).eqTrans (congrInst2 t (add_zero _) (.eqRefl _))
  have originalRight := (offset_at (Γ := Γ) t k one x).eqTrans (congrInst2 t (succ_eq_add_one _).eqSymm (.eqRefl _))
  exact (product_two _ _).eqTrans ((qmul_congr left right).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((qmul_congr originalLeft originalRight).eqSymm.eqTrans (product_two _ _).eqSymm)))

theorem product_suffix (t : PTm 2) (k M x : PTm n) : Γ ⊢[PRAAx]
    qprod (offB (swapBody t)) M (pairT (k+two) (pairT k x)) ≐ qprod (offB t) M (pairT (k+two) x) := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have after : Δ ⊢[PRAAx] le (succ (succ (Syn.shift k))) (Syn.shift k+two+var 0) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_add_right (Syn.shift k+two) (var 0))
  have actual := (offset_at (Γ := Δ) (swapBody t) (Syn.shift k+two) (var 0) (pairT (Syn.shift k) (Syn.shift x))).eqTrans
    ((swap_body_at t (Syn.shift k) (Syn.shift k+two+var 0) (Syn.shift x)).eqTrans
      ((congrInst2 t (Foundations.RuntimeAdjacentPermutationSwap.tau_after _ _ after) (.eqRefl _)).eqTrans
        (offset_at t (Syn.shift k+two) (var 0) (Syn.shift x)).eqSymm))
  simpa only [Δ,Syn.shift,subst_pairT,PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using actual

theorem product_three_segments (t : PTm 2) (A B C x : PTm n) : Γ ⊢[PRAAx]
    qprod t (A+B+C) x ≐ qmul (qmul (qprod t A x) (qprod (offB t) B (pairT A x)))
      (qprod (offB t) C (pairT (A+B) x)) :=
  (product_split t (A+B) C x).eqTrans (qmul_congr (product_split t A B x) (.eqRefl _))

/-- The only input is that both exchanged positions occur in the prefix. -/
theorem adjacent_product (t : PTm 2) (N k x : PTm n) (hk : Γ ⊢[PRAAx] lt (succ k) N) : Γ ⊢[PRAAx]
    qprod (swapBody t) N (pairT k x) ≐ qprod t N x := by
  let M := monus N (succ (succ k))
  have span : Γ ⊢[PRAAx] N ≐ k+two+M := (eq_add_of_le hk).eqTrans (by ipra_ring)
  exact (product_index_congr (swapBody t) span (.eqRefl _)).eqTrans
    ((product_three_segments _ k two M (pairT k x)).eqTrans
      ((qmul_congr (qmul_congr (product_prefix _ _ _) (product_middle _ _ _)) (product_suffix _ _ _ _)).eqTrans
        ((product_three_segments t k two M x).eqSymm.eqTrans (product_index_congr t span.eqSymm (.eqRefl _)))))

/-- The existing determinant factor reader remains the original producer. -/
def evaluatedFactorBody : PTm 2 := evaluate
  (inst2 GaussianPolynomialDeterminantTerms.factorBody (var 0) (fstT (var 1))) (sndT (var 1))
def factorData (M m L w z : PTm n) : PTm n := pairT (GaussianPolynomialDeterminantTerms.data M m L w) z
@[simp] theorem subst_factorData {l : ℕ} (σ : Fin n → PTm l) (M m L w z : PTm n) :
    Syn.subst σ (factorData M m L w z) = factorData (Syn.subst σ M) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ z) := by simp [factorData]

theorem evaluated_factor_at (M m L w z j : PTm n) : Γ ⊢[PRAAx]
    inst2 evaluatedFactorBody j (factorData M m L w z) ≐ evaluate (GaussianPolynomialDeterminantTerms.factor M m w j) z := by
  have entrySyntax : Syn.subst ![j,factorData M m L w z]
      (Syn.subst ![var 0,fstT (var 1)] GaussianPolynomialDeterminantTerms.factorBody) =
      inst2 GaussianPolynomialDeterminantTerms.factorBody j (fstT (factorData M m L w z)) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext i
    fin_cases i <;> simp
  simp only [evaluatedFactorBody,inst2,GaussianRationalHorner.subst_evaluate,subst_inst2,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,entrySyntax]
  exact GaussianRationalMonicReduction.evaluate_congr
    ((congrInst2 GaussianPolynomialDeterminantTerms.factorBody (.eqRefl _)
      (fst_pair (GaussianPolynomialDeterminantTerms.data M m L w) z)).eqTrans
        (GaussianPolynomialDeterminantTerms.factor_body_at M m L w j))
    (snd_pair (GaussianPolynomialDeterminantTerms.data M m L w) z)

def scalarLaw (M m L w z j : PTm n) : Fm PTm n :=
  qprod evaluatedFactorBody j (factorData M m L w z) ≐ GaussianPolynomialDeterminantTerms.scalarProduct M m L w z j
@[simp] theorem subst_scalarLaw {l : ℕ} (σ : Fin n → PTm l) (M m L w z j : PTm n) :
    (scalarLaw M m L w z j).subst σ = scalarLaw (Syn.subst σ M) (Syn.subst σ m)
      (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ z) (Syn.subst σ j) := by
  simp only [scalarLaw,Fm.subst_eq,GaussianRationalFiniteProduct.subst_qprod,subst_factorData,
    GaussianPolynomialDeterminantTerms.subst_scalarProduct]

theorem scalar_zero (M m L w z : PTm n) : Γ ⊢[PRAAx] scalarLaw M m L w z zero :=
  (product_zero _ _).eqTrans (GaussianPolynomialDeterminantTerms.scalar_zero M m L w z).eqSymm
theorem scalar_step (M m L w z j : PTm n) (ih : Γ ⊢[PRAAx] scalarLaw M m L w z j) : Γ ⊢[PRAAx]
    scalarLaw M m L w z (succ j) :=
  (product_succ _ _ _).eqTrans ((qmul_congr ih (evaluated_factor_at M m L w z j)).eqTrans
    (GaussianPolynomialDeterminantTerms.scalar_succ M m L w z j).eqSymm)

/-- All six arguments are numerical; no table or evaluation contract enters. -/
theorem scalar_fold (M m L w z j : PTm n) : Γ ⊢[PRAAx]
    qprod evaluatedFactorBody j (factorData M m L w z) ≐ GaussianPolynomialDeterminantTerms.scalarProduct M m L w z j := by
  have all : Γ ⊢[PRAAx] .all (scalarLaw (Syn.shift M) (Syn.shift m) (Syn.shift L)
      (Syn.shift w) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_scalarLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact scalar_zero _ _ _ _ _
    · simp only [subst_scalarLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact scalar_step _ _ _ _ _ _ Prf.hyp0
  have actual : Γ ⊢[PRAAx] scalarLaw M m L w z j := by
    simpa only [subst_scalarLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact actual

theorem scalar_product_as_qprod (M m L w z j : PTm n) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.scalarProduct M m L w z j ≐ qprod evaluatedFactorBody j (factorData M m L w z) :=
  (scalar_fold M m L w z j).eqSymm

def output (t : PTm 2) (N k x : PTm n) : PTm n := pairT (qprod (swapBody t) N (pairT k x)) (qprod t N x)
def outputF (t : PTm 2) : PR 3 := PTm.toPR (output t (var 0) (var 1) (var 2))
def run (t : PTm 2) (N k x : PTm n) : PTm n := ap3 (outputF t) N k x
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N k x : PTm n) :
    Syn.subst σ (output t N k x) = output t (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (N k x : PTm n) :
    Syn.subst σ (run t N k x) = run t (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ x) := by simp only [run,subst_ap3]
theorem program_at (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx] run t N k x ≐ output t N k x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output t (var 0) (var 1) (var 2) : PTm 3) ![N,k,x]
theorem returned_swapped (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx] fstT (run t N k x) ≐ qprod (swapBody t) N (pairT k x) :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_original (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx] sndT (run t N k x) ≐ qprod t N x :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_equal (t : PTm 2) (N k x : PTm n) (hk : Γ ⊢[PRAAx] lt (succ k) N) : Γ ⊢[PRAAx]
    fstT (run t N k x) ≐ sndT (run t N k x) :=
  (returned_swapped _ _ _ _).eqTrans ((adjacent_product _ _ _ _ hk).eqTrans (returned_original _ _ _ _).eqSymm)
theorem returned_swapped_canonical (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx] canonical (fstT (run t N k x)) :=
  GaussianRationalHorner.canonical_congr (returned_swapped _ _ _ _) (product_canonical _ _ _)
theorem returned_original_canonical (t : PTm 2) (N k x : PTm n) : Γ ⊢[PRAAx] canonical (sndT (run t N k x)) :=
  GaussianRationalHorner.canonical_congr (returned_original _ _ _ _) (product_canonical _ _ _)

theorem actual_adjacent_product_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 1)) (var 0) ⟶ qprod (swapBody t) (var 0) (pairT (var 1) (var 2)) ≐ qprod t (var 0) (var 2)) :=
  closeUniv 3 (.impI (adjacent_product _ _ _ _ Prf.hyp0))
theorem product_three_segments_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (qprod t (var 0+var 1+var 2) (var 3) ≐
      qmul (qmul (qprod t (var 0) (var 3)) (qprod (offB t) (var 1) (pairT (var 0) (var 3))))
        (qprod (offB t) (var 2) (pairT (var 0+var 1) (var 3)))) := closeUniv 4 (product_three_segments _ _ _ _ _)
theorem original_scalar_fold_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianPolynomialDeterminantTerms.scalarProduct (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      qprod evaluatedFactorBody (var 5) (factorData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (scalar_product_as_qprod _ _ _ _ _ _)
theorem actual_adjacent_product_program_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run t (var 0) (var 1) (var 2) ≐ output t (var 0) (var 1) (var 2)) ⋏
      ((fstT (run t (var 0) (var 1) (var 2)) ≐ qprod (swapBody t) (var 0) (pairT (var 1) (var 2))) ⋏
        sndT (run t (var 0) (var 1) (var 2)) ≐ qprod t (var 0) (var 2))) :=
  closeUniv 3 (.andI (program_at _ _ _ _) (.andI (returned_swapped _ _ _ _) (returned_original _ _ _ _)))
theorem returned_adjacent_product_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (succ (var 1)) (var 0) ⟶ fstT (run t (var 0) (var 1) (var 2)) ≐ sndT (run t (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (returned_equal _ _ _ _ Prf.hyp0))
theorem returned_canonical_products_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (fstT (run t (var 0) (var 1) (var 2))) ⋏ canonical (sndT (run t (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (returned_swapped_canonical _ _ _ _) (returned_original_canonical _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalAdjacentProduct
