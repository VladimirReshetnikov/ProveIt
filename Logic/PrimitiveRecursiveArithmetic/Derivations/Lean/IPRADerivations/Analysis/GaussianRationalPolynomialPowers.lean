import IPRADerivations.Analysis.GaussianPolynomialDeterminantTerms
import IPRADerivations.Analysis.GaussianRationalFiberVandermonde
import IPRADerivations.Analysis.GaussianRationalMonicReconstruction
import IPRADerivations.Analysis.GaussianRationalReciprocal

/-!
# Actual numerical powers of stored Gaussian-rational polynomials

The finite-composition step of Gamma (C4) needs the actual coefficients
of `H_d(X)^k`.  The existing polynomial-product recursor is reused on an
actual numerical table containing the original coefficient buffer in
every cell.  No additional polynomial-product recursion is introduced.

Every numerical powerPrefix up to the original cap has its true coefficient
convolution with the ORIGINAL buffer, and its Horner value is the actual
scalar power.  The only shape premise is the original buffer length.
These are literal polynomial powers, not a formal Bell coefficient alias;
the logarithm specialization and exponential sum remain separate adapters.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialPowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (evaluate)
open GaussianRationalSyntheticDivision (canonicalCoefficients qmul_congr)
open GaussianRationalMonicReduction (evaluate_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tableBody : PTm 3 := var 2
def table (C K : PTm n) : PTm n := GaussianRationalFiberVandermonde.table tableBody K K C
def powerPrefix (C N K j : PTm n) : PTm n := GaussianPolynomialDeterminantTerms.stage (table C K) K N zero j
def power (C N K : PTm n) : PTm n := powerPrefix C N K K

@[simp] theorem subst_table {m : ℕ} (σ : Fin n → PTm m) (C K : PTm n) :
    Syn.subst σ (table C K) = table (Syn.subst σ C) (Syn.subst σ K) := by simp [table]
@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (C N K j : PTm n) :
    Syn.subst σ (powerPrefix C N K j) = powerPrefix (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) := by simp [powerPrefix]
@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (C N K : PTm n) :
    Syn.subst σ (power C N K) = power (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) := by simp [power]

theorem table_lookup (C K r j : PTm n) (hr : Γ ⊢[PRAAx] lt r K) (hj : Γ ⊢[PRAAx] lt j K) :
    Γ ⊢[PRAAx] GaussianPolynomialDeterminantTerms.cell (table C K) r j ≐ C := by
  simpa only [table,tableBody,Syn.subst_var,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    GaussianRationalFiberVandermonde.table_lookup (Γ := Γ) tableBody K K C r j hr hj

theorem table_shape (C N K : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] GaussianPolynomialDeterminantTerms.tableShape (table C K) K N := by
  refine .andI (GaussianRationalFiberVandermonde.table_length _ _ _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [table,Syn.shift,GaussianRationalFiberVandermonde.subst_table] using
      (GaussianRationalFiberVandermonde.table_row_length (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift)
        tableBody (Syn.shift K) (Syn.shift K) (Syn.shift C) (var 0) Prf.hyp0)
  · refine .allI (.impI (.allI (.impI ?_)))
    let Δ := lt (var 0) (Syn.shift (Syn.shift K)) ::
      (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift).map Fm.shift
    have hr : Δ ⊢[PRAAx] lt (Syn.shift (var 0 : PTm (n+1))) (Syn.shift (Syn.shift K)) := by
      simpa only [Δ,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var] using
        (Prf.hyp1 : Δ ⊢[PRAAx] Fm.shift (lt (var 0) (Syn.shift K)))
    have hc : Δ ⊢[PRAAx] length (Syn.shift (Syn.shift C)) ≐ succ (Syn.shift (Syn.shift N)) := by
      simpa only [Δ,List.map_cons,Syn.shift,Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
        ConciseIPRA.PTm.subst_succ] using hC.shift.shift.wk.wk
    simpa only [Δ,Syn.shift,GaussianPolynomialDeterminantTerms.subst_cell,subst_table,
      Foundations.SequenceComposition.subst_length,Foundations.SequenceComposition.length,
      ConciseIPRA.PTm.subst_succ,Syn.subst_var] using
      (congrFst (table_lookup (Γ := Δ) (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift K))
        (Syn.shift (var 0 : PTm (n+1))) (var 0) hr Prf.hyp0)).eqTrans hc

theorem factor_original (C K j : PTm n) (hj : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.factor (table C K) K zero j ≐ C :=
  table_lookup C K _ j (Foundations.RuntimePermutationWords.digit_bound K zero j hj) hj

theorem prefix_zero (C N K : PTm n) : Γ ⊢[PRAAx]
    powerPrefix C N K zero ≐ GaussianRationalMonicReduction.singleton GaussianRationalSyntheticDivision.qone :=
  GaussianPolynomialDeterminantTerms.stage_zero _ _ _ _

theorem prefix_succ (C N K j : PTm n) (hj : Γ ⊢[PRAAx] lt j K) : Γ ⊢[PRAAx]
    powerPrefix C N K (succ j) ≐ GaussianRationalPolynomialProduct.product (powerPrefix C N K j) C (j*N) N :=
  (GaussianPolynomialDeterminantTerms.stage_succ _ _ _ _ _).eqTrans
    (GaussianPolynomialDeterminantTerms.product_congr (.eqRefl _) (factor_original C K j hj) (.eqRefl _) (.eqRefl _))

theorem prefix_length (C N K j : PTm n) : Γ ⊢[PRAAx] length (powerPrefix C N K j) ≐ succ (j*N) :=
  GaussianPolynomialDeterminantTerms.stage_length _ _ _ _ _
theorem power_length (C N K : PTm n) : Γ ⊢[PRAAx] length (power C N K) ≐ succ (K*N) :=
  prefix_length _ _ _ _
theorem prefix_canonical (C N K j : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (powerPrefix C N K j) :=
  GaussianPolynomialDeterminantTerms.stage_canonical _ _ _ _ _
theorem power_canonical (C N K : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (power C N K) :=
  prefix_canonical _ _ _ _

/-- No coefficient-convolution law is a premise: this is the original
product constructor's bounded convolution of actual previous coefficients. -/
theorem prefix_coefficient_succ (C N K j s : PTm n) (hj : Γ ⊢[PRAAx] lt j K)
    (hs : Γ ⊢[PRAAx] le s (succ j*N)) : Γ ⊢[PRAAx]
    entry (powerPrefix C N K (succ j)) s ≐ GaussianRationalPolynomialProduct.coefficient
      (powerPrefix C N K j) C N (succ (j*N)) s :=
  (GaussianPolynomialDeterminantTerms.stage_coefficient_succ _ _ _ _ _ _ hs).eqTrans
    (GaussianRationalMonicReconstruction.coefficient_right_congr _ _ _ _ (factor_original C K j hj))

def scalarLaw (C N K z j : PTm n) : Fm PTm n := le j K ⟶
  GaussianPolynomialDeterminantTerms.scalarProduct (table C K) K N zero z j ≐
    GaussianRationalReciprocal.power (evaluate C z) j
@[simp] theorem subst_scalarLaw {m : ℕ} (σ : Fin n → PTm m) (C N K z j : PTm n) :
    (scalarLaw C N K z j).subst σ = scalarLaw
      (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ z) (Syn.subst σ j) := by simp [scalarLaw]

/-- A genuine guarded QF induction compares the SAME scalar fold with the
existing actual scalar power, retaining the original cap. -/
theorem scalar_prefix (C N K z j : PTm n) (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.scalarProduct (table C K) K N zero z j ≐
      GaussianRationalReciprocal.power (evaluate C z) j := by
  have all : Γ ⊢[PRAAx] .all (scalarLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift z) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_scalarLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((GaussianPolynomialDeterminantTerms.scalar_zero _ _ _ _ _).eqTrans
        (GaussianRationalReciprocal.power_zero _).eqSymm)
    · simp only [subst_scalarLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := le (succ (var 0)) (Syn.shift K) ::
        scalarLaw (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift z) (var 0) :: Γ.map Fm.shift
      have hk : Δ ⊢[PRAAx] lt (var 0) (Syn.shift K) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] GaussianPolynomialDeterminantTerms.scalarProduct
          (table (Syn.shift C) (Syn.shift K)) (Syn.shift K) (Syn.shift N) zero (Syn.shift z) (var 0) ≐
            GaussianRationalReciprocal.power (evaluate (Syn.shift C) (Syn.shift z)) (var 0) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      exact (GaussianPolynomialDeterminantTerms.scalar_succ _ _ _ _ _ _).eqTrans
        ((qmul_congr ih (evaluate_congr (factor_original _ _ _ hk) (.eqRefl _))).eqTrans
          (GaussianRationalReciprocal.power_succ _ _).eqSymm)
  have gate : Γ ⊢[PRAAx] scalarLaw C N K z j := by
    simpa only [subst_scalarLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE gate hj

theorem prefix_evaluation (C N K j z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hj : Γ ⊢[PRAAx] le j K) : Γ ⊢[PRAAx]
    evaluate (powerPrefix C N K j) z ≐ GaussianRationalReciprocal.power (evaluate C z) j :=
  (GaussianPolynomialDeterminantTerms.stage_evaluation _ _ _ _ _ _ (table_shape C N K hC) hj).eqTrans
    (scalar_prefix C N K z j hj)

theorem power_evaluation (C N K z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (power C N K) z ≐ GaussianRationalReciprocal.power (evaluate C z) K :=
  prefix_evaluation _ _ _ _ _ hC (le_refl _)

def prefixF : PR 4 := PTm.toPR (powerPrefix (var 0) (var 1) (var 2) (var 3))
def powerF : PR 3 := PTm.toPR (power (var 0) (var 1) (var 2))
def prefixRun (C N K j : PTm n) : PTm n := PTm.app prefixF ![C,N,K,j]
def run (C N K : PTm n) : PTm n := PTm.app powerF ![C,N,K]
@[simp] theorem subst_prefixRun {m : ℕ} (σ : Fin n → PTm m) (C N K j : PTm n) :
    Syn.subst σ (prefixRun C N K j) = prefixRun
      (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ j) := by
  simp only [prefixRun,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N K : PTm n) :
    Syn.subst σ (run C N K) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem prefix_program_at (C N K j : PTm n) : Γ ⊢[PRAAx] prefixRun C N K j ≐ powerPrefix C N K j := by
  simpa [prefixRun,prefixF] using toPR_eq (Γ := Γ)
    (powerPrefix (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,K,j]
theorem program_at (C N K : PTm n) : Γ ⊢[PRAAx] run C N K ≐ power C N K := by
  simpa [run,powerF] using toPR_eq (Γ := Γ) (power (var 0) (var 1) (var 2) : PTm 3) ![C,N,K]
theorem returned_length (C N K : PTm n) : Γ ⊢[PRAAx] length (run C N K) ≐ succ (K*N) :=
  (congrFst (program_at C N K)).eqTrans (power_length _ _ _)
theorem returned_canonical (C N K : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (run C N K) :=
  GaussianRationalMonicReduction.canonical_coefficients_congr (program_at _ _ _) (power_canonical _ _ _)
theorem returned_evaluation (C N K z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (run C N K) z ≐ GaussianRationalReciprocal.power (evaluate C z) K :=
  (evaluate_congr (program_at C N K) (.eqRefl _)).eqTrans (power_evaluation C N K z hC)

theorem actual_polynomial_power_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (power (var 0) (var 1) (var 2)) ≐ succ (var 2*var 1) ⋏
      canonicalCoefficients (power (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (power_length _ _ _) (power_canonical _ _ _))
theorem actual_polynomial_power_prefix_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (powerPrefix (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 3*var 1) ⋏
      canonicalCoefficients (powerPrefix (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (prefix_length _ _ _ _) (prefix_canonical _ _ _ _))
theorem actual_polynomial_power_prefix_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ le (var 3) (var 2) ⟶
      evaluate (powerPrefix (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        GaussianRationalReciprocal.power (evaluate (var 0) (var 4)) (var 3)) :=
  closeUniv 5 (.impI (.impI (prefix_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_polynomial_power_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 2) ⟶ le (var 4) (succ (var 3)*var 1) ⟶
      entry (powerPrefix (var 0) (var 1) (var 2) (succ (var 3))) (var 4) ≐
        GaussianRationalPolynomialProduct.coefficient (powerPrefix (var 0) (var 1) (var 2) (var 3))
          (var 0) (var 1) (succ (var 3*var 1)) (var 4)) :=
  closeUniv 5 (.impI (.impI (prefix_coefficient_succ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_polynomial_power_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (power (var 0) (var 1) (var 2)) (var 3) ≐
        GaussianRationalReciprocal.power (evaluate (var 0) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (power_evaluation _ _ _ _ Prf.hyp0))
theorem actual_polynomial_power_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) ≐ power (var 0) (var 1) (var 2) ⋏
      prefixRun (var 0) (var 1) (var 2) (var 3) ≐ powerPrefix (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.andI (program_at _ _ _) (prefix_program_at _ _ _ _))
theorem actual_returned_polynomial_power_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (run (var 0) (var 1) (var 2)) ≐ succ (var 2*var 1) ⋏
      canonicalCoefficients (run (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (returned_length _ _ _) (returned_canonical _ _ _))
theorem actual_returned_polynomial_power_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶
      evaluate (run (var 0) (var 1) (var 2)) (var 3) ≐
        GaussianRationalReciprocal.power (evaluate (var 0) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (returned_evaluation _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialPowers
