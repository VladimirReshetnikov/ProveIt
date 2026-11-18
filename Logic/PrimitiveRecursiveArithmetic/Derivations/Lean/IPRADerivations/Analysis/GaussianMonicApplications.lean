import IPRADerivations.Analysis.GaussianMonicRD
import IPRADerivations.Analysis.GaussianApproximateFactorization

/-!
# Concrete monic approximate roots and approximate factorizations

The fixed, proved GaussianMonicRD.step is used by the actual finite clock
and deflation programs. Their original monic polynomial and rational
precision guards suffice: neither RD nor an external step contract is an
input. The roots, product polynomial, coefficient error and returned
program fields are the original actual programs instantiated at this step.
All coefficient lists, degrees, precisions and evaluation points are
internal numerical variables.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicApplications

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianMonicRD (step)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1 (coefficientNorm subCoefficients)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def approximateRoot (C N p q : PTm n) : PTm n := GaussianDescentClock.approximateRoot step N C p q
/-- This reuses the clock's actual PR4, whose original input order is N,C,p,q. -/
def rootF : PR 4 := GaussianDescentClock.approximateRootF step
def rootRun (C N p q : PTm n) : PTm n := GaussianDescentClock.run step N C p q
def rootList (C N p q : PTm n) : PTm n := GaussianApproximateFactorization.rootList step C N p q
def productPolynomial (C N p q : PTm n) : PTm n := GaussianApproximateFactorization.productPolynomial step C N p q
def coefficientError (C N p q : PTm n) : PTm n := GaussianApproximateFactorization.coefficientError step C N p q
def output (C N p q : PTm n) : PTm n := GaussianApproximateFactorization.output step C N p q
def outputF : PR 4 := GaussianApproximateFactorization.outputF step
def run (C N p q : PTm n) : PTm n := GaussianApproximateFactorization.run step C N p q

@[simp] theorem subst_approximateRoot {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (approximateRoot C N p q) = approximateRoot (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by simp [approximateRoot]
@[simp] theorem subst_rootRun {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (rootRun C N p q) = rootRun (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [rootRun,GaussianDescentClock.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_rootList {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (rootList C N p q) = rootList (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by simp [rootList]
@[simp] theorem subst_productPolynomial {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (productPolynomial C N p q) = productPolynomial (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by simp [productPolynomial]
@[simp] theorem subst_coefficientError {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (coefficientError C N p q) = coefficientError (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by simp [coefficientError]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (output C N p q) = output (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N p q : PTm n) :
    Syn.subst σ (run C N p q) = run (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [run,GaussianApproximateFactorization.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem local_rd (C N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone) : Γ ⊢[PRAAx]
    GaussianDescentClock.localRD step N C :=
  GaussianFactorParameters.monic_rd_at step N C GaussianMonicRD.monic_rd hN hC hm

/-- The actual initial base and finite iteration clock are computed by
the root program; the input contains no descent or residual premise. -/
theorem approximate_root (C N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    GaussianDescentClock.result C (approximateRoot C N p q) p q :=
  GaussianDescentClock.approximate_root step N C p q (local_rd C N hN hC hm) hp hq

theorem root_program_at (C N p q : PTm n) : Γ ⊢[PRAAx] rootRun C N p q ≐ approximateRoot C N p q :=
  GaussianDescentClock.program_at step N C p q
theorem root_program_correct (C N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    GaussianDescentClock.result C (rootRun C N p q) p q :=
  GaussianDescentClock.program_correct step N C p q (local_rd C N hN hC hm) hp hq

theorem rootList_length (C N p q : PTm n) : Γ ⊢[PRAAx] length (rootList C N p q) ≐ N :=
  GaussianApproximateFactorization.rootList_length step C N p q
theorem product_length (C N p q : PTm n) : Γ ⊢[PRAAx] length (productPolynomial C N p q) ≐ succ N :=
  GaussianApproximateFactorization.product_length step C N p q
theorem product_evaluation (C N p q y : PTm n) : Γ ⊢[PRAAx]
    evaluate (productPolynomial C N p q) y ≐ GaussianRationalReconstruction.product (rootList C N p q) N y :=
  GaussianApproximateFactorization.product_evaluation step C N p q y

/-- The literal reconstructed product of the actual N returned roots
has the source coefficient-error bound p/q. -/
theorem approximate_factorization (C N p q : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hN : Γ ⊢[PRAAx] le one N) (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    length (rootList C N p q) ≐ N ⋏
      RationalArgmin.rationalLE (coefficientError C N p q) (GaussianFactorBudget.eta p q) :=
  GaussianApproximateFactorization.approximate_factorization step C N p q GaussianMonicRD.monic_rd hC hm hN hp hpq

theorem program_at (C N p q : PTm n) : Γ ⊢[PRAAx] run C N p q ≐ output C N p q :=
  GaussianApproximateFactorization.program_at step C N p q
theorem returned_roots (C N p q : PTm n) : Γ ⊢[PRAAx] fstT (run C N p q) ≐ rootList C N p q :=
  GaussianApproximateFactorization.returned_roots step C N p q
theorem returned_polynomial (C N p q : PTm n) : Γ ⊢[PRAAx] sndT (run C N p q) ≐ productPolynomial C N p q :=
  GaussianApproximateFactorization.returned_polynomial step C N p q
theorem returned_product_evaluation (C N p q y : PTm n) : Γ ⊢[PRAAx]
    evaluate (sndT (run C N p q)) y ≐ GaussianRationalReconstruction.product (fstT (run C N p q)) N y :=
  GaussianApproximateFactorization.returned_product_evaluation step C N p q y

theorem program_correct (C N p q : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hN : Γ ⊢[PRAAx] le one N) (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    length (fstT (run C N p q)) ≐ N ⋏
      (length (sndT (run C N p q)) ≐ succ N ⋏
        RationalArgmin.rationalLE (coefficientNorm (subCoefficients C (sndT (run C N p q)) (succ N)))
          (GaussianFactorBudget.eta p q)) :=
  GaussianApproximateFactorization.program_correct step C N p q GaussianMonicRD.monic_rd hC hm hN hp hpq

theorem concrete_monic_approximate_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶
      le one (var 2) ⟶ le one (var 3) ⟶
        GaussianDescentClock.result (var 0) (rootRun (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (root_program_correct _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem concrete_monic_approximate_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶ le one (var 1) ⟶
      le one (var 2) ⟶ le (var 2) (var 3) ⟶
        (length (rootList (var 0) (var 1) (var 2) (var 3)) ≐ var 1 ⋏
          RationalArgmin.rationalLE (coefficientError (var 0) (var 1) (var 2) (var 3)) (GaussianFactorBudget.eta (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (approximate_factorization _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem concrete_returned_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ entry (var 0) zero ≐ qone ⟶ le one (var 1) ⟶
      le one (var 2) ⟶ le (var 2) (var 3) ⟶
        (length (fstT (run (var 0) (var 1) (var 2) (var 3))) ≐ var 1 ⋏
          (length (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ succ (var 1) ⋏
            RationalArgmin.rationalLE (coefficientNorm (subCoefficients (var 0)
              (sndT (run (var 0) (var 1) (var 2) (var 3))) (succ (var 1)))) (GaussianFactorBudget.eta (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (program_correct _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem concrete_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (evaluate (productPolynomial (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      GaussianRationalReconstruction.product (rootList (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4)) :=
  closeUniv 5 (product_evaluation _ _ _ _ _)
theorem concrete_returned_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (evaluate (sndT (run (var 0) (var 1) (var 2) (var 3))) (var 4) ≐
      GaussianRationalReconstruction.product (fstT (run (var 0) (var 1) (var 2) (var 3))) (var 1) (var 4)) :=
  closeUniv 5 (returned_product_evaluation _ _ _ _ _)
theorem concrete_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app rootF ![var 1,var 0,var 2,var 3] ≐ approximateRoot (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (root_program_at _ _ _ _)
theorem concrete_factorization_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app outputF ![var 0,var 1,var 2,var 3] ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianMonicApplications
