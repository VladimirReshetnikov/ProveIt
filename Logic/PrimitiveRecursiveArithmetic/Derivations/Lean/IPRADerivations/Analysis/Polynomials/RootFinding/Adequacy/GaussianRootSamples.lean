import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormEntries

/-!
# Actual sampled polynomials and root lists

The fixed PR3 evaluator a(i,s,x) supplies the original Gaussian-rational
coefficient names. The descending sample list has literal leading one and
coefficient i>0 equal to a(N-i,s,x). Source precision E(t) and its actual
power-of-two tolerance feed the checked uniform approximate factorizer.
All numerical degrees, radii, stages and persistent data are internal.
This constructs the source objects and their actual coefficient errors;
the common final radius and Hausdorff coherence are separate compositions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSamples

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N s x : PTm n) : PTm n := pairT N (pairT s x)
def sampleValue (a : PR 3) (i N s x : PTm n) : PTm n :=
  RationalArithmetic.select (sg i) qone (ap3 a (monus N i) s x)
def sampleBody (a : PR 3) : PTm 2 := sampleValue a (var 0)
  (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def sample (a : PR 3) (N s x : PTm n) : PTm n := sequence (sampleBody a) (succ N) (data N s x)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N s x : PTm n) :
    Syn.subst σ (data N s x) = data (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_sampleValue {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (i N s x : PTm n) :
    Syn.subst σ (sampleValue a i N s x) = sampleValue a (Syn.subst σ i) (Syn.subst σ N)
      (Syn.subst σ s) (Syn.subst σ x) := by simp [sampleValue,sg]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N s x : PTm n) :
    Syn.subst σ (sample a N s x) = sample a (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ x) := by simp [sample]

theorem sample_body_at (a : PR 3) (N s x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody a) i (data N s x) ≐ sampleValue a i N s x := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sampleValue a (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![i,fstT (data N s x),fstT (sndT (data N s x)),sndT (sndT (data N s x))])
    (σ' := ![i,N,s,x]) (fun j => by
      fin_cases j
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  simpa only [sampleBody,inst2,subst_sampleValue,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using h

theorem sample_length (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx] length (sample a N s x) ≐ succ N := sequence_length _ _ _

theorem sample_leading (a : PR 3) (N s x : PTm n) : Γ ⊢[PRAAx] entry (sample a N s x) zero ≐ qone :=
  (sequence_decode (sampleBody a) (zero_lt_succ N)).eqTrans
    ((sample_body_at a N s x zero).eqTrans (RationalArithmetic.select_zero _ _ _ sg_zero))

theorem sample_coefficient (a : PR 3) (N s x j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (sample a N s x) (succ j) ≐ ap3 a (monus N (succ j)) s x :=
  (sequence_decode (sampleBody a) ((succ_monus_succ (succ j) N).eqTrans hj)).eqTrans
    ((sample_body_at a N s x (succ j)).eqTrans (RationalArithmetic.select_one _ _ _ (sg_succ j)))

def polynomial (a : PR 3) (N R t x : PTm n) : PTm n := sample a N (GaussianRootSchedule.precision N R t) x
def rootList (step a : PR 3) (N R t x : PTm n) : PTm n :=
  GaussianApproximateFactorization.rootList step (polynomial a N R t x) N one (GaussianRootSchedule.toleranceDenominator N R t)
def productPolynomial (step a : PR 3) (N R t x : PTm n) : PTm n :=
  GaussianApproximateFactorization.productPolynomial step (polynomial a N R t x) N one (GaussianRootSchedule.toleranceDenominator N R t)

@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N R t x : PTm n) :
    Syn.subst σ (polynomial a N R t x) = polynomial a (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ t) (Syn.subst σ x) := by simp [polynomial]
@[simp] theorem subst_rootList {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N R t x : PTm n) :
    Syn.subst σ (rootList step a N R t x) = rootList step a (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ t) (Syn.subst σ x) := by simp [rootList]
@[simp] theorem subst_productPolynomial {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N R t x : PTm n) :
    Syn.subst σ (productPolynomial step a N R t x) = productPolynomial step a (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ t) (Syn.subst σ x) := by simp [productPolynomial]

theorem polynomial_length (a : PR 3) (N R t x : PTm n) : Γ ⊢[PRAAx] length (polynomial a N R t x) ≐ succ N := sample_length _ _ _ _
theorem polynomial_leading (a : PR 3) (N R t x : PTm n) : Γ ⊢[PRAAx] entry (polynomial a N R t x) zero ≐ qone := sample_leading _ _ _ _
theorem polynomial_coefficient (a : PR 3) (N R t x j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (polynomial a N R t x) (succ j) ≐ ap3 a (monus N (succ j)) (GaussianRootSchedule.precision N R t) x := sample_coefficient _ _ _ _ _ hj

theorem root_list_length (step a : PR 3) (N R t x : PTm n) : Γ ⊢[PRAAx] length (rootList step a N R t x) ≐ N :=
  GaussianApproximateFactorization.rootList_length _ _ _ _ _
theorem product_length (step a : PR 3) (N R t x : PTm n) : Γ ⊢[PRAAx] length (productPolynomial step a N R t x) ≐ succ N :=
  GaussianApproximateFactorization.product_length _ _ _ _ _
theorem product_leading (step a : PR 3) (N R t x : PTm n) : Γ ⊢[PRAAx] entry (productPolynomial step a N R t x) zero ≐ qone :=
  GaussianRationalReconstruction.reconstruct_monic _ _ _

theorem coefficient_error (step a : PR 3) (N R t x i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (entry (polynomial a N R t x) i)
      (entry (productPolynomial step a N R t x) i) one (GaussianRootSchedule.toleranceDenominator N R t) :=
  GaussianCoefficientNormEntries.approximate_factorization_entries step _ _ _ _ _ hRD
    (polynomial_length _ _ _ _ _) (polynomial_leading _ _ _ _ _) hN (le_refl _) (GaussianRootSchedule.tolerance_positive _ _ _) hi

theorem total_error (step a : PR 3) (N R t x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (GaussianCoefficientL1.coefficientNorm (GaussianCoefficientL1.subCoefficients
        (polynomial a N R t x) (productPolynomial step a N R t x) (succ N)))
      (GaussianFactorBudget.eta one (GaussianRootSchedule.toleranceDenominator N R t)) :=
  Prf.andE₂ (GaussianApproximateFactorization.approximate_factorization step _ _ _ _ hRD
    (polynomial_length _ _ _ _ _) (polynomial_leading _ _ _ _ _) hN (le_refl _) (GaussianRootSchedule.tolerance_positive _ _ _))

theorem product_evaluation (step a : PR 3) (N R t x z : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (productPolynomial step a N R t x) z ≐
      GaussianRationalReconstruction.product (rootList step a N R t x) N z :=
  GaussianApproximateFactorization.product_evaluation _ _ _ _ _ _

def output (step a : PR 3) (N R t x : PTm n) : PTm n :=
  pairT (polynomial a N R t x) (pairT (rootList step a N R t x) (productPolynomial step a N R t x))
def outputF (step a : PR 3) : PR 4 := PTm.toPR (output step a (var 0) (var 1) (var 2) (var 3))
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N R t x : PTm n) :
    Syn.subst σ (output step a N R t x) = output step a (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ t) (Syn.subst σ x) := by simp [output]
theorem sample_program (step a : PR 3) (N R t x : PTm n) : Γ ⊢[PRAAx]
    PTm.app (outputF step a) ![N,R,t,x] ≐ output step a N R t x := by
  simpa [outputF] using toPR_eq (Γ := Γ) (output step a (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,R,t,x]

theorem sampled_polynomial_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (sample a (var 0) (var 1) (var 2)) ≐ succ (var 0)) ⋏
      ((entry (sample a (var 0) (var 1) (var 2)) zero ≐ qone) ⋏
        (lt (var 3) (var 0) ⟶ entry (sample a (var 0) (var 1) (var 2)) (succ (var 3)) ≐
          ap3 a (monus (var 0) (succ (var 3))) (var 1) (var 2)))) :=
  closeUniv 4 (.andI (sample_length _ _ _ _) (.andI (sample_leading _ _ _ _) (.impI (sample_coefficient _ _ _ _ _ Prf.hyp0))))

theorem sampled_factor_error_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ le one (var 0) ⟶ le (var 4) (var 0) ⟶
      GaussianRationalMetric.distanceBounded (entry (polynomial a (var 0) (var 1) (var 2) (var 3)) (var 4))
        (entry (productPolynomial step a (var 0) (var 1) (var 2) (var 3)) (var 4))
        one (GaussianRootSchedule.toleranceDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (coefficient_error _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem sampled_factor_product_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalHorner.evaluate (productPolynomial step a (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      GaussianRationalReconstruction.product (rootList step a (var 0) (var 1) (var 2) (var 3)) (var 0) (var 4)) :=
  closeUniv 5 (product_evaluation _ _ _ _ _ _ _)

theorem root_samples_program_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app (outputF step a) ![var 0,var 1,var 2,var 3] ≐ output step a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (sample_program _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRootSamples
