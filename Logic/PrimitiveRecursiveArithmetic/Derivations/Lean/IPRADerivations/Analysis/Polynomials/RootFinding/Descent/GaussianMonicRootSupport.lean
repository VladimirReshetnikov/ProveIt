import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicRD
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRootSupport

/-!
# Concrete collision-tolerant root-support names

The fixed proved GaussianMonicRD.step is instantiated in the original
sample/factorization, radius and root-support programs. These definitions
are aliases of those exact programs, including their coefficient ordering,
source A/R/E(t) schedule, both original Euclidean covers, and Boolean checker.
Only the genuine coefficient-name CN, positive degree and stage order remain
as hypotheses. No step, RD, radius, coherence or accepted-output premise is
supplied. The external a:PR3 is the fixed coefficient syntax schema; every
degree, precision, point index and persistent data value is internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicRootSupport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianMonicRD (step)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN A R)
open LeanProofs.IPRA.Analysis.GaussianRootSupport (coverDenominator)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalStability (pointsBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (close check)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def roots (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootRadius.roots step a N t x
def product (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootRadius.product step a N t x
def polynomial (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootSamples.polynomial a N (R a N x) t x
def rootNameF (a : PR 3) : PR 3 := GaussianRootSupport.rootNameF step a
def output (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootRadius.output step a N t x
def outputF (a : PR 3) : PR 3 := GaussianRootRadius.outputF step a
def run (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootRadius.run step a N t x

@[simp] theorem subst_roots {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N t x : PTm n) :
    Syn.subst σ (roots a N t x) = roots a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [roots]
@[simp] theorem subst_product {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N t x : PTm n) :
    Syn.subst σ (product a N t x) = product a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [product]
@[simp] theorem subst_polynomial {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N t x : PTm n) :
    Syn.subst σ (polynomial a N t x) = polynomial a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [polynomial]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N t x : PTm n) :
    Syn.subst σ (output a N t x) = output a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N t x : PTm n) :
    Syn.subst σ (run a N t x) = run a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [run]

theorem roots_length (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] length (roots a N t x) ≐ N :=
  GaussianRootRadius.roots_length step a N t x
theorem product_length (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] length (product a N t x) ≐ succ N :=
  GaussianRootRadius.product_length step a N t x
theorem product_leading (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx]
    entry (product a N t x) zero ≐ GaussianRationalSyntheticDivision.qone := GaussianRootRadius.product_leading step a N t x
theorem polynomial_length (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] length (polynomial a N t x) ≐ succ N :=
  GaussianRootSamples.polynomial_length _ _ _ _ _
theorem polynomial_leading (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial a N t x) zero ≐ GaussianRationalSyntheticDivision.qone := GaussianRootSamples.polynomial_leading _ _ _ _ _
theorem polynomial_coefficient (a : PR 3) (N t x j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (polynomial a N t x) (succ j) ≐
      ap3 a (PTm.monus N (succ j)) (GaussianRootSchedule.precision N (R a N x) t) x :=
  GaussianRootSamples.polynomial_coefficient _ _ _ _ _ _ hj

theorem coefficient_error (a : PR 3) (N t x i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (entry (polynomial a N t x) i) (entry (product a N t x) i)
      one (GaussianRootSchedule.toleranceDenominator N (R a N x) t) :=
  GaussianRootSamples.coefficient_error step a _ _ _ _ _ GaussianMonicRD.monic_rd hN hi
theorem total_error (a : PR 3) (N t x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (GaussianCoefficientL1.coefficientNorm (GaussianCoefficientL1.subCoefficients (polynomial a N t x) (product a N t x) (succ N)))
      (GaussianFactorBudget.eta one (GaussianRootSchedule.toleranceDenominator N (R a N x) t)) :=
  GaussianRootSamples.total_error step a _ _ _ _ GaussianMonicRD.monic_rd hN
theorem product_evaluation (a : PR 3) (N t x z : PTm n) : Γ ⊢[PRAAx]
    evaluate (product a N t x) z ≐ GaussianRationalReconstruction.product (roots a N t x) N z :=
  GaussianRootSamples.product_evaluation step a N (R a N x) t x z

theorem product_coefficients (a : PR 3) (N t x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianEuclideanResidualRadius.coefficientBounds (product a N t x) (A a N x) :=
  GaussianRootRadius.product_coefficients step a N t x GaussianMonicRD.monic_rd hCN hN
theorem root_radius (a : PR 3) (N t x i : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (roots a N t x) i) (R a N x) one :=
  GaussianRootRadius.root_radius step a N t x i GaussianMonicRD.monic_rd hCN hN hi
theorem listed_zero (a : PR 3) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    evaluate (product a N t x) (entry (roots a N t x) i) ≐ qzero := GaussianRootRadius.listed_zero step a N t x i hi
theorem all_roots_bounded (a : PR 3) (N t x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    pointsBounded (roots a N t x) (R a N x) one :=
  GaussianRootSupport.all_roots_bounded step a N t x GaussianMonicRD.monic_rd hCN hN

theorem root_support (a : PR 3) (N t u x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    close (roots a N t x) (roots a N u x) one (coverDenominator t) :=
  GaussianRootSupport.root_support step a N t u x GaussianMonicRD.monic_rd hCN hN htu
theorem root_support_checker (a : PR 3) (N t u x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    check (roots a N t x) (roots a N u x) one (coverDenominator t) ≐ one :=
  GaussianRootSupport.root_support_checker step a N t u x GaussianMonicRD.monic_rd hCN hN htu

theorem root_name_program (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (rootNameF a) N t x ≐ roots a N t x := GaussianRootSupport.root_name_program step a N t x
theorem root_name_length (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx]
    length (ap3 (rootNameF a) N t x) ≐ N := (congrFst (root_name_program a N t x)).eqTrans (roots_length a N t x)
theorem root_name_radius (a : PR 3) (N t x i : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (ap3 (rootNameF a) N t x) i) (R a N x) one :=
  GaussianRationalReciprocal.bound_congr (entry_congr (root_name_program a N t x).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (root_radius a N t x i hCN hN hi)
theorem root_name_listed_zero (a : PR 3) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    evaluate (product a N t x) (entry (ap3 (rootNameF a) N t x) i) ≐ qzero :=
  (GaussianRationalReconstruction.evaluate_congr (.eqRefl _) (entry_congr (root_name_program a N t x) (.eqRefl _))).eqTrans (listed_zero a N t x i hi)

theorem checker_congr {S S' T T' p q : PTm n} (hS : Γ ⊢[PRAAx] S ≐ S') (hT : Γ ⊢[PRAAx] T ≐ T') : Γ ⊢[PRAAx]
    check S T p q ≐ check S' T' p q := by
  apply congrApp
  intro i
  fin_cases i
  · exact hS
  · exact hT
  · exact .eqRefl _
  · exact .eqRefl _

theorem root_name_checker (a : PR 3) (N t u x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    check (ap3 (rootNameF a) N t x) (ap3 (rootNameF a) N u x) one (coverDenominator t) ≐ one :=
  (checker_congr (root_name_program a N t x) (root_name_program a N u x)).eqTrans (root_support_checker a N t u x hCN hN htu)
theorem root_name_support (a : PR 3) (N t u x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    close (ap3 (rootNameF a) N t x) (ap3 (rootNameF a) N u x) one (coverDenominator t) :=
  (GaussianRationalCover.checker_reflection _ _ _ _).iffMp (root_name_checker a N t u x hCN hN htu)
theorem checker_boolean (a : PR 3) (N t u x : PTm n) : Γ ⊢[PRAAx]
    (check (roots a N t x) (roots a N u x) one (coverDenominator t) ≐ zero) ⋎
      (check (roots a N t x) (roots a N u x) one (coverDenominator t) ≐ one) := GaussianRationalCover.checker_boolean _ _ _ _
theorem checker_reflection (a : PR 3) (N t u x : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (check (roots a N t x) (roots a N u x) one (coverDenominator t) ≐ one)
      (close (roots a N t x) (roots a N u x) one (coverDenominator t)) := GaussianRationalCover.checker_reflection _ _ _ _

theorem program_at (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] run a N t x ≐ output a N t x := GaussianRootRadius.program_at step a N t x
theorem returned_roots (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] fstT (run a N t x) ≐ roots a N t x := GaussianRootRadius.returned_roots step a N t x
theorem returned_product (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run a N t x)) ≐ product a N t x := GaussianRootRadius.returned_product step a N t x
theorem returned_A (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run a N t x))) ≐ A a N x :=
  (congrFst ((congrSnd ((congrSnd (program_at a N t x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_R (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run a N t x))) ≐ R a N x :=
  (congrSnd ((congrSnd ((congrSnd (program_at a N t x)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_root_radius (a : PR 3) (N t x i : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (fstT (run a N t x)) i) (R a N x) one :=
  GaussianRootRadius.returned_root_radius step a N t x i GaussianMonicRD.monic_rd hCN hN hi
theorem returned_listed_zero (a : PR 3) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    evaluate (fstT (sndT (run a N t x))) (entry (fstT (run a N t x)) i) ≐ qzero :=
  GaussianRootRadius.returned_listed_zero step a N t x i hi
theorem returned_checker (a : PR 3) (N t u x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    check (fstT (run a N t x)) (fstT (run a N u x)) one (coverDenominator t) ≐ one :=
  (checker_congr (returned_roots a N t x) (returned_roots a N u x)).eqTrans (root_support_checker a N t u x hCN hN htu)
theorem returned_support (a : PR 3) (N t u x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    close (fstT (run a N t x)) (fstT (run a N u x)) one (coverDenominator t) :=
  (GaussianRationalCover.checker_reflection _ _ _ _).iffMp (returned_checker a N t u x hCN hN htu)

theorem concrete_root_support_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 3) ⟶ le one (var 0) ⟶
      (pointsBounded (roots a (var 0) (var 1) (var 3)) (R a (var 0) (var 3)) one ⋏
        (le (var 1) (var 2) ⟶ close (roots a (var 0) (var 1) (var 3)) (roots a (var 0) (var 2) (var 3)) one (coverDenominator (var 1))))) :=
  closeUniv 4 (.impI (.impI (.andI (all_roots_bounded _ _ _ _ Prf.hyp1 Prf.hyp0)
    (.impI (root_support _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem concrete_root_support_checker_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (var 1) (var 2) ⟶
      check (roots a (var 0) (var 1) (var 3)) (roots a (var 0) (var 2) (var 3)) one (coverDenominator (var 1)) ≐ one) :=
  closeUniv 4 (.impI (.impI (.impI (root_support_checker _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem concrete_root_name_checker_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (var 1) (var 2) ⟶
      check (ap3 (rootNameF a) (var 0) (var 1) (var 3)) (ap3 (rootNameF a) (var 0) (var 2) (var 3)) one (coverDenominator (var 1)) ≐ one) :=
  closeUniv 4 (.impI (.impI (.impI (root_name_checker _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem concrete_root_name_support_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (var 1) (var 2) ⟶
      close (ap3 (rootNameF a) (var 0) (var 1) (var 3)) (ap3 (rootNameF a) (var 0) (var 2) (var 3)) one (coverDenominator (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (root_name_support _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem concrete_sample_root_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ lt (var 3) (var 0) ⟶
      (bounded (entry (roots a (var 0) (var 1) (var 2)) (var 3)) (R a (var 0) (var 2)) one ⋏
        evaluate (product a (var 0) (var 1) (var 2)) (entry (roots a (var 0) (var 1) (var 2)) (var 3)) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (root_radius _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0) (listed_zero _ _ _ _ _ Prf.hyp0)))))
theorem concrete_product_coefficients_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (CN a (var 0) (var 2) ⟶ le one (var 0) ⟶
      GaussianEuclideanResidualRadius.coefficientBounds (product a (var 0) (var 1) (var 2)) (A a (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (product_coefficients _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem concrete_coefficient_error_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le (var 3) (var 0) ⟶ distanceBounded
      (entry (polynomial a (var 0) (var 1) (var 2)) (var 3)) (entry (product a (var 0) (var 1) (var 2)) (var 3))
      one (GaussianRootSchedule.toleranceDenominator (var 0) (R a (var 0) (var 2)) (var 1))) :=
  closeUniv 4 (.impI (.impI (coefficient_error _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem concrete_total_coefficient_error_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ RationalArgmin.rationalLE
      (GaussianCoefficientL1.coefficientNorm (GaussianCoefficientL1.subCoefficients
        (polynomial a (var 0) (var 1) (var 2)) (product a (var 0) (var 1) (var 2)) (succ (var 0))))
      (GaussianFactorBudget.eta one (GaussianRootSchedule.toleranceDenominator (var 0) (R a (var 0) (var 2)) (var 1)))) :=
  closeUniv 3 (.impI (total_error _ _ _ _ Prf.hyp0))
theorem concrete_product_evaluation_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (product a (var 0) (var 1) (var 2)) (var 3) ≐
      GaussianRationalReconstruction.product (roots a (var 0) (var 1) (var 2)) (var 0) (var 3)) := closeUniv 4 (product_evaluation _ _ _ _ _)
theorem concrete_root_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 (rootNameF a) (var 0) (var 1) (var 2) ≐ roots a (var 0) (var 1) (var 2)) ⋏
      (length (ap3 (rootNameF a) (var 0) (var 1) (var 2)) ≐ var 0 ⋏ run a (var 0) (var 1) (var 2) ≐ output a (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (root_name_program _ _ _ _) (.andI (root_name_length _ _ _ _) (program_at _ _ _ _)))
theorem concrete_returned_root_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ lt (var 3) (var 0) ⟶
      (bounded (entry (fstT (run a (var 0) (var 1) (var 2))) (var 3)) (R a (var 0) (var 2)) one ⋏
        evaluate (fstT (sndT (run a (var 0) (var 1) (var 2)))) (entry (fstT (run a (var 0) (var 1) (var 2))) (var 3)) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (returned_root_radius _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0) (returned_listed_zero _ _ _ _ _ Prf.hyp0)))))
theorem concrete_returned_support_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (var 1) (var 2) ⟶
      close (fstT (run a (var 0) (var 1) (var 3))) (fstT (run a (var 0) (var 2) (var 3))) one (coverDenominator (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_support _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem concrete_named_root_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ lt (var 3) (var 0) ⟶
      (bounded (entry (ap3 (rootNameF a) (var 0) (var 1) (var 2)) (var 3)) (R a (var 0) (var 2)) one ⋏
        evaluate (product a (var 0) (var 1) (var 2)) (entry (ap3 (rootNameF a) (var 0) (var 1) (var 2)) (var 3)) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (root_name_radius _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0) (root_name_listed_zero _ _ _ _ _ Prf.hyp0)))))
theorem concrete_checker_reflection_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (check (roots a (var 0) (var 1) (var 3)) (roots a (var 0) (var 2) (var 3)) one (coverDenominator (var 1)) ≐ one)
      (close (roots a (var 0) (var 1) (var 3)) (roots a (var 0) (var 2) (var 3)) one (coverDenominator (var 1)))) :=
  closeUniv 4 (checker_reflection _ _ _ _ _)
theorem concrete_returned_fields_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run a (var 0) (var 1) (var 2)) ≐ roots a (var 0) (var 1) (var 2)) ⋏
      ((fstT (sndT (run a (var 0) (var 1) (var 2))) ≐ product a (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (sndT (run a (var 0) (var 1) (var 2)))) ≐ A a (var 0) (var 2)) ⋏
          sndT (sndT (sndT (run a (var 0) (var 1) (var 2)))) ≐ R a (var 0) (var 2)))) :=
  closeUniv 3 (.andI (returned_roots _ _ _ _) (.andI (returned_product _ _ _ _)
    (.andI (returned_A _ _ _ _) (returned_R _ _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianMonicRootSupport
