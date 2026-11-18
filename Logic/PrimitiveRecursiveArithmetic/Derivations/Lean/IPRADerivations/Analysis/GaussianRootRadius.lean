import IPRADerivations.Analysis.GaussianCoefficientNameBounds
import IPRADerivations.Analysis.GaussianRootSamples
import IPRADerivations.Analysis.GaussianRationalDistanceOrder

/-!
# The computed common radius of the actual root-support samples

The radius is exactly source R=A+2, where A=3+ceil(max_i ||a(i,0,x)||1).
The final product coefficients are bounded using the original coefficient
name and the actual approximate-factorization error. The actual listed-root
zero theorem and Euclidean monic radius theorem then give this common radius
for every returned root. Temporary deflation coefficient/radius bounds are
not used as a substitute for this final-product argument.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN A R)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero evaluate)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def roots (step a : PR 3) (N t x : PTm n) : PTm n := GaussianRootSamples.rootList step a N (R a N x) t x
def product (step a : PR 3) (N t x : PTm n) : PTm n := GaussianRootSamples.productPolynomial step a N (R a N x) t x

@[simp] theorem subst_roots {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N t x : PTm n) :
    Syn.subst σ (roots step a N t x) = roots step a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [roots,GaussianRootSamples.subst_rootList,GaussianCoefficientNameBounds.subst_R]
@[simp] theorem subst_product {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N t x : PTm n) :
    Syn.subst σ (product step a N t x) = product step a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [product,GaussianRootSamples.subst_productPolynomial,GaussianCoefficientNameBounds.subst_R]

theorem roots_length (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] length (roots step a N t x) ≐ N :=
  GaussianRootSamples.root_list_length _ _ _ _ _ _
theorem product_length (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] length (product step a N t x) ≐ succ N :=
  GaussianRootSamples.product_length _ _ _ _ _ _
theorem product_leading (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] entry (product step a N t x) zero ≐ qone :=
  GaussianRootSamples.product_leading _ _ _ _ _ _

theorem A_positive (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] le one (A a N x) :=
  le_trans (le_of_eq_add (d := two) (by unfold GaussianCoefficientNameBounds.three; ipra_ring))
    (GaussianCoefficientNameBounds.A_lower a N x)

/-- Every nonleading original sample coefficient has the source bound A-1
at the actual E(t) used by the approximate factorizer. -/
theorem sample_lower_coefficient_bound (a : PR 3) (N t x j : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    bounded (entry (GaussianRootSamples.polynomial a N (R a N x) t x) (succ j)) (PTm.monus (A a N x) one) one :=
  GaussianRationalReciprocal.bound_congr (GaussianRootSamples.polynomial_coefficient a N (R a N x) t x j hj).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.sample_bound a N x (PTm.monus N (succ j))
      (GaussianRootSchedule.precision N (R a N x) t) hCN (GaussianApproximateFactorization.remaining_active N j hj))

/-- The actual AF coefficient discrepancy is at most one, since its actual
power-of-two tolerance denominator is positive. It is reversed to compare
final product coefficients against the original samples. -/
theorem reverse_coefficient_error_one (step a : PR 3) (N t x i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (entry (product step a N t x) i) (entry (GaussianRootSamples.polynomial a N (R a N x) t x) i) one one := by
  have positive := GaussianRootSchedule.tolerance_positive (Γ := Γ) N (R a N x) t
  have actual := GaussianRootSamples.coefficient_error step a N (R a N x) t x i hRD hN hi
  have reversed := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ positive actual
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ one _ one one positive (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) positive) reversed

/-- Each lower final-product coefficient is within the actual eta<=1 of a
sample of radius A-1. The conclusion concerns the computed final product,
not one of the temporary polynomials in synthetic deflation. -/
theorem product_lower_coefficient_bound (step a : PR 3) (N t x j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    bounded (entry (product step a N t x) (succ j)) (A a N x) one := by
  have sum := GaussianReconstructionRoots.norm_from_distance _ _ one one (PTm.monus (A a N x) one) one (le_refl _) (le_refl _)
    (reverse_coefficient_error_one step a N t x (succ j) hRD hN hj)
    (sample_lower_coefficient_bound a N t x j hCN hj)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    ((by ipra_ring : Γ ⊢[PRAAx] one*one+PTm.monus (A a N x) one*one ≐ one+PTm.monus (A a N x) one).eqTrans
      (eq_add_of_le (A_positive a N x)).eqSymm) (by ipra_ring) sum

theorem product_coefficient_bound (step a : PR 3) (N t x i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    bounded (entry (product step a N t x) i) (A a N x) one := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have head : ((i ≐ zero) :: Γ) ⊢[PRAAx] entry (product step a N t x) i ≐ qone :=
      (entry_congr (.eqRefl _) Prf.hyp0).eqTrans (product_leading step a N t x)
    exact GaussianRationalReciprocal.bound_congr head.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianCoefficientNameBounds.bounded_radius_mono _ one one _ one (le_refl _) (le_refl _)
        (le_congr (by ipra_ring) (by ipra_ring) (A_positive a N x)) GaussianRationalReciprocal.qone_bounded)
  · have index : ((i ≐ succ (PTm.pred i)) :: Γ) ⊢[PRAAx] lt (PTm.pred i) N := le_congr Prf.hyp0 (.eqRefl _) hi.wk
    exact GaussianRationalReciprocal.bound_congr (entry_congr (.eqRefl _) Prf.hyp0.eqSymm) (.eqRefl _) (.eqRefl _)
      (product_lower_coefficient_bound step a N t x (PTm.pred i) hRD.wk hCN.wk hN.wk index)

/-- The whole actual final product satisfies the original Euclidean
coefficient predicate required by the sharp monic radius theorem. -/
theorem product_coefficients (step a : PR 3) (N t x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianEuclideanResidualRadius.coefficientBounds (product step a N t x) (A a N x) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (product step a N t x))) :: Γ.map Fm.shift
  have hRD' : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have hCN' : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have hN' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  have range : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := by
    have h : Δ ⊢[PRAAx] lt (var 0) (length (product step a (Syn.shift N) (Syn.shift t) (Syn.shift x))) := by
      simpa only [Δ,Syn.shift,subst_product] using Prf.hyp0
    exact (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (.eqRefl _) (product_length step a (Syn.shift N) (Syn.shift t) (Syn.shift x)) h)
  simpa only [Δ,Syn.shift,subst_product,GaussianCoefficientNameBounds.subst_A] using
    product_coefficient_bound step a (Syn.shift N) (Syn.shift t) (Syn.shift x) (var 0) hRD'.wk hCN'.wk hN'.wk range

/-- Every actually listed root is an exact rational zero of its actual
final product polynomial, independently of the descent and CN contracts. -/
theorem listed_zero (step a : PR 3) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    evaluate (product step a N t x) (entry (roots step a N t x) i) ≐ qzero :=
  GaussianReconstructionRoots.listed_root_zero _ _ _ hi

/-- The common source radius follows from the final product coefficients
and its exact listed-zero result, rather than the temporary A_j radii. -/
theorem root_radius (step a : PR 3) (N t x i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (roots step a N t x) i) (R a N x) one :=
  GaussianReconstructionRoots.listed_radius _ _ _ _ hN (A_positive a N x) (product_coefficients step a N t x hRD hCN hN) hi

/-! Actual returned root/product fields and uniformly closed source results. -/
def output (step a : PR 3) (N t x : PTm n) : PTm n :=
  pairT (roots step a N t x) (pairT (product step a N t x) (pairT (A a N x) (R a N x)))
def outputF (step a : PR 3) : PR 3 := PTm.toPR (output step a (var 0) (var 1) (var 2))
def run (step a : PR 3) (N t x : PTm n) : PTm n := ap3 (outputF step a) N t x

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N t x : PTm n) :
    Syn.subst σ (output step a N t x) = output step a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [output,subst_pairT,subst_roots,subst_product,GaussianCoefficientNameBounds.subst_A,GaussianCoefficientNameBounds.subst_R]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N t x : PTm n) :
    Syn.subst σ (run step a N t x) = run step a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp only [run,subst_ap3]

theorem program_at (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] run step a N t x ≐ output step a N t x := by
  simpa only [run,outputF,ap3,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (output step a (var 0) (var 1) (var 2) : PTm 3) ![N,t,x]

theorem returned_roots (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] fstT (run step a N t x) ≐ roots step a N t x :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_product (step a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run step a N t x)) ≐ product step a N t x :=
  (congrFst ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)

theorem returned_root_radius (step a : PR 3) (N t x i : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (fstT (run step a N t x)) i) (R a N x) one :=
  GaussianRationalReciprocal.bound_congr (entry_congr (returned_roots step a N t x).eqSymm (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (root_radius step a N t x i hRD hCN hN hi)

theorem returned_listed_zero (step a : PR 3) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    evaluate (fstT (sndT (run step a N t x))) (entry (fstT (run step a N t x)) i) ≐ qzero :=
  (GaussianRationalReconstruction.evaluate_congr (returned_product step a N t x)
    (entry_congr (returned_roots step a N t x) (.eqRefl _))).eqTrans (listed_zero step a N t x i hi)

theorem final_product_coefficients_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (monicRD step ⟶ CN a (var 0) (var 2) ⟶ le one (var 0) ⟶
      GaussianEuclideanResidualRadius.coefficientBounds (product step a (var 0) (var 1) (var 2)) (A a (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (product_coefficients _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem final_product_coefficient_bound_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ le (var 3) (var 0) ⟶
      bounded (entry (product step a (var 0) (var 1) (var 2)) (var 3)) (A a (var 0) (var 2)) one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (product_coefficient_bound _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem sampled_root_radius_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ lt (var 3) (var 0) ⟶
      bounded (entry (roots step a (var 0) (var 1) (var 2)) (var 3)) (R a (var 0) (var 2)) one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (root_radius _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem sampled_listed_zero_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶ evaluate (product step a (var 0) (var 1) (var 2))
      (entry (roots step a (var 0) (var 1) (var 2)) (var 3)) ≐ qzero) :=
  closeUniv 4 (.impI (listed_zero _ _ _ _ _ _ Prf.hyp0))

theorem returned_sample_root_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (monicRD step ⟶ CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ lt (var 3) (var 0) ⟶
      (bounded (entry (fstT (run step a (var 0) (var 1) (var 2))) (var 3)) (R a (var 0) (var 2)) one ⋏
        (evaluate (fstT (sndT (run step a (var 0) (var 1) (var 2))))
          (entry (fstT (run step a (var 0) (var 1) (var 2))) (var 3)) ≐ qzero))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.andI
    (returned_root_radius _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)
    (returned_listed_zero _ _ _ _ _ _ Prf.hyp0))))))

theorem root_radius_program_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run step a (var 0) (var 1) (var 2) ≐ output step a (var 0) (var 1) (var 2)) ⋏
      ((length (fstT (run step a (var 0) (var 1) (var 2))) ≐ var 0) ⋏
        (length (fstT (sndT (run step a (var 0) (var 1) (var 2)))) ≐ succ (var 0)))) :=
  closeUniv 3 (.andI (program_at _ _ _ _ _) (.andI
    ((congrFst (returned_roots _ _ _ _ _)).eqTrans (roots_length _ _ _ _ _))
    ((congrFst (returned_product _ _ _ _ _)).eqTrans (product_length _ _ _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianRootRadius
