import IPRADerivations.Analysis.GaussianCharacteristicNames
import IPRADerivations.Analysis.GaussianMonicRootAdequacy

/-!
# Actual characteristic names in the concrete monic root-support program

Only original matrix-name CN and positive numerical size supply the root
support theorem. The radius and schedule are the existing computed ones,
at coefficientF a with actual packed data (N,x). Every stage polynomial's
stored coefficients are bound to the same actual characteristic run at
its source cofinal matrix precision. Adequacy for an arbitrary query name
retains its genuine point-name and disk conditions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicRootSupport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCharacteristicNames (coefficientF)
open GaussianRationalMetric (bounded)
open GaussianRationalCover (close check)
open GaussianRootSupport (coverDenominator)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N x : PTm n) : PTm n := pairT N x
def radius (a : PR 4) (N x : PTm n) : PTm n := GaussianCoefficientNameBounds.R (coefficientF a) N (data N x)
def stagePrecision (a : PR 4) (N t x : PTm n) : PTm n := GaussianRootSchedule.precision N (radius a N x) t
def sourcePrecision (a : PR 4) (N t x : PTm n) : PTm n := stagePrecision a N t x+
  GaussianCharacteristicPrecisionShift.clock N (GaussianMatrixNames.B a N x)
def roots (a : PR 4) (N t x : PTm n) : PTm n := GaussianMonicRootSupport.roots (coefficientF a) N t (data N x)
def product (a : PR 4) (N t x : PTm n) : PTm n := GaussianMonicRootSupport.product (coefficientF a) N t (data N x)
def polynomial (a : PR 4) (N t x : PTm n) : PTm n := GaussianMonicRootSupport.polynomial (coefficientF a) N t (data N x)
def actualPolynomial (a : PR 4) (N t x : PTm n) : PTm n := GaussianRationalCharacteristicPolynomial.run
  (GaussianMatrixNames.sample a N (sourcePrecision a N t x) x) N
def rootNameF (a : PR 4) : PR 3 := GaussianMonicRootSupport.rootNameF (coefficientF a)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (N x : PTm n) :
    Syn.subst σ (data N x) = data (Syn.subst σ N) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N x : PTm n) :
    Syn.subst σ (radius a N x) = radius a (Syn.subst σ N) (Syn.subst σ x) := by simp [radius]
@[simp] theorem subst_stagePrecision {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (stagePrecision a N t x) = stagePrecision a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [stagePrecision]
@[simp] theorem subst_sourcePrecision {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (sourcePrecision a N t x) = sourcePrecision a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [sourcePrecision]
@[simp] theorem subst_roots {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (roots a N t x) = roots a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [roots]
@[simp] theorem subst_product {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (product a N t x) = product a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [product]
@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (polynomial a N t x) = polynomial a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [polynomial]
@[simp] theorem subst_actualPolynomial {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (actualPolynomial a N t x) = actualPolynomial a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by simp [actualPolynomial]

theorem coefficient_name (a : PR 4) (N x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] GaussianCoefficientNameBounds.CN (coefficientF a) N (data N x) :=
  GaussianCharacteristicNames.coefficient_name a N x h
theorem radius_explicit (a : PR 4) (N x : PTm n) : Γ ⊢[PRAAx]
    radius a N x ≐ GaussianCoefficientNameBounds.three+
      GaussianCoefficientNameBounds.ceilM (coefficientF a) N (data N x)+two := .eqRefl _
theorem roots_length (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx] length (roots a N t x) ≐ N :=
  GaussianMonicRootSupport.roots_length _ _ _ _
theorem root_radius (a : PR 4) (N t x i : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (roots a N t x) i) (radius a N x) one :=
  GaussianMonicRootSupport.root_radius _ _ _ _ _ (coefficient_name a N x h) hN hi
theorem root_support (a : PR 4) (N t u x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    close (roots a N t x) (roots a N u x) one (coverDenominator t) :=
  GaussianMonicRootSupport.root_support _ _ _ _ _ (coefficient_name a N x h) hN htu
theorem root_support_checker (a : PR 4) (N t u x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    check (roots a N t x) (roots a N u x) one (coverDenominator t) ≐ one :=
  GaussianMonicRootSupport.root_support_checker _ _ _ _ _ (coefficient_name a N x h) hN htu

theorem root_name_at (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (rootNameF a) N t (data N x) ≐ roots a N t x := GaussianMonicRootSupport.root_name_program _ _ _ _
theorem root_name_length (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx] length (ap3 (rootNameF a) N t (data N x)) ≐ N :=
  GaussianMonicRootSupport.root_name_length _ _ _ _
theorem root_name_support (a : PR 4) (N t u x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    close (ap3 (rootNameF a) N t (data N x)) (ap3 (rootNameF a) N u (data N x)) one (coverDenominator t) :=
  GaussianMonicRootSupport.root_name_support _ _ _ _ _ (coefficient_name a N x h) hN htu
theorem root_name_radius (a : PR 4) (N t x i : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (entry (ap3 (rootNameF a) N t (data N x)) i) (radius a N x) one :=
  GaussianMonicRootSupport.root_name_radius _ _ _ _ _ (coefficient_name a N x h) hN hi

theorem stage_polynomial_length (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx] length (polynomial a N t x) ≐ succ N :=
  GaussianMonicRootSupport.polynomial_length _ _ _ _
theorem actual_polynomial_length (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx] length (actualPolynomial a N t x) ≐ succ N :=
  GaussianRationalCharacteristicPolynomial.returned_length _ _
theorem stage_head_binding (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial a N t x) zero ≐ entry (actualPolynomial a N t x) zero :=
  (GaussianMonicRootSupport.polynomial_leading _ _ _ _).eqTrans (GaussianRationalCharacteristicPolynomial.returned_monic _ _).eqSymm
theorem stage_coefficient_binding (a : PR 4) (N t x j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (polynomial a N t x) (succ j) ≐ entry (actualPolynomial a N t x) (succ j) :=
  (GaussianMonicRootSupport.polynomial_coefficient _ _ _ _ _ hj).eqTrans
    ((GaussianCharacteristicNames.coefficient_at a N (monus N (succ j)) (stagePrecision a N t x) x).eqTrans
      (entry_congr (.eqRefl _) (Foundations.BoundedSyntaxBackwardInduction.reverse_complement N (succ j) hj)))

theorem stage_entry_binding (a : PR 4) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (polynomial a N t x) i ≐ entry (actualPolynomial a N t x) i := by
  refine .orE (zero_or_succ i) ?_ ?_
  · exact (entry_congr (.eqRefl _) Prf.hyp0).eqTrans
      ((stage_head_binding a N t x).eqTrans (entry_congr (.eqRefl _) Prf.hyp0).eqSymm)
  · have hj : (i ≐ succ (PTm.pred i)) :: Γ ⊢[PRAAx] lt (PTm.pred i) N :=
      le_congr Prf.hyp0 (.eqRefl _) hi.wk
    exact (entry_congr (.eqRefl _) Prf.hyp0).eqTrans
      ((stage_coefficient_binding a N t x _ hj).eqTrans (entry_congr (.eqRefl _) Prf.hyp0).eqSymm)

theorem completed_distance (a : PR 4) (point : PR 2) (N x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN point (data N x)) : Γ ⊢[PRAAx]
    GaussianMonicRootAdequacy.distanceConclusion (coefficientF a) point N (data N x) :=
  GaussianMonicRootAdequacy.completed_distance _ _ _ _ (.andI (coefficient_name a N x h) (.andI hN hPoint))
theorem root_adequacy (a : PR 4) (point : PR 2) (N Z x : PTm n) (h : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (radius a N x) Z)
    (hPoint : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN point (data N x))
    (hDisk : Γ ⊢[PRAAx] GaussianRepresentedPointBounds.normLE point Z (data N x)) : Γ ⊢[PRAAx]
    GaussianMonicRootAdequacy.conclusion (coefficientF a) point N Z (data N x) :=
  GaussianMonicRootAdequacy.root_adequacy _ _ _ _ _
    (.andI (coefficient_name a N x h) (.andI hN (.andI hR (.andI hPoint hDisk))))

theorem actual_characteristic_root_length_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (ap3 (rootNameF a) (var 0) (var 1) (data (var 0) (var 2))) ≐ var 0) := closeUniv 3 (root_name_length a _ _ _)
theorem actual_characteristic_root_support_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianMatrixNames.CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ le (var 1) (var 2) ⟶
      close (ap3 (rootNameF a) (var 0) (var 1) (data (var 0) (var 3)))
        (ap3 (rootNameF a) (var 0) (var 2) (data (var 0) (var 3))) one (coverDenominator (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (root_name_support a _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_characteristic_root_radius_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianMatrixNames.CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ lt (var 3) (var 0) ⟶
      bounded (entry (ap3 (rootNameF a) (var 0) (var 1) (data (var 0) (var 2))) (var 3)) (radius a (var 0) (var 2)) one) :=
  closeUniv 4 (.impI (.impI (.impI (root_name_radius a _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_stage_coefficient_binding_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 0) ⟶ entry (polynomial a (var 0) (var 1) (var 2)) (succ (var 3)) ≐
      entry (actualPolynomial a (var 0) (var 1) (var 2)) (succ (var 3))) := closeUniv 4 (.impI (stage_coefficient_binding a _ _ _ _ Prf.hyp0))
theorem actual_stage_head_binding_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (polynomial a (var 0) (var 1) (var 2)) zero ≐ entry (actualPolynomial a (var 0) (var 1) (var 2)) zero) :=
  closeUniv 3 (stage_head_binding a _ _ _)
theorem actual_stage_all_slots_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 0) ⟶ entry (polynomial a (var 0) (var 1) (var 2)) (var 3) ≐
      entry (actualPolynomial a (var 0) (var 1) (var 2)) (var 3)) := closeUniv 4 (.impI (stage_entry_binding a _ _ _ _ Prf.hyp0))
theorem actual_characteristic_completed_distance_closed (a : PR 4) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianMatrixNames.CN a (var 0) (var 1) ⟶ le one (var 0) ⟶ GaussianEuclideanDistanceName.pointCN point (data (var 0) (var 1)) ⟶
      GaussianMonicRootAdequacy.distanceConclusion (coefficientF a) point (var 0) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (completed_distance a point _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_characteristic_root_adequacy_closed (a : PR 4) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianMatrixNames.CN a (var 0) (var 2) ⟶ le one (var 0) ⟶ le (radius a (var 0) (var 2)) (var 1) ⟶
      GaussianEuclideanDistanceName.pointCN point (data (var 0) (var 2)) ⟶
      GaussianRepresentedPointBounds.normLE point (var 1) (data (var 0) (var 2)) ⟶
      GaussianMonicRootAdequacy.conclusion (coefficientF a) point (var 0) (var 1) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI
    (root_adequacy a point _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianCharacteristicRootSupport
