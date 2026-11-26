import IPRADerivations.Analysis.Integration.GaussianCompactIntervalRescaling
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Gamma.GaussianGammaCompactCutoffSplit

/-!
# Cofinal transformed meshes for the unchanged lower compact name

The root-transformed uniform time grid is a positive refinement of the
original compact mesh after positively rescaling its interval encoding.
The original evaluator precision and the original Lipschitz constant are
retained. No equality between differently encoded evaluator calls is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerCofinalQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature sample mesh precision)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactCutoffGeometry (lowerWidth)
open GaussianEulerCompactModulus (lipschitz)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rootMesh (t L T : PTm n) : PTm n := unit t*mesh t L T
def scale (t A L T : PTm n) : PTm n := pw (rootMesh t L T) A
def count (t A C L T : PTm n) : PTm n := C*scale t A L T
def factor (t A C L T : PTm n) : PTm n := C*pw (rootMesh t L T) (pred A)*unit t
def transformed (F : PR 3) (t A C E L T x : PTm n) : PTm n :=
  quadrature F (precision t T) (count t A C L T) (scale t A L T)
    (C*scale t A L T) (E*scale t A L T) x

def input (F : PR 3) (A C E L T x : PTm n) : Fm PTm n :=
  le one A ⋏ (le one C ⋏ GaussianCompactRiemannName.input F one C E L T x)

@[simp] theorem subst_rootMesh {m : ℕ} (σ : Fin n → PTm m) (t L T : PTm n) :
    Syn.subst σ (rootMesh t L T) = rootMesh (Syn.subst σ t) (Syn.subst σ L) (Syn.subst σ T) := by simp [rootMesh]
@[simp] theorem subst_scale {m : ℕ} (σ : Fin n → PTm m) (t A L T : PTm n) :
    Syn.subst σ (scale t A L T) = scale (Syn.subst σ t) (Syn.subst σ A) (Syn.subst σ L) (Syn.subst σ T) := by simp [scale]
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (t A C L T : PTm n) :
    Syn.subst σ (count t A C L T) = count (Syn.subst σ t) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ L) (Syn.subst σ T) := by simp [count]
@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (t A C L T : PTm n) :
    Syn.subst σ (factor t A C L T) = factor (Syn.subst σ t) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ L) (Syn.subst σ T) := by simp [factor]
@[simp] theorem subst_transformed {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (t A C E L T x : PTm n) :
    Syn.subst σ (transformed F t A C E L T x) = transformed F (Syn.subst σ t) (Syn.subst σ A) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [transformed]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (A C E L T x : PTm n) :
    (input F A C E L T x).subst σ = input F (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E)
      (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [input]

theorem root_mesh_positive (t L T : PTm n) : Γ ⊢[PRAAx] le one (rootMesh t L T) :=
  positive_product _ _ (unit_positive t) (GaussianCompactRiemannName.mesh_positive t L T)
theorem scale_positive (t A L T : PTm n) : Γ ⊢[PRAAx] le one (scale t A L T) :=
  GaussianPolynomialPerturbation.power_positive _ _ (root_mesh_positive t L T)
theorem factor_positive (t A C L T : PTm n) (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx] le one (factor t A C L T) :=
  positive_product _ _ (positive_product _ _ hC (GaussianPolynomialPerturbation.power_positive _ _ (root_mesh_positive t L T))) (unit_positive t)

/-- The actual transformed count, with a genuine positive refinement factor. -/
theorem count_factorization (t A C L T : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    count t A C L T ≐ factor t A C L T*mesh t L T := by
  have step := (congrAp2 powF (GaussianOffDominantWeights.positive_succ_pred A hA) (.eqRefl (rootMesh t L T))).eqTrans
    (pw_succ (rootMesh t L T) (pred A))
  exact (congrMul (.eqRefl C) step).eqTrans (by unfold factor rootMesh; ipra_ring)

theorem transformed_at (F : PR 3) (t A C E L T x : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    transformed F t A C E L T x ≐ quadrature F (precision t T) (factor t A C L T*mesh t L T)
      (scale t A L T*one) (scale t A L T*C) (scale t A L T*E) x := by
  simpa [transformed] using Prf.eqCongr (quadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![precision t T,count t A C L T,scale t A L T,C*scale t A L T,E*scale t A L T,x])
    (σ' := ![precision t T,factor t A C L T*mesh t L T,scale t A L T*one,scale t A L T*C,scale t A L T*E,x])
    (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact count_factorization t A C L T hA
      · exact (by ipra_ring : Γ ⊢[PRAAx] scale t A L T ≐ scale t A L T*one)
      · exact mul_comm _ _
      · exact mul_comm _ _
      · exact .eqRefl _)

/-- The original modulus L is unchanged by the transformed encoding. -/
theorem transformed_refinement (F : PR 3) (t A C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F A C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (transformed F t A C E L T x)
      (sample F t (scale t A L T*one) (scale t A L T*C) (scale t A L T*E) L T x) (num 3) (unit (t+num 6)) := by
  have scaled := GaussianCompactIntervalRescaling.scaled_input F (scale t A L T) one C E L T x
    (.andI (scale_positive t A L T) h.andE₂.andE₂)
  exact distance_congr (transformed_at F t A C E L T x h.andE₁).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianCompactMeshIndependence.arbitrary_refinement F t (precision t T) (factor t A C L T)
      (scale t A L T*one) (scale t A L T*C) (scale t A L T*E) L T x scaled (factor_positive t A C L T h.andE₂.andE₁) (le_refl _))

theorem three_slack (t : PTm n) : Γ ⊢[PRAAx] le (num 3*unit t) (unit (t+num 6)) := by
  have square : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  have fourth : Γ ⊢[PRAAx] pw two (two+two) ≐ num 16 :=
    (pw_add two two two).eqTrans ((congrMul square square).eqTrans (by ipra_ring))
  have eval : Γ ⊢[PRAAx] pw two (num 6) ≐ num 64 :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] num 6 ≐ (two+two)+two) (.eqRefl _)).eqTrans
      ((pw_add two (two+two) two).eqTrans ((congrMul fourth square).eqTrans (by ipra_ring)))
  have split : Γ ⊢[PRAAx] unit (t+num 6) ≐ unit t*num 64 :=
    (pw_add two t (num 6)).eqTrans (congrMul (.eqRefl _) eval)
  exact le_congr (.eqRefl _) split.eqSymm (le_of_eq_add (d := num 61*unit t) (by ipra_ring))

/-- Comparison with any requested observation of the original, unscaled
compact name. The error is 2*2^(-t)+2^(-r). -/
theorem observations (F : PR 3) (t r A C E L T x : PTm n) (h : Γ ⊢[PRAAx] input F A C E L T x) : Γ ⊢[PRAAx]
    distanceBounded (transformed F t A C E L T x) (sample F r one C E L T x)
      (two*unit r+unit t) (unit t*unit r) := by
  have refine := transformed_refinement F t A C E L T x h
  have coarse := distance_radius_mono _ _ _ _ one (unit t) (unit_positive _) (unit_positive _) (le_congr (.eqRefl _) (by ipra_ring) (three_slack t)) refine
  have rescaled := distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive t))
    (GaussianCompactIntervalRescaling.observations F r t (scale t A L T) one C E L T x
      (.andI (scale_positive t A L T) h.andE₂.andE₂))
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive t)
    (positive_product _ _ (unit_positive r) (unit_positive t)) coarse rescaled
  exact distance_radius_mono _ _ _ _ (two*unit r+unit t) (unit t*unit r)
    (positive_product _ _ (unit_positive t) (positive_product _ _ (unit_positive r) (unit_positive t)))
    (positive_product _ _ (unit_positive t) (unit_positive r)) (le_of_eq_add (d := zero) (by ipra_ring)) joined

/-- Only original disk, positive encoding, and strict cutoff guards are
needed for the lower interval specialization. -/
theorem original_lower_observations (t r z R B p q A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCompactCutoffSplit.source z R B p q A) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    distanceBounded (transformed GaussianEulerIntegrandName.evaluatorF t A (lowerWidth p q A) (etaDen q A R)
      (lipschitz R (etaDen q A R) (top q A R)) (top q A R) (GaussianEulerIntegrandName.fixedData z B))
      (ap2 GaussianEulerCompactAdditivity.nameF r (GaussianGammaCompactCutoffSplit.lowerData z R B p q A))
      (two*unit r+unit t) (unit t*unit r) := by
  have old := GaussianEulerCompactAdditivity.compact_input z R B one (lowerWidth p q A) (etaDen q A R) (top q A R)
    (GaussianGammaCompactCutoffSplit.lower_source z R B p q A h)
  have actual := observations GaussianEulerIntegrandName.evaluatorF t r A (lowerWidth p q A) (etaDen q A R)
    (lipschitz R (etaDen q A R) (top q A R)) (top q A R) (GaussianEulerIntegrandName.fixedData z B)
    (.andI h.andE₂.andE₁ (.andI (GaussianGammaCompactCutoffGeometry.lower_positive p q A h.andE₂.andE₁ hpq) old))
  exact distance_congr (.eqRefl _) (GaussianCompactRiemannName.name_at _ _ _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) actual

/-- Actual primitive-recursive observation, with every mesh parameter
retained in the returned quadrature code. -/
def transformedF (F : PR 3) : PR 7 := PTm.toPR
  (transformed F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (F : PR 3) (t A C E L T x : PTm n) : PTm n :=
  PTm.app (transformedF F) ![t,A,C,E,L,T,x]
theorem program_at (F : PR 3) (t A C E L T x : PTm n) : Γ ⊢[PRAAx]
    run F t A C E L T x ≐ transformed F t A C E L T x := by
  simpa [run,transformedF] using toPR_eq (Γ := Γ)
    (transformed F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![t,A,C,E,L,T,x]

theorem actual_transformed_count_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ count (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      factor (var 0) (var 1) (var 2) (var 3) (var 4)*mesh (var 0) (var 3) (var 4)) :=
  closeUniv 5 (.impI (count_factorization _ _ _ _ _ Prf.hyp0))

theorem actual_transformed_positive_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ le one (factor (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (factor_positive _ _ _ _ _ Prf.hyp0))

theorem actual_cofinal_original_compact_observations_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (transformed F (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (sample F (var 1) one (var 3) (var 4) (var 5) (var 6) (var 7))
        (two*unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (observations F _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_lower_tail_transformed_quadrature_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianGammaCompactCutoffSplit.source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⋏ lt (var 5) (var 6)) ⟶
      distanceBounded (transformed GaussianEulerIntegrandName.evaluatorF (var 0) (var 7)
        (lowerWidth (var 5) (var 6) (var 7)) (etaDen (var 6) (var 7) (var 3))
        (lipschitz (var 3) (etaDen (var 6) (var 7) (var 3)) (top (var 6) (var 7) (var 3)))
        (top (var 6) (var 7) (var 3)) (GaussianEulerIntegrandName.fixedData (var 2) (var 4)))
        (ap2 GaussianEulerCompactAdditivity.nameF (var 1)
          (GaussianGammaCompactCutoffSplit.lowerData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (two*unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_lower_observations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_transformed_quadrature_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      transformed F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at F _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLowerCofinalQuadrature
