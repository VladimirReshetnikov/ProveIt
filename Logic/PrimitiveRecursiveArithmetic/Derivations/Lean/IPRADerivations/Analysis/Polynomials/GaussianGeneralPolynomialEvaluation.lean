import IPRADerivations.Analysis.Polynomials.GaussianGeneralPolynomialSamples
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerLipschitz
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootApproximationWitness
import IPRADerivations.Analysis.Geometry.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.Names.GaussianFastValueCut

/-!
# General polynomial observations at a bounded fast Gaussian name

The actual observer evaluates every original coefficient, including the
possibly zero or changing leading sample. Coefficient data x and point data
y are separate numerical inputs. The derived modulus is C+M, where
C=(N+1)U^N and M is the actual weighted Horner Lipschitz sum. No residual,
monicity, name-validity of the output or regularity premise is used.

The existing all-coefficient and point-variation kernels contain their genuine
QF prefix inductions. This module composes their finite estimates at the
literal middle value P_t(z_s), including N=0 and raw original Gaussian codes.
Only the schemas a:PR3 and point:PR2 are externally fixed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialEvaluation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def A (a : PR 3) (N x : PTm n) : PTm n := GaussianCoefficientNameBounds.A a (succ N) x
def C (N U : PTm n) : PTm n := succ N*pw U N
def M (a : PR 3) (N U x : PTm n) : PTm n :=
  GaussianRationalHornerLipschitz.constant N U (A a N x)
def T (a : PR 3) (N U x : PTm n) : PTm n := C N U+M a N U x

def observation (a : PR 3) (point : PR 2) (N x y s : PTm n) : PTm n :=
  evaluate (GaussianGeneralPolynomialSamples.sample a N s x) (ap2 point s y)
def observationData (N x y : PTm n) : PTm n := pairT N (pairT x y)
def observationBody (a : PR 3) (point : PR 2) : PTm 2 :=
  observation a point (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def observationF (a : PR 3) (point : PR 2) : PR 2 := PTm.toPR (observationBody a point)

def input (a : PR 3) (point : PR 2) (N U x y : PTm n) : Fm PTm n :=
  generalCN a N x ⋏ (pointCN point y ⋏ (pointBounds point U y ⋏ le one U))

@[simp] theorem subst_A {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N x : PTm n) :
    Syn.subst σ (A a N x) = A a (Syn.subst σ N) (Syn.subst σ x) := by simp [A]
@[simp] theorem subst_C {m : ℕ} (σ : Fin n → PTm m) (N U : PTm n) :
    Syn.subst σ (C N U) = C (Syn.subst σ N) (Syn.subst σ U) := by simp [C]
@[simp] theorem subst_M {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x : PTm n) :
    Syn.subst σ (M a N U x) = M a (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [M]
@[simp] theorem subst_T {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x : PTm n) :
    Syn.subst σ (T a N U x) = T a (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [T]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2)
    (N x y s : PTm n) : Syn.subst σ (observation a point N x y s) =
      observation a point (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ s) := by simp [observation]
@[simp] theorem subst_observationData {m : ℕ} (σ : Fin n → PTm m) (N x y : PTm n) :
    Syn.subst σ (observationData N x y) =
      observationData (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) := by simp [observationData]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2)
    (N U x y : PTm n) : (input a point N U x y).subst σ =
      input a point (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) (Syn.subst σ y) := by simp [input]

/-- Structural congruence through the actual coefficient and Horner programs. -/
theorem observation_congr (a : PR 3) (point : PR 2) {N N' x x' y y' s s' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hx : Γ ⊢[PRAAx] x ≐ x')
    (hy : Γ ⊢[PRAAx] y ≐ y') (hs : Γ ⊢[PRAAx] s ≐ s') : Γ ⊢[PRAAx]
    observation a point N x y s ≐ observation a point N' x' y' s' := by
  have samples := (GaussianGeneralPolynomialSamples.program_at a N s x).eqSymm.eqTrans
    ((congrAp3 (GaussianGeneralPolynomialSamples.sampleF a) hN hs hx).eqTrans
      (GaussianGeneralPolynomialSamples.program_at a N' s' x'))
  exact GaussianRationalTranslation.evaluate_congr samples (congrAp2 point hs hy)

theorem observation_at (a : PR 3) (point : PR 2) (N x y s : PTm n) : Γ ⊢[PRAAx]
    ap2 (observationF a point) s (observationData N x y) ≐ observation a point N x y s := by
  have fields := observation_congr (Γ := Γ) a point
    (fst_pair N (pairT x y))
    ((congrFst (snd_pair N (pairT x y))).eqTrans (fst_pair x y))
    ((congrSnd (snd_pair N (pairT x y))).eqTrans (snd_pair x y)) (.eqRefl s)
  exact (toPR_eq (observationBody a point) ![s,observationData N x y]).eqTrans (by
    simpa only [observationBody,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,observationData] using fields)

theorem observation_canonical (a : PR 3) (point : PR 2) (N x y s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (observation a point N x y s) :=
  GaussianRationalHorner.horner_canonical _ _ _

/-- Every stored coefficient bound is derived from all original coefficient names. -/
theorem sample_coefficients (a : PR 3) (N s x : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) : Γ ⊢[PRAAx]
    GaussianEuclideanResidualRadius.coefficientBounds (GaussianGeneralPolynomialSamples.sample a N s x) (A a N x) := by
  refine .allI (.impI ?_)
  have cn : Γ.map Fm.shift ⊢[PRAAx] generalCN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift
  have inside : (lt (var 0) (length (Syn.shift (GaussianGeneralPolynomialSamples.sample a N s x))) :: Γ.map Fm.shift)
      ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans
      (lt_congr (.eqRefl _) (GaussianGeneralPolynomialSamples.sample_length a (Syn.shift N) (Syn.shift s) (Syn.shift x))
        (by simpa only [Syn.shift,GaussianGeneralPolynomialSamples.subst_sample] using Prf.hyp0))
  have bound := GaussianGeneralPolynomialSamples.sample_coefficient_bound a (Syn.shift N) (Syn.shift s)
    (Syn.shift x) (var 0) cn.wk inside
  change _ ⊢[PRAAx] bounded _ (PTm.monus (A a (Syn.shift N) (Syn.shift x)) one) one at bound
  have bigger := GaussianCoefficientNameBounds.bounded_radius_mono _ _ one (A a (Syn.shift N) (Syn.shift x)) one
    (le_refl _) (le_refl _) (le_congr (by ipra_ring) (by ipra_ring)
      (GaussianMonicResidualRadius.monus_le_left (A a (Syn.shift N) (Syn.shift x)) one)) bound
  simpa only [Syn.shift,GaussianGeneralPolynomialSamples.subst_sample,subst_A] using bigger

/-- Split at P_t(z_s): coefficient variation and point variation have the same denominator. -/
theorem observation_regular_at (a : PR 3) (point : PR 2) (N U x y s t : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    distanceBounded (observation a point N x y s) (observation a point N x y t)
      (T a N U x*(unit s+unit t)) (unit s*unit t) := by
  have pos := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive t)
  have first := GaussianRationalAllCoefficientPerturbation.evaluation_bound
    (GaussianGeneralPolynomialSamples.sample a N s x) (GaussianGeneralPolynomialSamples.sample a N t x)
    (ap2 point s y) N U (unit s+unit t) (unit s*unit t)
    (GaussianGeneralPolynomialSamples.sample_length a N s x) (GaussianGeneralPolynomialSamples.sample_length a N t x)
    hU pos (GaussianGeneralPolynomialSamples.all_coefficient_coherence a N s t x hCN)
    (GaussianRootApproximationWitness.point_at point U y s hBounds)
  have second := GaussianRationalHornerLipschitz.evaluation_bound
    (GaussianGeneralPolynomialSamples.sample a N t x) (ap2 point s y) (ap2 point t y)
    N U (A a N x) (unit s+unit t) (unit s*unit t)
    (GaussianGeneralPolynomialSamples.sample_length a N t x) (sample_coefficients a N t x hCN)
    (GaussianRootApproximationWitness.point_at point U y s hBounds)
    (GaussianRootApproximationWitness.point_at point U y t hBounds) pos
    (GaussianEuclideanDistanceName.point_cn_at point y s t hPoint)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold T C M; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ pos first second)

/-- The actual PR2 observer is regular; regularity is a conclusion, not a premise. -/
theorem observation_regular (a : PR 3) (point : PR 2) (N U x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (observationF a point) (T a N U x) (observationData N x y) := by
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      generalCN a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianGeneralCoefficientNames.subst_generalCN,Syn.shift] using hCN.shift.shift
  have pointCN' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift.shift
  have bounds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      pointBounds point (Syn.shift (Syn.shift U)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_pointBounds,Syn.shift] using hBounds.shift.shift
  have hu : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift U)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hU.shift.shift
  have actual := observation_regular_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift U))
    (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (var 0) cn pointCN' bounds hu
  simpa only [Syn.shift,subst_observationData,subst_T] using distance_congr
    (observation_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1)).eqSymm
    (observation_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) actual

theorem regular_of_input (a : PR 3) (point : PR 2) (N U x y : PTm n)
    (h : Γ ⊢[PRAAx] input a point N U x y) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (observationF a point) (T a N U x) (observationData N x y) :=
  observation_regular a point N U x y (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))

/-- Variables: N,U,x,y,s,t. Every coefficient including the head may vary. -/
theorem general_polynomial_observation_coherence_closed (a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (input a point (var 0) (var 1) (var 2) (var 3) ⟶
        distanceBounded (observation a point (var 0) (var 2) (var 3) (var 4))
          (observation a point (var 0) (var 2) (var 3) (var 5))
          (T a (var 0) (var 1) (var 2)*(unit (var 4)+unit (var 5))) (unit (var 4)*unit (var 5))) := by
  refine closeUniv 6 (.impI ?_)
  exact observation_regular_at a point _ _ _ _ _ _ (Prf.andE₁ Prf.hyp0) (Prf.andE₁ (Prf.andE₂ Prf.hyp0))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ Prf.hyp0))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ Prf.hyp0)))

/-- Variables: N,U,x,y. The actual persistent-data program has the derived modulus. -/
theorem general_polynomial_observer_regular_closed (a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (input a point (var 0) (var 1) (var 2) (var 3) ⟶
        GaussianFastValueCut.regular (observationF a point) (T a (var 0) (var 1) (var 2))
          (observationData (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular_of_input a point _ _ _ _ Prf.hyp0))

/-- Variables: N,x,y,s. The returned code is the actual original-polynomial observation. -/
theorem general_polynomial_observation_program_closed (a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (ap2 (observationF a point) (var 3) (observationData (var 0) (var 1) (var 2)) ≐
        observation a point (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (observation_at a point _ _ _ _)

/-- Variables: N,s,x. All stored sample bounds, including degree zero, are derived. -/
theorem general_sample_coefficient_bounds_closed (a : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (generalCN a (var 0) (var 2) ⟶
        GaussianEuclideanResidualRadius.coefficientBounds
          (GaussianGeneralPolynomialSamples.sample a (var 0) (var 1) (var 2)) (A a (var 0) (var 2))) :=
  closeUniv 3 (.impI (sample_coefficients a _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialEvaluation
