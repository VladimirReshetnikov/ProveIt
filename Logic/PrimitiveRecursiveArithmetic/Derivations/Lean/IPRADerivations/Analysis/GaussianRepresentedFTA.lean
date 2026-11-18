import IPRADerivations.Analysis.GaussianGeneralFTAValueZero
import IPRADerivations.Analysis.GaussianPolynomialNameHorner

/-!
# The constructed general FTA root in actual Gaussian name arithmetic

FTA_iPRA's final paragraph identifies the residual-zero name with ordinary
name arithmetic. Here the root is the exact existing trajectory program and
the polynomial is the actual uniform numerical-prefix Horner protocol. The
original source radius, coefficient data, point data and normalization shift
are retained. Original inclusive coefficient CN and one finite nonconstant
coefficient apartness certificate are the only inputs of the source theorem.

This is a finite-code represented-name theorem. It does not construct an
abstract complete-field quotient or a represented full factorization.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LeanProofs.IPRA.Analysis.GaussianRepresentedFTA

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput subst_sourceInput)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)
open LeanProofs.IPRA.Analysis.GaussianNameEquivalence (crossEquivalent)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialValueName (programZero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rootF (a : PR 3) : PR 2 := GaussianGeneralFTATrajectory.nameF a
def rootData (N h x : PTm n) : PTm n := GaussianGeneralFTATrajectory.nameData N h x
def radius (a : PR 3) (N h x : PTm n) : PTm n := GaussianGeneralFTAConstants.R a N h x
def prefixF (a : PR 3) : PR 2 := GaussianPolynomialNameHorner.prefixF a (rootF a)
def prefixData (a : PR 3) (N h x j : PTm n) : PTm n :=
  GaussianPolynomialNameHorner.nameData a N (radius a N h x) j x (rootData N h x)
def valueData (a : PR 3) (N h x : PTm n) : PTm n := prefixData a N h x (succ N)
def stepF (a : PR 3) : PR 2 := GaussianPolynomialNameHorner.stepF a (rootF a)
def stepData (a : PR 3) (N h x j : PTm n) : PTm n :=
  GaussianPolynomialNameHorner.stepData a (rootF a) N (radius a N h x) j x (rootData N h x)

def properPrefixes (a : PR 3) (N h x : PTm n) : Fm PTm n := .all
  (le (var 0) (succ (Syn.shift N)) ⟶ pointCN (prefixF a)
    (prefixData a (Syn.shift N) (Syn.shift h) (Syn.shift x) (var 0)))
def hornerSteps (a : PR 3) (N h x : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift N) ⟶ crossEquivalent (prefixF a) (stepF a)
    (prefixData a (Syn.shift N) (Syn.shift h) (Syn.shift x) (succ (var 0)))
    (stepData a (Syn.shift N) (Syn.shift h) (Syn.shift x) (var 0)))
def certificate (a : PR 3) (N h x : PTm n) : Fm PTm n :=
  pointCN (rootF a) (rootData N h x) ⋏
    (pointBounds (rootF a) (radius a N h x) (rootData N h x) ⋏
    (properPrefixes a N h x ⋏
    (crossEquivalent (prefixF a) GaussianNameRingLaws.zeroF (prefixData a N h x zero) zero ⋏
    (hornerSteps a N h x ⋏
    (pointCN (prefixF a) (valueData a N h x) ⋏
    (programZero (prefixF a) (valueData a N h x) ⋏
      crossEquivalent (prefixF a) GaussianNameRingLaws.zeroF (valueData a N h x) zero))))))

@[simp] theorem subst_rootData {m : ℕ} (σ : Fin n → PTm m) (N h x : PTm n) :
    Syn.subst σ (rootData N h x) = rootData (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [rootData]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (radius a N h x) = radius a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [radius]
@[simp] theorem subst_prefixData {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (prefixData a N h x j) = prefixData a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by
  simp [prefixData]
@[simp] theorem subst_valueData {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (valueData a N h x) = valueData a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [valueData]
@[simp] theorem subst_stepData {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x j : PTm n) :
    Syn.subst σ (stepData a N h x j) = stepData a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ j) := by simp [stepData]
@[simp] theorem subst_properPrefixes {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    (properPrefixes a N h x).subst σ = properPrefixes a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp [properPrefixes,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_hornerSteps {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    (hornerSteps a N h x).subst σ = hornerSteps a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp [hornerSteps,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    (certificate a N h x).subst σ = certificate a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [certificate]

theorem root_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (rootF a) t (rootData N h x) ≐ GaussianGeneralFTATrajectory.alpha a N h x t :=
  GaussianGeneralFTATrajectory.name_at a N h x t
theorem root_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (rootF a) t (rootData N h x)) :=
  GaussianGeneralFTATrajectory.returned_canonical a N h x t

theorem root_fast (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    pointCN (rootF a) (rootData N h x) := GaussianGeneralFTAName.name_fast a N k h x hSource
theorem root_bounds (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    pointBounds (rootF a) (radius a N h x) (rootData N h x) := GaussianGeneralFTAName.name_bounds a N k h x hSource

theorem prefix_fast (a : PR 3) (N k h x j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (hj : Γ ⊢[PRAAx] le j (succ N)) : Γ ⊢[PRAAx]
    pointCN (prefixF a) (prefixData a N h x j) :=
  GaussianPolynomialNameHorner.prefix_fast a (rootF a) N (radius a N h x) j x (rootData N h x)
    (Prf.andE₁ hSource) (root_fast a N k h x hSource) (root_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x) hj

theorem all_prefixes (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    properPrefixes a N h x := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,subst_sourceInput,Syn.shift] using hSource.shift
  simpa only [Syn.shift,subst_prefixData] using
    prefix_fast a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) (var 0) hs.wk Prf.hyp0

theorem prefix_zero (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a) GaussianNameRingLaws.zeroF (prefixData a N h x zero) zero :=
  GaussianPolynomialNameHorner.zero_prefix a (rootF a) N (radius a N h x) x (rootData N h x)
    (Prf.andE₁ hSource) (root_fast a N k h x hSource) (root_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x)

theorem prefix_step (a : PR 3) (N k h x j : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a) (stepF a) (prefixData a N h x (succ j)) (stepData a N h x j) :=
  GaussianPolynomialNameHorner.recurrence a (rootF a) N (radius a N h x) j x (rootData N h x)
    (Prf.andE₁ hSource) (root_fast a N k h x hSource) (root_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x) hj

theorem all_steps (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    hornerSteps a N h x := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,subst_sourceInput,Syn.shift] using hSource.shift
  simpa only [Syn.shift,subst_prefixData,subst_stepData] using
    prefix_step a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) (var 0) hs.wk Prf.hyp0

theorem value_fast (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    pointCN (prefixF a) (valueData a N h x) := prefix_fast a N k h x (succ N) hSource (le_refl _)
theorem value_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (prefixF a) t (valueData a N h x)) :=
  GaussianPolynomialNameHorner.prefix_canonical a (rootF a) N (radius a N h x) (succ N) x (rootData N h x) t

/-- The full prefix uses precisely the original FTA polynomial-value query. -/
theorem value_program_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (prefixF a) t (valueData a N h x) ≐
      ap2 (GaussianGeneralFTAValueZero.valueNameF a) t (GaussianGeneralFTAValueZero.valueNameData a N h x) :=
  GaussianPolynomialNameHorner.full_prefix_at a (rootF a) N (radius a N h x) x (rootData N h x) t

theorem value_zero (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    programZero (prefixF a) (valueData a N h x) :=
  (GaussianPolynomialNameHorner.full_zero_iff a (rootF a) N (radius a N h x) x (rootData N h x)
    (Prf.andE₁ hSource) (root_fast a N k h x hSource) (root_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x)).iffMpr
    (GaussianGeneralFTAValueZero.generic_value_zero a N k h x hSource)
theorem value_bound (a : PR 3) (N k h x t : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (ap2 (prefixF a) t (valueData a N h x)) one (unit t) :=
  GaussianGeneralPolynomialValueName.program_zero_at _ _ _ (value_zero a N k h x hSource)

/-- The actual Horner value is zero as a represented name class as well as
satisfying the existing concrete zero predicate. -/
theorem value_equivalent_zero (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    crossEquivalent (prefixF a) GaussianNameRingLaws.zeroF (valueData a N h x) zero := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ one
    (value_fast a N k h x hSource) (GaussianNameRingLaws.zero_fast zero)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,subst_sourceInput,Syn.shift] using hSource.shift
  have small := (GaussianReconstructionRoots.distance_zero_iff _ one (unit (var 0)) (unit_positive _)).iffMpr
    (value_bound a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) (var 0) hs)
  simpa only [Syn.shift,subst_valueData,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (GaussianNameRingLaws.zero_at (var 0) zero).eqSymm
      (.eqRefl _) (.eqRefl _) small

/-- Source-only FTA at the actual uniform name/ring-arithmetic program. -/
theorem represented_fta (a : PR 3) (N k h x : PTm n) (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    certificate a N h x :=
  .andI (root_fast a N k h x hSource) (.andI (root_bounds a N k h x hSource)
    (.andI (all_prefixes a N k h x hSource) (.andI (prefix_zero a N k h x hSource)
      (.andI (all_steps a N k h x hSource) (.andI (value_fast a N k h x hSource)
        (.andI (value_zero a N k h x hSource) (value_equivalent_zero a N k h x hSource)))))))

/-- The finite apartness coefficient index k is proof-only. The actual
observations take exactly N,h,x,t, matching the original trajectory program. -/
def output (a : PR 3) (N h x t : PTm n) : PTm n :=
  pairT (ap2 (rootF a) t (rootData N h x)) (pairT (ap2 (prefixF a) t (valueData a N h x)) (radius a N h x))
def outputF (a : PR 3) : PR 4 := PTm.toPR (output a (var 0) (var 1) (var 2) (var 3))
def run (a : PR 3) (N h x t : PTm n) : PTm n := PTm.app (outputF a) ![N,h,x,t]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (output a N h x t) = output a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by
  simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (run a N h x t) = run a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1; funext j; fin_cases j <;> rfl

theorem output_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx] run a N h x t ≐ output a N h x t := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,h,x,t]
theorem returned_root (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N h x t) ≐ ap2 (rootF a) t (rootData N h x) :=
  (congrFst (output_at a N h x t)).eqTrans (fst_pair _ _)
theorem returned_value (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a N h x t)) ≐ ap2 (prefixF a) t (valueData a N h x) :=
  (congrFst ((congrSnd (output_at a N h x t)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_radius (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run a N h x t)) ≐ radius a N h x :=
  (congrSnd ((congrSnd (output_at a N h x t)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_root_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N h x t) ≐ GaussianGeneralFTATrajectory.alpha a N h x t :=
  (returned_root a N h x t).eqTrans (root_at a N h x t)
theorem returned_original_value_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a N h x t)) ≐
      ap2 (GaussianGeneralFTAValueZero.valueNameF a) t (GaussianGeneralFTAValueZero.valueNameData a N h x) :=
  (returned_value a N h x t).eqTrans (value_program_at a N h x t)
theorem returned_root_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (fstT (run a N h x t)) (sndT (sndT (run a N h x t))) one :=
  GaussianRationalReciprocal.bound_congr (returned_root a N h x t).eqSymm
    (returned_radius a N h x t).eqSymm (.eqRefl _)
    (GaussianGeneralFTAName.named_disk a N k h x t hSource)
theorem returned_value_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (fstT (sndT (run a N h x t))) one (unit t) :=
  GaussianRationalReciprocal.bound_congr (returned_value a N h x t).eqSymm (.eqRefl _) (.eqRefl _)
    (value_bound a N k h x t hSource)
theorem returned_root_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (fstT (run a N h x t)) :=
  GaussianRationalHorner.canonical_congr (returned_root a N h x t) (root_canonical a N h x t)
theorem returned_value_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (fstT (sndT (run a N h x t))) :=
  GaussianRationalHorner.canonical_congr (returned_value a N h x t) (value_canonical a N h x t)

/-! All source guards are original coefficient CN, numerical 1<=k<=N and
finite apartness of the original coefficient observation at h+2. No root,
disk, descent, regularity or value law occurs on the input side below. -/
theorem source_represented_fta_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ certificate a (var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (represented_fta a _ _ _ _ Prf.hyp0))
theorem source_root_name_and_horner_zero_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN (rootF a) (rootData (var 0) (var 2) (var 3)) ⋏
      (pointCN (prefixF a) (valueData a (var 0) (var 2) (var 3)) ⋏
      (programZero (prefixF a) (valueData a (var 0) (var 2) (var 3)) ⋏
        crossEquivalent (prefixF a) GaussianNameRingLaws.zeroF (valueData a (var 0) (var 2) (var 3)) zero)))) :=
  closeUniv 4 (.impI (.andI (root_fast a _ _ _ _ Prf.hyp0)
    (.andI (value_fast a _ _ _ _ Prf.hyp0) (.andI (value_zero a _ _ _ _ Prf.hyp0) (value_equivalent_zero a _ _ _ _ Prf.hyp0)))))
theorem source_actual_horner_recurrence_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 0) ⟶
      crossEquivalent (prefixF a) (stepF a) (prefixData a (var 0) (var 2) (var 3) (succ (var 4)))
        (stepData a (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (prefix_step a _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem source_actual_empty_prefix_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (prefixF a) GaussianNameRingLaws.zeroF (prefixData a (var 0) (var 2) (var 3) zero) zero) :=
  closeUniv 4 (.impI (prefix_zero a _ _ _ _ Prf.hyp0))
theorem literal_original_root_and_value_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (rootF a) (var 3) (rootData (var 0) (var 1) (var 2)) ≐
        GaussianGeneralFTATrajectory.alpha a (var 0) (var 1) (var 2) (var 3) ⋏
      ap2 (prefixF a) (var 3) (valueData a (var 0) (var 1) (var 2)) ≐
        ap2 (GaussianGeneralFTAValueZero.valueNameF a) (var 3)
          (GaussianGeneralFTAValueZero.valueNameData a (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.andI (root_at a _ _ _ _) (value_program_at a _ _ _ _))
theorem actual_sample_program_fields_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run a (var 0) (var 1) (var 2) (var 3) ≐ output a (var 0) (var 1) (var 2) (var 3) ⋏
      (fstT (run a (var 0) (var 1) (var 2) (var 3)) ≐ GaussianGeneralFTATrajectory.alpha a (var 0) (var 1) (var 2) (var 3) ⋏
      (fstT (sndT (run a (var 0) (var 1) (var 2) (var 3))) ≐
        ap2 (GaussianGeneralFTAValueZero.valueNameF a) (var 3)
          (GaussianGeneralFTAValueZero.valueNameData a (var 0) (var 1) (var 2)) ⋏
        sndT (sndT (run a (var 0) (var 1) (var 2) (var 3))) ≐ radius a (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.andI (output_at a _ _ _ _) (.andI (returned_root_at a _ _ _ _)
    (.andI (returned_original_value_at a _ _ _ _) (returned_radius a _ _ _ _))))
theorem source_returned_sample_bounds_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (bounded (fstT (run a (var 0) (var 2) (var 3) (var 4)))
        (sndT (sndT (run a (var 0) (var 2) (var 3) (var 4)))) one ⋏
        bounded (fstT (sndT (run a (var 0) (var 2) (var 3) (var 4)))) one (unit (var 4)))) :=
  closeUniv 5 (.impI (.andI (returned_root_bound a _ _ _ _ _ Prf.hyp0) (returned_value_bound a _ _ _ _ _ Prf.hyp0)))
theorem actual_canonical_samples_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalHorner.canonical (fstT (run a (var 0) (var 1) (var 2) (var 3))) ⋏
      GaussianRationalHorner.canonical (fstT (sndT (run a (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.andI (returned_root_canonical a _ _ _ _) (returned_value_canonical a _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRepresentedFTA
