import IPRADerivations.Analysis.GaussianGeneralPolynomialValueName
import IPRADerivations.Analysis.GaussianGeneralFTAPolynomialValueName
import IPRADerivations.Analysis.GaussianGeneralFTAName

/-!
# The general polynomial-value program is zero at the constructed FTA name

The coefficient data and point-name data remain distinct numerical inputs.
The general observer is instantiated at the actual constructed root name,
then identified with the already proved same-precision polynomial observation.
Its genuine source-only dyadic envelope is passed through the general value
normalizer's finite slack-removal theorem. No comparison between the envelope
constant and the regularity modulus is required. The two normalized value
programs keep their own precision shifts; their raw codes are not identified.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAValueZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialSamples (sourceInput)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (R)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def envelopeConstant (a : PR 3) (N h x : PTm n) : PTm n :=
  (two*two*two)*GaussianGeneralFTAPolynomialValueName.S a N h x+one

def valueNameF (a : PR 3) : PR 2 :=
  GaussianGeneralPolynomialValueName.nameF a (GaussianGeneralFTATrajectory.nameF a)

def valueNameData (a : PR 3) (N h x : PTm n) : PTm n :=
  GaussianGeneralPolynomialValueName.nameData a N (R a N h x) x
    (GaussianGeneralFTATrajectory.nameData N h x)

def value (a : PR 3) (N h x t : PTm n) : PTm n :=
  GaussianGeneralPolynomialValueName.value a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) t

def valueZero (a : PR 3) (N h x : PTm n) : Fm PTm n :=
  GaussianGeneralPolynomialValueName.valueZero a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x)

def nameZero (a : PR 3) (N h x : PTm n) : Fm PTm n :=
  GaussianGeneralPolynomialValueName.nameZero a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x)

@[simp] theorem subst_envelopeConstant {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (envelopeConstant a N h x) =
      envelopeConstant a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp [envelopeConstant]
@[simp] theorem subst_valueNameData {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (valueNameData a N h x) =
      valueNameData a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp [valueNameData]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x t : PTm n) :
    Syn.subst σ (value a N h x t) =
      value a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) (Syn.subst σ t) := by
  simp [value]
@[simp] theorem subst_valueZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    (valueZero a N h x).subst σ =
      valueZero a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp [valueZero]
@[simp] theorem subst_nameZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    (nameZero a N h x).subst σ =
      nameZero a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by
  simp [nameZero]

/-- Actual Horner evaluation at the returned point program, without a
canonical-input or value-law premise. -/
theorem observation_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialEvaluation.observation a (GaussianGeneralFTATrajectory.nameF a)
      N x (GaussianGeneralFTATrajectory.nameData N h x) t ≐
        GaussianGeneralFTAPolynomialValueName.observation a N h x t := by
  exact congrAp3 GaussianRationalHorner.hornerF (.eqRefl _) (.eqRefl _)
    (GaussianGeneralFTATrajectory.name_at a N h x t)

theorem raw_observation_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianGeneralPolynomialEvaluation.observationF a (GaussianGeneralFTATrajectory.nameF a)) t
      (GaussianGeneralPolynomialEvaluation.observationData N x (GaussianGeneralFTATrajectory.nameData N h x)) ≐
        GaussianGeneralFTAPolynomialValueName.observation a N h x t :=
  (GaussianGeneralPolynomialEvaluation.observation_at a (GaussianGeneralFTATrajectory.nameF a)
    N x (GaussianGeneralFTATrajectory.nameData N h x) t).eqTrans (observation_at a N h x t)

/-- The actual all-coefficient observer has a source-only envelope. Its
constant is not required to lie below the observer's regularity modulus. -/
theorem raw_observation_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianGeneralPolynomialEvaluation.observationF a (GaussianGeneralFTATrajectory.nameF a)) t
      (GaussianGeneralPolynomialEvaluation.observationData N x (GaussianGeneralFTATrajectory.nameData N h x)))
      (envelopeConstant a N h x) (unit t) := by
  have small := GaussianGeneralFTAPolynomialValueName.observation_bound a N k h x t hSource
  have enlarged : Γ ⊢[PRAAx] bounded
      (GaussianGeneralFTAPolynomialValueName.observation a N h x t)
      (envelopeConstant a N h x) (unit t) :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _ (le_succ_self one) (le_succ_self one))
      (unit_positive _)) (unit_positive _)
    (le_of_eq_add (d := (two*two*two)*GaussianGeneralFTAPolynomialValueName.S a N h x*(unit t+unit t+unit t)+
      unit t+unit t+unit t) (by unfold envelopeConstant; ipra_ring)) small
  exact GaussianRationalReciprocal.bound_congr (raw_observation_at a N h x t).eqSymm
    (.eqRefl _) (.eqRefl _) enlarged

theorem raw_envelope (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialValueName.rawEnvelope a (GaussianGeneralFTATrajectory.nameF a)
      N x (GaussianGeneralFTATrajectory.nameData N h x) (envelopeConstant a N h x) := by
  have input : Γ.map Fm.shift ⊢[PRAAx]
      sourceInput a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift
  refine .allI ?_
  have result : Γ.map Fm.shift ⊢[PRAAx]
      bounded (ap2 (GaussianGeneralPolynomialEvaluation.observationF a (GaussianGeneralFTATrajectory.nameF a))
        (var 0) (GaussianGeneralPolynomialEvaluation.observationData (Syn.shift N) (Syn.shift x)
          (GaussianGeneralFTATrajectory.nameData (Syn.shift N) (Syn.shift h) (Syn.shift x))))
        (zero*unit (var 0)+envelopeConstant a (Syn.shift N) (Syn.shift h) (Syn.shift x)*one)
        (one*unit (var 0)) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (raw_observation_bound a (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) (var 0) input)
  simpa only [GaussianGeneralPolynomialValueName.rawEnvelope,GaussianGeneralPolynomialValueName.rawZeroEnvelope,
    GaussianFastValueCut.rawEnvelope,Syn.shift,GaussianGeneralPolynomialEvaluation.subst_observationData,
    GaussianGeneralFTATrajectory.subst_nameData,subst_envelopeConstant,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using result

/-- Genuine generic regularity is derived from coefficient and point names. -/
theorem observation_regular (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular
      (GaussianGeneralPolynomialEvaluation.observationF a (GaussianGeneralFTATrajectory.nameF a))
      (GaussianGeneralPolynomialEvaluation.T a N (R a N h x) x)
      (GaussianGeneralPolynomialEvaluation.observationData N x (GaussianGeneralFTATrajectory.nameData N h x)) :=
  GaussianGeneralPolynomialEvaluation.observation_regular a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) (Prf.andE₁ hSource)
    (GaussianGeneralFTAName.name_fast a N k h x hSource)
    (GaussianGeneralFTAName.name_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x)

theorem generic_value_zero (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx] valueZero a N h x :=
  GaussianGeneralPolynomialValueName.envelope_to_value_zero a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) (envelopeConstant a N h x)
    (Prf.andE₁ hSource) (GaussianGeneralFTAName.name_fast a N k h x hSource)
    (GaussianGeneralFTAName.name_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x) (raw_envelope a N k h x hSource)

theorem generic_name_zero (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx] nameZero a N h x :=
  GaussianGeneralPolynomialValueName.envelope_to_name_zero a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) (envelopeConstant a N h x)
    (Prf.andE₁ hSource) (GaussianGeneralFTAName.name_fast a N k h x hSource)
    (GaussianGeneralFTAName.name_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x) (raw_envelope a N k h x hSource)

theorem value_name_zero_bound (a : PR 3) (N k h x t : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    bounded (ap2 (valueNameF a) t (valueNameData a N h x)) one (unit t) :=
  GaussianGeneralPolynomialValueName.program_zero_at (valueNameF a) (valueNameData a N h x) t
    (generic_name_zero a N k h x hSource)

theorem value_name_at (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    ap2 (valueNameF a) t (valueNameData a N h x) ≐ value a N h x t :=
  GaussianGeneralPolynomialValueName.name_at a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) t

theorem value_name_canonical (a : PR 3) (N h x t : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (valueNameF a) t (valueNameData a N h x)) :=
  GaussianGeneralPolynomialValueName.name_canonical a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) t

theorem value_name_fast (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (valueNameF a) (valueNameData a N h x) :=
  GaussianGeneralPolynomialValueName.name_fast a (GaussianGeneralFTATrajectory.nameF a)
    N (R a N h x) x (GaussianGeneralFTATrajectory.nameData N h x) (Prf.andE₁ hSource)
    (GaussianGeneralFTAName.name_fast a N k h x hSource)
    (GaussianGeneralFTAName.name_bounds a N k h x hSource)
    (GaussianGeneralFTAConstants.R_positive a N h x)

/-- The original source assumptions construct both the root point program
and the genuine general-polynomial value program, with its zero predicate. -/
theorem general_fta (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] sourceInput a N k h x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (GaussianGeneralFTATrajectory.nameF a)
      (GaussianGeneralFTATrajectory.nameData N h x) ⋏
    (GaussianRootApproximationWitness.pointBounds (GaussianGeneralFTATrajectory.nameF a)
      (R a N h x) (GaussianGeneralFTATrajectory.nameData N h x) ⋏
    (GaussianEuclideanDistanceName.pointCN (valueNameF a) (valueNameData a N h x) ⋏ nameZero a N h x)) :=
  .andI (GaussianGeneralFTAName.name_fast a N k h x hSource)
    (.andI (GaussianGeneralFTAName.name_bounds a N k h x hSource)
      (.andI (value_name_fast a N k h x hSource) (generic_name_zero a N k h x hSource)))

/-! Closed source and actual-program endpoints. All displayed numbers,
including degree, apartness witnesses and precision, are internal. -/

theorem actual_raw_observation_binding_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (GaussianGeneralPolynomialEvaluation.observationF a (GaussianGeneralFTATrajectory.nameF a)) (var 3)
      (GaussianGeneralPolynomialEvaluation.observationData (var 0) (var 2)
        (GaussianGeneralFTATrajectory.nameData (var 0) (var 1) (var 2))) ≐
      GaussianGeneralFTAPolynomialValueName.observation a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (raw_observation_at _ _ _ _ _)

theorem original_general_fta_raw_envelope_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianGeneralPolynomialValueName.rawEnvelope a (GaussianGeneralFTATrajectory.nameF a)
        (var 0) (var 3) (GaussianGeneralFTATrajectory.nameData (var 0) (var 2) (var 3))
        (envelopeConstant a (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (raw_envelope _ _ _ _ _ Prf.hyp0))

theorem original_general_polynomial_value_zero_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ valueZero a (var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (generic_value_zero _ _ _ _ _ Prf.hyp0))

theorem original_general_fta_program_zero_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      (GaussianEuclideanDistanceName.pointCN (GaussianGeneralFTATrajectory.nameF a)
        (GaussianGeneralFTATrajectory.nameData (var 0) (var 2) (var 3)) ⋏
      (GaussianRootApproximationWitness.pointBounds (GaussianGeneralFTATrajectory.nameF a)
        (R a (var 0) (var 2) (var 3)) (GaussianGeneralFTATrajectory.nameData (var 0) (var 2) (var 3)) ⋏
      (GaussianEuclideanDistanceName.pointCN (valueNameF a) (valueNameData a (var 0) (var 2) (var 3)) ⋏
        nameZero a (var 0) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (general_fta _ _ _ _ _ Prf.hyp0))

theorem original_general_polynomial_program_zero_bound_closed (a : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      bounded (ap2 (valueNameF a) (var 4) (valueNameData a (var 0) (var 2) (var 3)))
        one (unit (var 4))) :=
  closeUniv 5 (.impI (value_name_zero_bound _ _ _ _ _ _ Prf.hyp0))

theorem actual_value_name_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (valueNameF a) (var 3) (valueNameData a (var 0) (var 1) (var 2)) ≐
      value a (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (value_name_at _ _ _ _ _)

theorem actual_value_name_canonical_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalHorner.canonical
      (ap2 (valueNameF a) (var 3) (valueNameData a (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (value_name_canonical _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAValueZero
