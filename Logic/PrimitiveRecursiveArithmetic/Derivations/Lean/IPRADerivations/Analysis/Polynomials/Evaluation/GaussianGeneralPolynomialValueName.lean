import IPRADerivations.Analysis.Polynomials.Evaluation.GaussianGeneralPolynomialEvaluation
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual value names of general coefficient and point names

The raw observations evaluate every original coefficient, including the
possibly zero leading coefficient. Genuine coefficient and point regularity
on a bounded disk supply their numerical modulus. The actual generic PR2
normalizer retains separate coefficient and point data. Its canonical
recoding requires no canonical input-code hypothesis.

A raw envelope K/2^s implies zero of the normalized name by finite slack
removal at each fixed query. K is arbitrary; no comparison with the
normalization modulus is assumed. These are finite-code name statements,
without an assumed polynomial operation on a quotient completion.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialValueName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (canonical)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit subst_unit)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def normalizedZero (f : PR 2) (L x : PTm n) : Fm PTm n := .all
  (bounded (GaussianFastValueCut.value f (Syn.shift L) (Syn.shift x) (var 0)) one (unit (var 0)))

def programZero (f : PR 2) (x : PTm n) : Fm PTm n := .all
  (bounded (ap2 f (var 0) (Syn.shift x)) one (unit (var 0)))

def rawZeroEnvelope (f : PR 2) (x K : PTm n) : Fm PTm n :=
  GaussianFastValueCut.rawEnvelope f x zero one K

@[simp] theorem subst_normalizedZero {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L x : PTm n) :
    (normalizedZero f L x).subst σ = normalizedZero f (Syn.subst σ L) (Syn.subst σ x) := by
  simp [normalizedZero,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_programZero {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    (programZero f x).subst σ = programZero f (Syn.subst σ x) := by
  simp [programZero,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_rawZeroEnvelope {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x K : PTm n) :
    (rawZeroEnvelope f x K).subst σ = rawZeroEnvelope f (Syn.subst σ x) (Syn.subst σ K) := by
  simp [rawZeroEnvelope]

theorem normalized_zero_at (f : PR 2) (L x k : PTm n)
    (h : Γ ⊢[PRAAx] normalizedZero f L x) : Γ ⊢[PRAAx]
    bounded (GaussianFastValueCut.value f L x k) one (unit k) := by
  simpa [normalizedZero] using h.allE k

theorem program_zero_at (f : PR 2) (x k : PTm n)
    (h : Γ ⊢[PRAAx] programZero f x) : Γ ⊢[PRAAx]
    bounded (ap2 f k x) one (unit k) := by
  simpa [programZero] using h.allE k

theorem normalized_zero_to_program_zero (f : PR 2) (L x : PTm n)
    (h : Γ ⊢[PRAAx] normalizedZero f L x) : Γ ⊢[PRAAx]
    programZero (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameData L x) := by
  refine .allI ?_
  have hz : Γ.map Fm.shift ⊢[PRAAx] normalizedZero f (Syn.shift L) (Syn.shift x) := by
    simpa only [Fm.shift,subst_normalizedZero,Syn.shift] using h.shift
  simpa only [programZero,Syn.shift,GaussianFastValueCut.subst_nameData] using
    GaussianRationalReciprocal.bound_congr
      (GaussianFastValueCut.name_at f (Syn.shift L) (Syn.shift x) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (normalized_zero_at f _ _ (var 0) hz)

theorem program_zero_to_normalized_zero (f : PR 2) (L x : PTm n)
    (h : Γ ⊢[PRAAx] programZero (GaussianFastValueCut.nameF f)
      (GaussianFastValueCut.nameData L x)) : Γ ⊢[PRAAx] normalizedZero f L x := by
  refine .allI ?_
  have hz : Γ.map Fm.shift ⊢[PRAAx] programZero (GaussianFastValueCut.nameF f)
      (GaussianFastValueCut.nameData (Syn.shift L) (Syn.shift x)) := by
    simpa only [Fm.shift,subst_programZero,GaussianFastValueCut.subst_nameData,Syn.shift] using h.shift
  exact GaussianRationalReciprocal.bound_congr
    (GaussianFastValueCut.name_at f (Syn.shift L) (Syn.shift x) (var 0))
    (.eqRefl _) (.eqRefl _) (program_zero_at _ _ (var 0) hz)

theorem normalized_zero_iff_program_zero (f : PR 2) (L x : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (normalizedZero f L x)
      (programZero (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameData L x)) :=
  .andI (.impI (normalized_zero_to_program_zero f L x Prf.hyp0))
    (.impI (program_zero_to_normalized_zero f L x Prf.hyp0))

/-- The all-slack theorem removes arbitrary K at each fixed raw query.
The precision shift depends only on L; no L >= K premise occurs. -/
theorem raw_envelope_value_zero (f : PR 2) (L x K : PTm n)
    (hReg : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x)
    (hEnv : Γ ⊢[PRAAx] rawZeroEnvelope f x K) : Γ ⊢[PRAAx] normalizedZero f L x := by
  refine .allI ?_
  have reg : Γ.map Fm.shift ⊢[PRAAx] GaussianFastValueCut.regular f (Syn.shift L) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianFastValueCut.subst_regular,Syn.shift] using hReg.shift
  have env : Γ.map Fm.shift ⊢[PRAAx] rawZeroEnvelope f (Syn.shift x) (Syn.shift K) := by
    simpa only [Fm.shift,subst_rawZeroEnvelope,Syn.shift] using hEnv.shift
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianFastValueCut.value_cut_at f (Syn.shift L) (Syn.shift x) zero one
      (Syn.shift K) (var 0) reg (le_refl one) env)

theorem raw_envelope_program_zero (f : PR 2) (L x K : PTm n)
    (hReg : Γ ⊢[PRAAx] GaussianFastValueCut.regular f L x)
    (hEnv : Γ ⊢[PRAAx] rawZeroEnvelope f x K) : Γ ⊢[PRAAx]
    programZero (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameData L x) :=
  normalized_zero_to_program_zero f L x (raw_envelope_value_zero f L x K hReg hEnv)

def value (a : PR 3) (point : PR 2) (N U x y k : PTm n) : PTm n :=
  GaussianFastValueCut.value (GaussianGeneralPolynomialEvaluation.observationF a point)
    (GaussianGeneralPolynomialEvaluation.T a N U x)
    (GaussianGeneralPolynomialEvaluation.observationData N x y) k

def exponent (a : PR 3) (N U x k : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (GaussianGeneralPolynomialEvaluation.T a N U x) k

def nameF (a : PR 3) (point : PR 2) : PR 2 :=
  GaussianFastValueCut.nameF (GaussianGeneralPolynomialEvaluation.observationF a point)

def nameData (a : PR 3) (N U x y : PTm n) : PTm n :=
  GaussianFastValueCut.nameData (GaussianGeneralPolynomialEvaluation.T a N U x)
    (GaussianGeneralPolynomialEvaluation.observationData N x y)

def valueZero (a : PR 3) (point : PR 2) (N U x y : PTm n) : Fm PTm n :=
  normalizedZero (GaussianGeneralPolynomialEvaluation.observationF a point)
    (GaussianGeneralPolynomialEvaluation.T a N U x)
    (GaussianGeneralPolynomialEvaluation.observationData N x y)

def nameZero (a : PR 3) (point : PR 2) (N U x y : PTm n) : Fm PTm n :=
  programZero (nameF a point) (nameData a N U x y)

def rawEnvelope (a : PR 3) (point : PR 2) (N x y K : PTm n) : Fm PTm n :=
  rawZeroEnvelope (GaussianGeneralPolynomialEvaluation.observationF a point)
    (GaussianGeneralPolynomialEvaluation.observationData N x y) K

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N U x y k : PTm n) :
    Syn.subst σ (value a point N U x y k) = value a point (Syn.subst σ N) (Syn.subst σ U)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ k) := by simp [value]

@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x k : PTm n) :
    Syn.subst σ (exponent a N U x k) = exponent a (Syn.subst σ N) (Syn.subst σ U)
      (Syn.subst σ x) (Syn.subst σ k) := by simp [exponent]

@[simp] theorem subst_nameData {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x y : PTm n) :
    Syn.subst σ (nameData a N U x y) = nameData a (Syn.subst σ N) (Syn.subst σ U)
      (Syn.subst σ x) (Syn.subst σ y) := by simp [nameData]

@[simp] theorem subst_valueZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N U x y : PTm n) :
    (valueZero a point N U x y).subst σ = valueZero a point (Syn.subst σ N) (Syn.subst σ U)
      (Syn.subst σ x) (Syn.subst σ y) := by simp [valueZero]

@[simp] theorem subst_nameZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N U x y : PTm n) :
    (nameZero a point N U x y).subst σ = nameZero a point (Syn.subst σ N) (Syn.subst σ U)
      (Syn.subst σ x) (Syn.subst σ y) := by simp [nameZero]

@[simp] theorem subst_rawEnvelope {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N x y K : PTm n) :
    (rawEnvelope a point N x y K).subst σ = rawEnvelope a point (Syn.subst σ N)
      (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ K) := by simp [rawEnvelope]

theorem name_at (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF a point) k (nameData a N U x y) ≐ value a point N U x y k :=
  GaussianFastValueCut.name_at _ _ _ _

/-- Literal binding to the actual all-coefficient Horner observation at
the computed precision, retaining the value-preserving canonical recode. -/
theorem value_observation (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    value a point N U x y k ≐ GaussianFastValueCut.recode
      (GaussianGeneralPolynomialEvaluation.observation a point N x y (exponent a N U x k)) := by
  have h := GaussianGeneralPolynomialEvaluation.observation_at (Γ := Γ) a point N x y (exponent a N U x k)
  ipra_congr (GaussianFastValueCut.recode (var 0) : PTm 1) with
    [h] using [value, exponent, GaussianFastValueCut.value]

theorem name_observation (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF a point) k (nameData a N U x y) ≐ GaussianFastValueCut.recode
      (GaussianGeneralPolynomialEvaluation.observation a point N x y (exponent a N U x k)) :=
  (name_at a point N U x y k).eqTrans (value_observation a point N U x y k)

theorem name_canonical (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 (nameF a point) k (nameData a N U x y)) :=
  GaussianFastValueCut.name_canonical _ _ _ _

theorem value_canonical (a : PR 3) (point : PR 2) (N U x y k : PTm n) : Γ ⊢[PRAAx]
    canonical (value a point N U x y k) := GaussianFastValueCut.recode_canonical _

theorem name_fast (a : PR 3) (point : PR 2) (N U x y : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    pointCN (nameF a point) (nameData a N U x y) :=
  GaussianFastValueCut.name_fast _ _ _
    (GaussianGeneralPolynomialEvaluation.observation_regular a point N U x y hCN hPoint hBounds hU)

theorem value_zero_iff_name_zero (a : PR 3) (point : PR 2) (N U x y : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (valueZero a point N U x y) (nameZero a point N U x y) :=
  normalized_zero_iff_program_zero _ _ _

theorem envelope_to_value_zero (a : PR 3) (point : PR 2) (N U x y K : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope a point N x y K) : Γ ⊢[PRAAx] valueZero a point N U x y :=
  raw_envelope_value_zero _ _ _ K
    (GaussianGeneralPolynomialEvaluation.observation_regular a point N U x y hCN hPoint hBounds hU) hEnv

theorem envelope_to_name_zero (a : PR 3) (point : PR 2) (N U x y K : PTm n)
    (hCN : Γ ⊢[PRAAx] generalCN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point y)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U y) (hU : Γ ⊢[PRAAx] le one U)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope a point N x y K) : Γ ⊢[PRAAx] nameZero a point N U x y :=
  raw_envelope_program_zero _ _ _ K
    (GaussianGeneralPolynomialEvaluation.observation_regular a point N U x y hCN hPoint hBounds hU) hEnv

theorem general_polynomial_name_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGeneralPolynomialEvaluation.input a point (var 0) (var 1) (var 2) (var 3) ⟶
      pointCN (nameF a point) (nameData a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_fast _ _ _ _ _ _ (.andE₁ Prf.hyp0) (.andE₁ (.andE₂ Prf.hyp0))
    (.andE₁ (.andE₂ (.andE₂ Prf.hyp0))) (.andE₂ (.andE₂ (.andE₂ Prf.hyp0)))))

theorem general_polynomial_zero_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (valueZero a point (var 0) (var 1) (var 2) (var 3))
      (nameZero a point (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (value_zero_iff_name_zero _ _ _ _ _ _)

theorem general_polynomial_envelope_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGeneralPolynomialEvaluation.input a point (var 0) (var 1) (var 2) (var 3) ⟶
      rawEnvelope a point (var 0) (var 2) (var 3) (var 4) ⟶
        nameZero a point (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (envelope_to_name_zero _ _ _ _ _ _ _
    (.andE₁ Prf.hyp1) (.andE₁ (.andE₂ Prf.hyp1))
    (.andE₁ (.andE₂ (.andE₂ Prf.hyp1))) (.andE₂ (.andE₂ (.andE₂ Prf.hyp1))) Prf.hyp0)))

theorem general_polynomial_value_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 (nameF a point) (var 4) (nameData a (var 0) (var 1) (var 2) (var 3)) ≐
      value a point (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (name_at _ _ _ _ _ _ _)

theorem general_polynomial_value_canonical_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (canonical (ap2 (nameF a point) (var 4) (nameData a (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 5 (name_canonical _ _ _ _ _ _ _)

theorem arbitrary_envelope_zero_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianFastValueCut.regular f (var 0) (var 1) ⟶ rawZeroEnvelope f (var 1) (var 2) ⟶
      programZero (GaussianFastValueCut.nameF f) (GaussianFastValueCut.nameData (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (raw_envelope_program_zero _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialValueName
