import IPRADerivations.Analysis.GaussianGeneralPolynomialValueName
import IPRADerivations.Analysis.GaussianValueNormalizerExtensionality

/-!
# Extensionality of actual general polynomial value names

Equivalent original coefficient names and equivalent bounded Gaussian point
names give equivalent polynomial value programs. The two numerical disks,
data encodings and computed normalizer shifts remain independent. A common
disk is used only in the proof of the raw observation bound. All original
coefficients, including the leading one, are retained, and degree zero is
allowed. Different upper degrees require a separate actual padding adapter.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialExtensionality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open LeanProofs.IPRA.Analysis.GaussianGeneralCoefficientNames (generalCN)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialEvaluation (observation observationF observationData T)
open LeanProofs.IPRA.Analysis.GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (pointBounds)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientDiagonal (a b : PR 3) (i x w : PTm n) : Fm PTm n := .all
  (distanceBounded (ap3 a (Syn.shift i) (var 0) (Syn.shift x))
    (ap3 b (Syn.shift i) (var 0) (Syn.shift w)) two (unit (var 0)))

def coefficientEquivalent (a b : PR 3) (N x w : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift N) ⟶ coefficientDiagonal a b (var 0) (Syn.shift x) (Syn.shift w))

def disk (U V : PTm n) : PTm n := U+V+one
def envelope (b : PR 3) (N U V w : PTm n) : PTm n := two*T b N (disk U V) w

def input (a b : PR 3) (f g : PR 2) (N U V x w y z : PTm n) : Fm PTm n :=
  GaussianGeneralPolynomialEvaluation.input a f N U x y ⋏
  (GaussianGeneralPolynomialEvaluation.input b g N V w z ⋏
    (coefficientEquivalent a b N x w ⋏ diagonalEquivalent f g y z))

@[simp] theorem subst_coefficientDiagonal {m : ℕ} (σ : Fin n → PTm m) (a b : PR 3) (i x w : PTm n) :
    (coefficientDiagonal a b i x w).subst σ =
      coefficientDiagonal a b (Syn.subst σ i) (Syn.subst σ x) (Syn.subst σ w) := by
  simp [coefficientDiagonal,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_coefficientEquivalent {m : ℕ} (σ : Fin n → PTm m) (a b : PR 3) (N x w : PTm n) :
    (coefficientEquivalent a b N x w).subst σ =
      coefficientEquivalent a b (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ w) := by
  simp [coefficientEquivalent,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (U V : PTm n) :
    Syn.subst σ (disk U V) = disk (Syn.subst σ U) (Syn.subst σ V) := by simp [disk]
@[simp] theorem subst_envelope {m : ℕ} (σ : Fin n → PTm m) (b : PR 3) (N U V w : PTm n) :
    Syn.subst σ (envelope b N U V w) =
      envelope b (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ V) (Syn.subst σ w) := by simp [envelope]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (a b : PR 3) (f g : PR 2)
    (N U V x w y z : PTm n) : (input a b f g N U V x w y z).subst σ =
      input a b f g (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ V)
        (Syn.subst σ x) (Syn.subst σ w) (Syn.subst σ y) (Syn.subst σ z) := by simp [input]

theorem coefficient_at (a b : PR 3) (N x w i m : PTm n)
    (h : Γ ⊢[PRAAx] coefficientEquivalent a b N x w) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (ap3 a i m x) (ap3 b i m w) two (unit m) := by
  have rule : Γ ⊢[PRAAx] le i N ⟶ coefficientDiagonal a b i x w := by
    simpa [coefficientEquivalent] using h.allE i
  simpa [coefficientDiagonal] using (Prf.impE rule hi).allE m

theorem coefficient_reflexive (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx]
    coefficientEquivalent a a N x x := by
  refine .allI (.impI (.allI ?_))
  have h := GaussianRationalReciprocal.bound_congr
    (Γ := ((le (var 0) (Syn.shift N) :: Γ.map Fm.shift).map Fm.shift))
    (GaussianCoefficientNormOrder.qsub_self
      (ap3 a (var 1) (var 0) (Syn.shift (Syn.shift x)))).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded two (unit (var 0)) (unit_positive _))
  simpa [coefficientEquivalent,coefficientDiagonal,GaussianRationalMetric.distanceBounded,Syn.shift] using h

theorem disk_left (U V : PTm n) : Γ ⊢[PRAAx] le U (disk U V) :=
  le_congr (.eqRefl _) (by unfold disk; ipra_ring) (le_add_right U (V+one))
theorem disk_right (U V : PTm n) : Γ ⊢[PRAAx] le V (disk U V) :=
  le_congr (.eqRefl _) (by unfold disk; ipra_ring) (le_add_right V (U+one))
theorem disk_positive (U V : PTm n) : Γ ⊢[PRAAx] le one (disk U V) :=
  le_congr (.eqRefl _) (by unfold disk; ipra_ring) (le_add_right one (U+V))

theorem widen_point (f : PR 2) (U W y m : PTm n)
    (h : Γ ⊢[PRAAx] pointBounds f U y) (hUW : Γ ⊢[PRAAx] le U W) : Γ ⊢[PRAAx]
    bounded (ap2 f m y) W one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl _) (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) hUW)
    (GaussianRootApproximationWitness.point_at f U y m h)

theorem sample_errors (a b : PR 3) (N x w m : PTm n)
    (h : Γ ⊢[PRAAx] coefficientEquivalent a b N x w) : Γ ⊢[PRAAx]
    GaussianRationalAllCoefficientPerturbation.coefficientErrors
      (GaussianGeneralPolynomialSamples.sample a N m x)
      (GaussianGeneralPolynomialSamples.sample b N m w) N two (unit m) := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx]
      coefficientEquivalent a b (Syn.shift N) (Syn.shift x) (Syn.shift w) := by
    simpa only [Fm.shift,subst_coefficientEquivalent,Syn.shift] using h.shift
  have e := coefficient_at (Γ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    a b (Syn.shift N) (Syn.shift x) (Syn.shift w)
    (PTm.monus (Syn.shift N) (var 0)) (Syn.shift m) hs.wk
    (GaussianMonicResidualRadius.monus_le_left _ _)
  simpa only [Syn.shift,GaussianGeneralPolynomialSamples.subst_sample,subst_unit,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using distance_congr
    (GaussianGeneralPolynomialSamples.sample_lookup a (Syn.shift N) (Syn.shift m) (Syn.shift x) (var 0) Prf.hyp0).eqSymm
    (GaussianGeneralPolynomialSamples.sample_lookup b (Syn.shift N) (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0).eqSymm
    (.eqRefl _) (.eqRefl _) e

/-- Both variations are bounded on a proof disk. The programs keep their own U and V. -/
theorem observation_diagonal_at (a b : PR 3) (f g : PR 2) (N U V x w y z m : PTm n)
    (h : Γ ⊢[PRAAx] input a b f g N U V x w y z) : Γ ⊢[PRAAx]
    distanceBounded (observation a f N x y m) (observation b g N w z m)
      (envelope b N U V w) (unit m) := by
  have hA := Prf.andE₁ h
  have hB := Prf.andE₁ (Prf.andE₂ h)
  have hCoeff := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hPoint := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have fDisk := widen_point f U (disk U V) y m
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hA))) (disk_left U V)
  have gDisk := widen_point g V (disk U V) z m
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hB))) (disk_right U V)
  have first := GaussianRationalAllCoefficientPerturbation.evaluation_bound
    (GaussianGeneralPolynomialSamples.sample a N m x) (GaussianGeneralPolynomialSamples.sample b N m w)
    (ap2 f m y) N (disk U V) two (unit m)
    (GaussianGeneralPolynomialSamples.sample_length a N m x)
    (GaussianGeneralPolynomialSamples.sample_length b N m w)
    (disk_positive U V) (unit_positive m) (sample_errors a b N x w m hCoeff) fDisk
  have second := GaussianRationalHornerLipschitz.evaluation_bound
    (GaussianGeneralPolynomialSamples.sample b N m w) (ap2 f m y) (ap2 g m z)
    N (disk U V) (GaussianGeneralPolynomialEvaluation.A b N w) two (unit m)
    (GaussianGeneralPolynomialSamples.sample_length b N m w)
    (GaussianGeneralPolynomialEvaluation.sample_coefficients b N m w (Prf.andE₁ hB))
    fDisk gDisk (unit_positive m) (GaussianNameEquivalence.diagonal_at f g y z m hPoint)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold envelope T GaussianGeneralPolynomialEvaluation.C GaussianGeneralPolynomialEvaluation.M; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ (unit_positive m) first second)

theorem raw_diagonal (a b : PR 3) (f g : PR 2) (N U V x w y z : PTm n)
    (h : Γ ⊢[PRAAx] input a b f g N U V x w y z) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal (observationF a f) (observationF b g)
      (observationData N x y) (observationData N w z) (envelope b N U V w) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input a b f g (Syn.shift N) (Syn.shift U) (Syn.shift V)
      (Syn.shift x) (Syn.shift w) (Syn.shift y) (Syn.shift z) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using h.shift
  simpa only [Syn.shift,GaussianGeneralPolynomialEvaluation.subst_observationData,subst_envelope] using
    distance_congr
      (GaussianGeneralPolynomialEvaluation.observation_at a f (Syn.shift N) (Syn.shift x) (Syn.shift y) (var 0)).eqSymm
      (GaussianGeneralPolynomialEvaluation.observation_at b g (Syn.shift N) (Syn.shift w) (Syn.shift z) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _)
      (observation_diagonal_at a b f g (Syn.shift N) (Syn.shift U) (Syn.shift V)
        (Syn.shift x) (Syn.shift w) (Syn.shift y) (Syn.shift z) (var 0) hs)

theorem names_equivalent (a b : PR 3) (f g : PR 2) (N U V x w y z : PTm n)
    (h : Γ ⊢[PRAAx] input a b f g N U V x w y z) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF b g)
      (GaussianGeneralPolynomialValueName.nameData a N U x y)
      (GaussianGeneralPolynomialValueName.nameData b N V w z) :=
  GaussianValueNormalizerExtensionality.normalized_names_equivalent (observationF a f) (observationF b g)
    (T a N U x) (T b N V w) (observationData N x y) (observationData N w z) (envelope b N U V w)
    (GaussianGeneralPolynomialEvaluation.regular_of_input a f N U x y (Prf.andE₁ h))
    (GaussianGeneralPolynomialEvaluation.regular_of_input b g N V w z (Prf.andE₁ (Prf.andE₂ h)))
    (raw_diagonal a b f g N U V x w y z h)

theorem zero_iff (a b : PR 3) (f g : PR 2) (N U V x w y z : PTm n)
    (h : Γ ⊢[PRAAx] input a b f g N U V x w y z) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f N U x y)
      (GaussianGeneralPolynomialValueName.nameZero b g N V w z) :=
  GaussianNameEquivalence.cross_zero_iff _ _ _ _ (names_equivalent a b f g N U V x w y z h)

/-- Point extensionality needs no supplied reflexivity contract for the coefficients. -/
theorem point_input (a : PR 3) (f g : PR 2) (N U V x y z : PTm n)
    (hF : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hG : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a g N V x z)
    (hPoint : Γ ⊢[PRAAx] diagonalEquivalent f g y z) : Γ ⊢[PRAAx]
    input a a f g N U V x x y z :=
  .andI hF (.andI hG (.andI (coefficient_reflexive a N x) hPoint))

theorem point_names_equivalent (a : PR 3) (f g : PR 2) (N U V x y z : PTm n)
    (hF : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hG : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a g N V x z)
    (hPoint : Γ ⊢[PRAAx] diagonalEquivalent f g y z) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF a g)
      (GaussianGeneralPolynomialValueName.nameData a N U x y)
      (GaussianGeneralPolynomialValueName.nameData a N V x z) :=
  names_equivalent a a f g N U V x x y z (point_input a f g N U V x y z hF hG hPoint)

theorem point_zero_iff (a : PR 3) (f g : PR 2) (N U V x y z : PTm n)
    (hF : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hG : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a g N V x z)
    (hPoint : Γ ⊢[PRAAx] diagonalEquivalent f g y z) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f N U x y)
      (GaussianGeneralPolynomialValueName.nameZero a g N V x z) :=
  zero_iff a a f g N U V x x y z (point_input a f g N U V x y z hF hG hPoint)

/-- Changing only the admissible disk changes neither the represented value nor zero. -/
theorem disk_names_equivalent (a : PR 3) (f : PR 2) (N U V x y : PTm n)
    (hU : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hV : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N V x y) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF a f)
      (GaussianGeneralPolynomialValueName.nameData a N U x y)
      (GaussianGeneralPolynomialValueName.nameData a N V x y) :=
  point_names_equivalent a f f N U V x y y hU hV (GaussianNameEquivalence.diagonal_refl f y)

theorem disk_zero_iff (a : PR 3) (f : PR 2) (N U V x y : PTm n)
    (hU : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hV : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N V x y) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f N U x y)
      (GaussianGeneralPolynomialValueName.nameZero a f N V x y) :=
  point_zero_iff a f f N U V x y y hU hV (GaussianNameEquivalence.diagonal_refl f y)

theorem general_polynomial_extensionality_closed (a b : PR 3) (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input a b f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF b g)
          (GaussianGeneralPolynomialValueName.nameData a (var 0) (var 1) (var 3) (var 5))
          (GaussianGeneralPolynomialValueName.nameData b (var 0) (var 2) (var 4) (var 6))) :=
  closeUniv 7 (.impI (names_equivalent a b f g _ _ _ _ _ _ _ Prf.hyp0))

theorem general_polynomial_zero_extensionality_closed (a b : PR 3) (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input a b f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f (var 0) (var 1) (var 3) (var 5))
          (GaussianGeneralPolynomialValueName.nameZero b g (var 0) (var 2) (var 4) (var 6))) :=
  closeUniv 7 (.impI (zero_iff a b f g _ _ _ _ _ _ _ Prf.hyp0))

theorem polynomial_disk_independence_closed (a : PR 3) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 1) (var 3) (var 4) ⟶
       GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 2) (var 3) (var 4) ⟶
        crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF a f)
          (GaussianGeneralPolynomialValueName.nameData a (var 0) (var 1) (var 3) (var 4))
          (GaussianGeneralPolynomialValueName.nameData a (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (disk_names_equivalent a f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem polynomial_disk_zero_independence_closed (a : PR 3) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 1) (var 3) (var 4) ⟶
       GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 2) (var 3) (var 4) ⟶
        Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f (var 0) (var 1) (var 3) (var 4))
          (GaussianGeneralPolynomialValueName.nameZero a f (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (disk_zero_iff a f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialExtensionality
