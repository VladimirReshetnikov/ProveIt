import IPRADerivations.Analysis.Polynomials.Representation.GaussianPolynomialDegreePadding
import IPRADerivations.Analysis.Polynomials.Evaluation.GaussianGeneralPolynomialExtensionality

/-!
# Degree-independent general polynomial value names

Actual leading-zero padding preserves the raw Horner observation. The two
value programs keep their independently computed original and padded moduli;
zero raw discrepancy suffices for their name equivalence. Two original
polynomials of different numerical upper degrees are then compared at the
computed common degree N+M and transported back to the original programs.
All original coefficients, disks, data and precision shifts are retained.
No padding identity, output regularity or evaluation comparison is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDegreeExtensionality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianPolynomialDegreePadding (extensionF data)
open LeanProofs.IPRA.Analysis.GaussianGeneralPolynomialEvaluation (observation observationF observationData T)
open LeanProofs.IPRA.Analysis.GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonDegree (N M : PTm n) : PTm n := N+M

def coefficientEquivalent (a b : PR 3) (N M x w : PTm n) : Fm PTm n :=
  GaussianGeneralPolynomialExtensionality.coefficientEquivalent (extensionF a) (extensionF b)
    (commonDegree N M) (data N x) (data M w)

def input (a b : PR 3) (f g : PR 2) (N M U V x w y z : PTm n) : Fm PTm n :=
  GaussianGeneralPolynomialEvaluation.input a f N U x y ⋏
  (GaussianGeneralPolynomialEvaluation.input b g M V w z ⋏
    (coefficientEquivalent a b N M x w ⋏ diagonalEquivalent f g y z))

@[simp] theorem subst_commonDegree {m : ℕ} (σ : Fin n → PTm m) (N M : PTm n) :
    Syn.subst σ (commonDegree N M) = commonDegree (Syn.subst σ N) (Syn.subst σ M) := by simp [commonDegree]
@[simp] theorem subst_coefficientEquivalent {m : ℕ} (σ : Fin n → PTm m) (a b : PR 3) (N M x w : PTm n) :
    (coefficientEquivalent a b N M x w).subst σ =
      coefficientEquivalent a b (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) (Syn.subst σ w) := by
  simp [coefficientEquivalent]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (a b : PR 3) (f g : PR 2)
    (N M U V x w y z : PTm n) : (input a b f g N M U V x w y z).subst σ =
      input a b f g (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ U) (Syn.subst σ V)
        (Syn.subst σ x) (Syn.subst σ w) (Syn.subst σ y) (Syn.subst σ z) := by simp [input]

theorem common_left (N M : PTm n) : Γ ⊢[PRAAx] le N (commonDegree N M) := le_add_right N M

theorem common_right (N M : PTm n) : Γ ⊢[PRAAx] le M (commonDegree N M) :=
  le_congr (.eqRefl _) (add_comm M N) (le_add_right M N)

/-- The extended coefficient family is genuinely regular at every numerical
upper degree; point data and disk remain the original ones. -/
theorem padded_input (a : PR 3) (f : PR 2) (N P U x y : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialEvaluation.input (extensionF a) f P U (data N x) y :=
  .andI (GaussianPolynomialDegreePadding.extended_generalCN a N P x (Prf.andE₁ hInput)) (Prf.andE₂ hInput)

/-- This is the proved evaluator identity of the actual padding program,
instantiated at the actual point-name observation. -/
theorem padded_observation_at (a : PR 3) (f : PR 2) (N P x y s : PTm n)
    (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    observation (extensionF a) f P (data N x) y s ≐ observation a f N x y s :=
  GaussianPolynomialDegreePadding.padded_evaluation a N P s x (ap2 f s y) hNP

theorem raw_padding_at (a : PR 3) (f : PR 2) (N P x y s : PTm n)
    (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    ap2 (observationF a f) s (observationData N x y) ≐
      ap2 (observationF (extensionF a) f) s (observationData P (data N x) y) :=
  (GaussianGeneralPolynomialEvaluation.observation_at a f N x y s).eqTrans
    ((padded_observation_at a f N P x y s hNP).eqSymm.eqTrans
      (GaussianGeneralPolynomialEvaluation.observation_at (extensionF a) f P (data N x) y s).eqSymm)

/-- Zero discrepancy is derived from the real program identity, without
requiring canonical coefficient samples or equality of outer list codes. -/
theorem padding_raw_diagonal (a : PR 3) (f : PR 2) (N P x y : PTm n)
    (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal (observationF a f) (observationF (extensionF a) f)
      (observationData N x y) (observationData P (data N x) y) zero := by
  refine .allI ?_
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift N) (Syn.shift P) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hNP.shift
  simpa only [Syn.shift,GaussianGeneralPolynomialEvaluation.subst_observationData,
    GaussianPolynomialDegreePadding.subst_data,ConciseIPRA.PTm.subst_zero] using
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _)
      (raw_padding_at a f (Syn.shift N) (Syn.shift P) (Syn.shift x) (Syn.shift y) (var 0) hn)
      (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero
        (ap2 (observationF a f) (var 0) (observationData (Syn.shift N) (Syn.shift x) (Syn.shift y)))
        (unit (var 0)) (unit_positive _))

/-- Each actual value program retains its own numerical upper degree,
coefficient encoding and computed normalization modulus. -/
theorem padding_names_equivalent (a : PR 3) (f : PR 2) (N P U x y : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f)
      (GaussianGeneralPolynomialValueName.nameF (extensionF a) f)
      (GaussianGeneralPolynomialValueName.nameData a N U x y)
      (GaussianGeneralPolynomialValueName.nameData (extensionF a) P U (data N x) y) :=
  GaussianValueNormalizerExtensionality.normalized_names_equivalent (observationF a f) (observationF (extensionF a) f)
    (T a N U x) (T (extensionF a) P U (data N x))
    (observationData N x y) (observationData P (data N x) y) zero
    (GaussianGeneralPolynomialEvaluation.regular_of_input a f N U x y hInput)
    (GaussianGeneralPolynomialEvaluation.regular_of_input (extensionF a) f P U (data N x) y
      (padded_input a f N P U x y hInput)) (padding_raw_diagonal a f N P x y hNP)

theorem padding_zero_iff (a : PR 3) (f : PR 2) (N P U x y : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianGeneralPolynomialEvaluation.input a f N U x y)
    (hNP : Γ ⊢[PRAAx] le N P) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f N U x y)
      (GaussianGeneralPolynomialValueName.nameZero (extensionF a) f P U (data N x) y) :=
  GaussianNameEquivalence.cross_zero_iff _ _ _ _ (padding_names_equivalent a f N P U x y hInput hNP)

/-- All regularity and disk hypotheses of the common-degree theorem are
derived from the two original input bundles and the actual extension program. -/
theorem common_input (a b : PR 3) (f g : PR 2) (N M U V x w y z : PTm n)
    (hInput : Γ ⊢[PRAAx] input a b f g N M U V x w y z) : Γ ⊢[PRAAx]
    GaussianGeneralPolynomialExtensionality.input (extensionF a) (extensionF b) f g
      (commonDegree N M) U V (data N x) (data M w) y z :=
  .andI (padded_input a f N (commonDegree N M) U x y (Prf.andE₁ hInput))
    (.andI (padded_input b g M (commonDegree N M) V w z (Prf.andE₁ (Prf.andE₂ hInput)))
      (Prf.andE₂ (Prf.andE₂ hInput)))

theorem common_names_equivalent (a b : PR 3) (f g : PR 2) (N M U V x w y z : PTm n)
    (hInput : Γ ⊢[PRAAx] input a b f g N M U V x w y z) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianGeneralPolynomialValueName.nameF (extensionF a) f)
      (GaussianGeneralPolynomialValueName.nameF (extensionF b) g)
      (GaussianGeneralPolynomialValueName.nameData (extensionF a) (commonDegree N M) U (data N x) y)
      (GaussianGeneralPolynomialValueName.nameData (extensionF b) (commonDegree N M) V (data M w) z) :=
  GaussianGeneralPolynomialExtensionality.names_equivalent (extensionF a) (extensionF b) f g
    (commonDegree N M) U V (data N x) (data M w) y z (common_input a b f g N M U V x w y z hInput)

/-- The final programs use the ORIGINAL N and M and their ORIGINAL shifts,
rather than exposing a padded replacement as the desired conclusion. -/
theorem names_equivalent (a b : PR 3) (f g : PR 2) (N M U V x w y z : PTm n)
    (hInput : Γ ⊢[PRAAx] input a b f g N M U V x w y z) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF b g)
      (GaussianGeneralPolynomialValueName.nameData a N U x y)
      (GaussianGeneralPolynomialValueName.nameData b M V w z) := by
  have left := padding_names_equivalent a f N (commonDegree N M) U x y (Prf.andE₁ hInput) (common_left N M)
  have middle := common_names_equivalent a b f g N M U V x w y z hInput
  have right := GaussianNameEquivalence.cross_symm _ _ _ _
    (padding_names_equivalent b g M (commonDegree N M) V w z (Prf.andE₁ (Prf.andE₂ hInput)) (common_right N M))
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ left middle) right

theorem zero_iff (a b : PR 3) (f g : PR 2) (N M U V x w y z : PTm n)
    (hInput : Γ ⊢[PRAAx] input a b f g N M U V x w y z) : Γ ⊢[PRAAx]
    Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f N U x y)
      (GaussianGeneralPolynomialValueName.nameZero b g M V w z) :=
  GaussianNameEquivalence.cross_zero_iff _ _ _ _ (names_equivalent a b f g N M U V x w y z hInput)

/-! The closed interfaces retain every degree, disk and data argument as
an internal numerical variable. Only the fixed programs are external. -/

theorem common_degree_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (commonDegree (var 0) (var 1)) ⋏ le (var 1) (commonDegree (var 0) (var 1))) :=
  closeUniv 2 (.andI (common_left _ _) (common_right _ _))

theorem padded_input_contract_closed (a : PR 3) (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 2) (var 3) (var 4) ⟶
      GaussianGeneralPolynomialEvaluation.input (extensionF a) f (var 1) (var 2) (data (var 0) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (padded_input a f _ _ _ _ _ Prf.hyp0))

theorem actual_raw_padding_program_closed (a : PR 3) (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 0) (var 1) ⟶
      ap2 (observationF a f) (var 4) (observationData (var 0) (var 2) (var 3)) ≐
        ap2 (observationF (extensionF a) f) (var 4)
          (observationData (var 1) (data (var 0) (var 2)) (var 3))) :=
  closeUniv 5 (.impI (raw_padding_at a f _ _ _ _ _ Prf.hyp0))

theorem exact_padding_names_equivalent_closed (a : PR 3) (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 2) (var 3) (var 4) ⟶ le (var 0) (var 1) ⟶
      crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f)
        (GaussianGeneralPolynomialValueName.nameF (extensionF a) f)
        (GaussianGeneralPolynomialValueName.nameData a (var 0) (var 2) (var 3) (var 4))
        (GaussianGeneralPolynomialValueName.nameData (extensionF a) (var 1) (var 2)
          (data (var 0) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (padding_names_equivalent a f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem exact_padding_zero_iff_closed (a : PR 3) (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGeneralPolynomialEvaluation.input a f (var 0) (var 2) (var 3) (var 4) ⟶ le (var 0) (var 1) ⟶
      Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f (var 0) (var 2) (var 3) (var 4))
        (GaussianGeneralPolynomialValueName.nameZero (extensionF a) f (var 1) (var 2)
          (data (var 0) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (padding_zero_iff a f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem arbitrary_degree_polynomial_extensionality_closed (a b : PR 3) (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input a b f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        crossEquivalent (GaussianGeneralPolynomialValueName.nameF a f) (GaussianGeneralPolynomialValueName.nameF b g)
          (GaussianGeneralPolynomialValueName.nameData a (var 0) (var 2) (var 4) (var 6))
          (GaussianGeneralPolynomialValueName.nameData b (var 1) (var 3) (var 5) (var 7))) :=
  closeUniv 8 (.impI (names_equivalent a b f g _ _ _ _ _ _ _ _ Prf.hyp0))

theorem arbitrary_degree_polynomial_zero_extensionality_closed (a b : PR 3) (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input a b f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        Fm.iff (GaussianGeneralPolynomialValueName.nameZero a f (var 0) (var 2) (var 4) (var 6))
          (GaussianGeneralPolynomialValueName.nameZero b g (var 1) (var 3) (var 5) (var 7))) :=
  closeUniv 8 (.impI (zero_iff a b f g _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDegreeExtensionality
