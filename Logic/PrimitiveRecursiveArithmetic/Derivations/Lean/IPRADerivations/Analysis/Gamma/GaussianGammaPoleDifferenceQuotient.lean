import IPRADerivations.Analysis.Gamma.GaussianGammaLocalPoleFormula
import IPRADerivations.Analysis.Gamma.GaussianGammaPoleReciprocalFactor
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# Literal division in the original Gamma-pole difference quotient

On the original nonzero encoded open unit disk, the actual reciprocal
of h/B times the original P(-j+h/B) name agrees with the SAME original
factored quotient program. The checked puncture certificate licenses
the actual reciprocal; no divided output identity is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleDifferenceQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaPoleReciprocalFactor (quotientF quotientData factoredF factoredData)
open GaussianGammaLocalPoleGuards (center)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalReciprocal (reciprocal)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (normSq)
open GaussianRationalSyntheticDivision (qone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (h B : PTm n) : Fm PTm n := le one B ⋏ (le one (normSq h) ⋏ lt (normSq h) (B*B))
def divisionF : PR 2 := multiplyF constantF GaussianGammaC7Name.nameF
def divisionData (h B j : PTm n) : PTm n := multiplyData constantF GaussianGammaC7Name.nameF
  (reciprocal (ofGaussian h B)) (GaussianGammaC7Name.data (center h B j) (succ j) B)
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (h B : PTm n) :
    (input h B).subst σ = input (Syn.subst σ h) (Syn.subst σ B) := by simp [input]
@[simp] theorem subst_divisionData {l : ℕ} (σ : Fin n → PTm l) (h B j : PTm n) :
    Syn.subst σ (divisionData h B j) = divisionData (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ j) := by simp [divisionData]

theorem step_disk (h B : PTm n) (hi : Γ ⊢[PRAAx] input h B) : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h B :=
  le_trans (le_succ_self (normSq h)) hi.andE₂.andE₂

theorem actual_step_inverse (h B : PTm n) (hi : Γ ⊢[PRAAx] input h B) : Γ ⊢[PRAAx]
    qmul (reciprocal (ofGaussian h B)) (ofGaussian h B) ≐ qone :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    (GaussianGammaPoleMultiplier.step_inverse h B one (GaussianGammaLocalPoleFormula.punctureUpper B)
      (GaussianGammaLocalPoleFormula.punctureDenominator B) hi.andE₁ (le_refl one)
      (GaussianGammaLocalPoleFormula.puncture_denominator_positive B hi.andE₁)
      (GaussianGammaLocalPoleFormula.actual_puncture_certificate h B hi.andE₁ hi.andE₂.andE₁ hi.andE₂.andE₂))

theorem division_regular (h B j : PTm n) (hi : Γ ⊢[PRAAx] input h B) : Γ ⊢[PRAAx] pointCN divisionF (divisionData h B j) :=
  multiply_fast _ _ _ _ (constant_regular _)
    (GaussianGammaC7Name.name_regular _ _ _ (GaussianGammaLocalPoleGuards.center_source_disk h B j hi.andE₁ (step_disk h B hi)))

theorem constant_unit_cross (c y : PTm n) (e : Γ ⊢[PRAAx] c ≐ qone) : Γ ⊢[PRAAx]
    crossEquivalent constantF GaussianNameRingLaws.oneF c y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (GaussianNameRingLaws.one_fast y)
  refine .allI ?_
  have es : Γ.map Fm.shift ⊢[PRAAx] Syn.shift c ≐ qone := by simpa [Fm.shift,Syn.shift] using e.shift
  have actual : Γ.map Fm.shift ⊢[PRAAx] ap2 constantF (var 0) (Syn.shift c) ≐ ap2 GaussianNameRingLaws.oneF (var 0) (Syn.shift y) :=
    (GaussianGammaCanonicalExponent.constant_at _ _).eqTrans (es.eqTrans (GaussianNameRingLaws.one_at _ _).eqSymm)
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using actual

/-- The source C23 difference quotient is the actual original P sampler
multiplied by the actual reciprocal step, at every nonzero encoded h. -/
theorem original_C23_literal_difference_quotient (h B j : PTm n) (hi : Γ ⊢[PRAAx] input h B) : Γ ⊢[PRAAx]
    crossEquivalent divisionF quotientF (divisionData h B j) (quotientData h B j) := by
  let P := GaussianGammaC7Name.nameF
  let z := GaussianGammaC7Name.data (center h B j) (succ j) B
  let y := quotientData h B j
  let step := ofGaussian h B
  let inv := reciprocal step
  let v := factoredData h B j
  have hs := constant_regular (Γ := Γ) step
  have hc := constant_regular (Γ := Γ) inv
  have hp := GaussianGammaC7Name.name_regular _ _ _ (GaussianGammaLocalPoleGuards.center_source_disk h B j hi.andE₁ (step_disk h B hi))
  have hq := GaussianGammaPoleReciprocalFactor.original_quotient_regular h B j hi.andE₁ (step_disk h B hi)
  have hv : Γ ⊢[PRAAx] pointCN factoredF v := multiply_fast _ _ _ _ hs hq
  have fact := GaussianGammaPoleReciprocalFactor.original_P_linear_factor h B j hi.andE₁ (step_disk h B hi)
  have lift := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF P factoredF inv inv z v hc hc hp hv (cross_refl _ _ hc) fact
  have merge := GaussianGammaEulerShift.merge_head quotientF inv step y hq
  have replacement := GaussianGammaAdjacentCutoff.multiply_cross constantF GaussianNameRingLaws.oneF quotientF quotientF
    (qmul inv step) y y y (constant_regular _) (GaussianNameRingLaws.one_fast y) hq hq
    (constant_unit_cross (qmul inv step) y (actual_step_inverse h B hi)) (cross_refl _ _ hq)
  exact cross_trans _ _ _ _ _ _ lift (cross_trans _ _ _ _ _ _ merge
    (cross_trans _ _ _ _ _ _ replacement (GaussianNameRingLaws.multiply_one_left quotientF y hq)))
/-- Actual divided observation, original quotient observation and actual reciprocal step. -/
def output (p q h B j : PTm n) : PTm n := pairT (ap2 divisionF p (divisionData h B j))
  (pairT (ap2 quotientF q (quotientData h B j)) (reciprocal (ofGaussian h B)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (p q h B j : PTm n) : PTm n := PTm.app outputF ![p,q,h,B,j]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p q h B j : PTm n) :
    Syn.subst σ (output p q h B j) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ j) :=
  by simp [output,quotientData,GaussianGammaLocalPoleGuards.terminal]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p q h B j : PTm n) :
    Syn.subst σ (run p q h B j) = run (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem program_at (p q h B j : PTm n) : Γ ⊢[PRAAx] run p q h B j ≐ output p q h B j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![p,q,h,B,j]
theorem returned_division (p q h B j : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q h B j) ≐ ap2 divisionF p (divisionData h B j) := (congrFst (program_at p q h B j)).eqTrans (fst_pair _ _)
theorem returned_quotient (p q h B j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q h B j)) ≐ ap2 quotientF q (quotientData h B j) :=
  (congrFst ((congrSnd (program_at p q h B j)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_reciprocal (p q h B j : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q h B j)) ≐ reciprocal (ofGaussian h B) :=
  (congrSnd ((congrSnd (program_at p q h B j)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_distance (p q h B j : PTm n) (hi : Γ ⊢[PRAAx] input h B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (fstT (run p q h B j)) (fstT (sndT (run p q h B j)))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_division p q h B j).eqSymm (returned_quotient p q h B j).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_C23_literal_difference_quotient h B j hi))

theorem actual_original_punctured_step_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ qmul (reciprocal (ofGaussian (var 0) (var 1))) (ofGaussian (var 0) (var 1)) ≐ qone) :=
  closeUniv 2 (.impI (actual_step_inverse _ _ Prf.hyp0))
theorem actual_original_divided_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) ⟶ pointCN divisionF (divisionData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (division_regular _ _ _ Prf.hyp0))
theorem original_C23_actual_punctured_difference_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) ⟶ crossEquivalent divisionF quotientF (divisionData (var 0) (var 1) (var 2))
      (quotientData (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (original_C23_literal_difference_quotient _ _ _ Prf.hyp0))
theorem actual_original_pole_difference_quotient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_original_difference_quotient_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 2) (var 3) ⟶ GaussianRationalMetric.distanceBounded
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
      (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
      (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) := closeUniv 5 (.impI (returned_distance _ _ _ _ _ Prf.hyp0))


end LeanProofs.IPRA.Analysis.GaussianGammaPoleDifferenceQuotient
