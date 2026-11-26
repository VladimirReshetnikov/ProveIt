import IPRADerivations.Analysis.Polynomials.GaussianRationalSyntheticDivision

/-!
# Actual Gaussian ring step for rational polynomial translation

The original raw Gaussian inputs need not be canonical. Their three actual
positive decoded denominators produce a common denominator. Canonical
multiplication outputs then identify the cancellation of the shifted query
inside a product. No false equality between a normalized difference and an
arbitrary raw input code is used. The actual synthetic-division expression
therefore equals the ordinary translated Horner step at every internal input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalTranslationAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qadd qmul represents positive_product qadd_represents qmul_represents represents_congr canonical_unique)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qsub_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr rescale_to)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- True common-denominator input representations prove the literal
canonical product identity. No output identity or canonical input is assumed. -/
theorem cancel_shift_product_from_representations (z w u Z W U E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hz : Γ ⊢[PRAAx] represents z Z E)
    (hw : Γ ⊢[PRAAx] represents w W E) (hu : Γ ⊢[PRAAx] represents u U E) : Γ ⊢[PRAAx]
    qmul (qsub (qadd z w) z) u ≐ qmul u w := by
  have e2 := positive_product (Γ := Γ) E E hE hE
  have sum := qadd_represents z w Z W E hE hz hw
  have difference := qsub_represents _ _ _ _ _ hE sum hz
  have left := qmul_represents _ _ _ _ _ _ hE hE difference hu
  have right := qmul_represents u w U W E E hE hE hu hw
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.qmul_canonical _ _) e2 (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_mul,im_mul,re_sub,im_sub,re_add,im_add] <;> ring

def commonDenominator (z w u : PTm n) : PTm n := rawDen z*rawDen w*rawDen u
@[simp] theorem subst_commonDenominator {m : ℕ} (σ : Fin n → PTm m) (z w u : PTm n) :
    Syn.subst σ (commonDenominator z w u) = commonDenominator (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ u) := by
  simp [commonDenominator]

theorem common_denominator_positive (z w u : PTm n) : Γ ⊢[PRAAx] le one (commonDenominator z w u) :=
  positive_product _ _ (positive_product _ _ (raw_den_positive z) (raw_den_positive w)) (raw_den_positive u)

/-- Every representation in the local algebra proof is derived from the
actual three original input codes and their own decoded denominators. -/
theorem cancel_shift_product (z w u : PTm n) : Γ ⊢[PRAAx]
    qmul (qsub (qadd z w) z) u ≐ qmul u w := by
  let E := commonDenominator z w u
  have hz := rescale_to z (rawGaussian z) (rawDen z) (rawDen w*rawDen u) E (raw_represents (Γ := Γ) z)
    (by unfold E commonDenominator; ipra_ring)
  have hw := rescale_to w (rawGaussian w) (rawDen w) (rawDen z*rawDen u) E (raw_represents (Γ := Γ) w)
    (by unfold E commonDenominator; ipra_ring)
  have hu := rescale_to u (rawGaussian u) (rawDen u) (rawDen z*rawDen w) E (raw_represents (Γ := Γ) u)
    (by unfold E commonDenominator; ipra_ring)
  exact cancel_shift_product_from_representations z w u _ _ _ E (common_denominator_positive z w u) hz hw hu

/-- Exact orientation of the existing synthetic-division evaluation rule
at y=z+w. The arbitrary original fourth input is normalized by qadd itself. -/
theorem shifted_division_step (z w u v : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (qsub (qadd z w) z) u) v ≐ qadd (qmul u w) v :=
  qadd_congr (cancel_shift_product z w u) (.eqRefl _)

/-! The two literal PR4 programs are the synthetic-division side and the
translated Horner side. Their equality has no numerical input guards. -/
def divisionStep (z w u v : PTm n) : PTm n := qadd (qmul (qsub (qadd z w) z) u) v
def hornerStep (_z w u v : PTm n) : PTm n := qadd (qmul u w) v
def divisionStepF : PR 4 := PTm.toPR (divisionStep (var 0) (var 1) (var 2) (var 3))
def hornerStepF : PR 4 := PTm.toPR (hornerStep (var 0) (var 1) (var 2) (var 3))

@[simp] theorem subst_divisionStep {m : ℕ} (σ : Fin n → PTm m) (z w u v : PTm n) :
    Syn.subst σ (divisionStep z w u v) = divisionStep (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ u) (Syn.subst σ v) := by
  simp [divisionStep]
@[simp] theorem subst_hornerStep {m : ℕ} (σ : Fin n → PTm m) (z w u v : PTm n) :
    Syn.subst σ (hornerStep z w u v) = hornerStep (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ u) (Syn.subst σ v) := by
  simp [hornerStep]

theorem division_program (z w u v : PTm n) : Γ ⊢[PRAAx]
    PTm.app divisionStepF ![z,w,u,v] ≐ divisionStep z w u v := by
  simpa [divisionStepF] using toPR_eq (Γ := Γ) (divisionStep (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,w,u,v]
theorem horner_program (z w u v : PTm n) : Γ ⊢[PRAAx]
    PTm.app hornerStepF ![z,w,u,v] ≐ hornerStep z w u v := by
  simpa [hornerStepF] using toPR_eq (Γ := Γ) (hornerStep (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,w,u,v]

theorem actual_programs_equal (z w u v : PTm n) : Γ ⊢[PRAAx]
    PTm.app divisionStepF ![z,w,u,v] ≐ PTm.app hornerStepF ![z,w,u,v] :=
  (division_program z w u v).eqTrans ((shifted_division_step z w u v).eqTrans (horner_program z w u v).eqSymm)

theorem shifted_query_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qmul (qsub (qadd (var 0) (var 1)) (var 0)) (var 2) ≐ qmul (var 2) (var 1)) :=
  closeUniv 3 (cancel_shift_product _ _ _)

theorem translated_synthetic_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (qadd (qmul (qsub (qadd (var 0) (var 1)) (var 0)) (var 2)) (var 3) ≐
      qadd (qmul (var 2) (var 1)) (var 3)) := closeUniv 4 (shifted_division_step _ _ _ _)

theorem translation_step_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((PTm.app divisionStepF ![var 0,var 1,var 2,var 3] ≐ divisionStep (var 0) (var 1) (var 2) (var 3)) ⋏
      ((PTm.app hornerStepF ![var 0,var 1,var 2,var 3] ≐ hornerStep (var 0) (var 1) (var 2) (var 3)) ⋏
        (PTm.app divisionStepF ![var 0,var 1,var 2,var 3] ≐ PTm.app hornerStepF ![var 0,var 1,var 2,var 3]))) :=
  closeUniv 4 (.andI (division_program _ _ _ _) (.andI (horner_program _ _ _ _) (actual_programs_equal _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalTranslationAlgebra
