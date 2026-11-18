import IPRADerivations.Analysis.GaussianRootMembership
import IPRADerivations.Analysis.GaussianPolynomialValueName
import IPRADerivations.Analysis.GaussianRepresentedPointBounds

/-!
# Represented root-support membership is equivalent to polynomial vanishing

Source04, prop:root-adequacy, the two membership implications and the
primitive-recursive forward stage. Inputs use the supplied integer Z and
the original represented disk bound. The actual sample disk U=Z+1 is
derived. Polynomial vanishing concerns the actual fast Gaussian value
name, whose evaluations and coherence are independently proved.

The source's additional sharp C_Z/M_Z evaluation and distance estimates
remain separate obligations; this module does not claim those estimates.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootAdequacy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (R CN)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRepresentedPointBounds (normLE)
open LeanProofs.IPRA.Analysis.GaussianRootMembership (member stageCondition)
open LeanProofs.IPRA.Analysis.GaussianPolynomialValueName (valueZero nameZero nameF nameData)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inputContract (step a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n :=
  monicRD step ⋏ (CN a N x ⋏ (le one N ⋏ (le (R a N x) Z ⋏ (pointCN point x ⋏ normLE point Z x))))
@[simp] theorem subst_inputContract {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (point : PR 2) (N Z x : PTm n) :
    (inputContract step a point N Z x).subst σ = inputContract step a point (Syn.subst σ N) (Syn.subst σ Z) (Syn.subst σ x) := by
  simp [inputContract]

theorem source_sample_contract (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianRootMembership.inputContract step a point N (Z+one) x := by
  have rd := Prf.andE₁ h
  have cn := Prf.andE₁ (Prf.andE₂ h)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have rz := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have data := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact .andI rd (.andI cn (.andI hn (.andI (le_trans rz (le_add_right Z one))
    (.andI (Prf.andE₁ data) (GaussianRepresentedPointBounds.uniform_sample_bound point Z x (Prf.andE₂ data))))))

/-- The actual normalized evaluator is a genuine fast Gaussian name for
P(z), with N,Z and all persistent data retained as numerical inputs. -/
theorem polynomial_value_name (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    pointCN (nameF a point) (nameData N (Z+one) x) := by
  have h' := source_sample_contract step a point N Z x h
  have cn := Prf.andE₁ (Prf.andE₂ h')
  have ru := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h')))
  have data := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h')))
  exact GaussianPolynomialValueName.name_fast _ _ _ _ _ cn (Prf.andE₁ data) (Prf.andE₂ data)
    (le_trans (GaussianRootSupport.radius_positive a N x) ru)

theorem normalized_root_iff_value_zero (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    Fm.iff (GaussianRootApproximationWitness.normalizedZero a point N (Z+one) x) (valueZero a point N (Z+one) x) := by
  have h' := source_sample_contract step a point N Z x h
  have cn := Prf.andE₁ (Prf.andE₂ h')
  have ru := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h')))
  have data := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h')))
  exact GaussianPolynomialValueName.zero_iff _ _ _ _ _ cn (Prf.andE₁ data) (Prf.andE₂ data)
    (le_trans (GaussianRootSupport.radius_positive a N x) ru)

/-- Both original quantified represented-membership directions. -/
theorem member_iff_polynomial_zero (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    Fm.iff (member step a point N x) (valueZero a point N (Z+one) x) :=
  (GaussianRootMembership.membership_iff_zero step a point N (Z+one) x (source_sample_contract _ _ _ _ _ _ h)).iffTrans
    (normalized_root_iff_value_zero step a point N Z x h)

/-- The zero predicate here literally queries the returned PR2 name. -/
theorem member_iff_computed_polynomial_zero (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    Fm.iff (member step a point N x) (nameZero a point N (Z+one) x) :=
  (member_iff_polynomial_zero step a point N Z x h).iffTrans
    (.iffI (.impI (GaussianPolynomialValueName.value_zero_to_name_zero _ _ _ _ _ Prf.hyp0))
      (.impI (GaussianPolynomialValueName.name_zero_to_value_zero _ _ _ _ _ Prf.hyp0)))

theorem primitive_root_stage (step a : PR 3) (point : PR 2) (N Z x k : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x)
    (hZero : Γ ⊢[PRAAx] valueZero a point N (Z+one) x) : Γ ⊢[PRAAx]
    stageCondition step a point N x k (GaussianRootApproximationWitness.stageIndex N (Z+one) k) :=
  GaussianRootMembership.root_to_stage step a point N (Z+one) x k (source_sample_contract _ _ _ _ _ _ h)
    ((normalized_root_iff_value_zero step a point N Z x h).iffMpr hZero)

theorem represented_root_membership_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract step a point (var 0) (var 1) (var 2) ⟶
      Fm.iff (member step a point (var 0) (var 2)) (nameZero a point (var 0) (var 1+one) (var 2))) :=
  closeUniv 3 (.impI (member_iff_computed_polynomial_zero _ _ _ _ _ _ Prf.hyp0))

theorem represented_polynomial_value_name_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract step a point (var 0) (var 1) (var 2) ⟶
      pointCN (nameF a point) (nameData (var 0) (var 1+one) (var 2))) :=
  closeUniv 3 (.impI (polynomial_value_name _ _ _ _ _ _ Prf.hyp0))

theorem primitive_represented_root_stage_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract step a point (var 0) (var 1) (var 2) ⟶ nameZero a point (var 0) (var 1+one) (var 2) ⟶
      stageCondition step a point (var 0) (var 2) (var 3) (GaussianRootApproximationWitness.stageIndex (var 0) (var 1+one) (var 3))) :=
  closeUniv 4 (.impI (.impI (primitive_root_stage _ _ _ _ _ _ _ Prf.hyp1
    (GaussianPolynomialValueName.name_zero_to_value_zero _ _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRootAdequacy
