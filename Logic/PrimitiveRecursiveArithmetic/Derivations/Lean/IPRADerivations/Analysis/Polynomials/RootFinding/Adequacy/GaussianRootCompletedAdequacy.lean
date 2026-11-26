import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootAdequacyTheorem
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.Distances.GaussianRootDistanceZero

/-!
# Root adequacy and zero of the actual completed Euclidean distance

The original root-adequacy input contract implies both the full named
source proposition and its subsequent zero-distance interpretation. The
completed distance and polynomial values are the literal packed PR2
programs already constructed, with all degree, disk and name data internal.
The local monic descent contract remains explicit.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootCompletedAdequacy

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRootAdequacy (inputContract)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem completion_input (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianRootDistanceCompletion.input step a point N x :=
  .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h))
    (.andI (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
      (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))))

theorem completed_zero_iff_polynomial_zero (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    Fm.iff (GaussianRootDistanceZero.completedZero step a point N x)
      (GaussianPolynomialValueName.nameZero a point N (Z+one) x) := by
  have distance := GaussianRootDistanceZero.member_iff_completed_zero step a point N x
    (completion_input step a point N Z x h)
  have polynomial := GaussianRootAdequacy.member_iff_computed_polynomial_zero step a point N Z x h
  exact .iffI (.impI (polynomial.wk.iffMp (distance.wk.iffMpr Prf.hyp0)))
    (.impI (distance.wk.iffMp (polynomial.wk.iffMpr Prf.hyp0)))

def distanceNonnegative (step a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n :=
  .all (RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
    (ap2 (GaussianRootDistanceCompletion.nameF step a point) (var 0)
      (GaussianRootDistanceCompletion.nameData (Syn.shift N) (Syn.shift x))))

ipra_subst distanceNonnegative [Syn.subst_shift, Syn.shift_subst]

theorem completed_distance_nonnegative (step a : PR 3) (point : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] distanceNonnegative step a point N x :=
  .allI (GaussianRootDistanceCompletion.name_nonnegative step a point (Syn.shift N) (Syn.shift x) (var 0))

def completionConclusion (step a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n :=
  GaussianLinearDistanceName.scalarCN (GaussianRootDistanceCompletion.nameF step a point)
    (GaussianRootDistanceCompletion.nameData N x) ⋏
  (distanceNonnegative step a point N x ⋏
    Fm.iff (GaussianRootDistanceZero.completedZero step a point N x)
      (GaussianPolynomialValueName.nameZero a point N (Z+one) x))

ipra_subst completionConclusion [Fm.iff]

def conclusion (step a : PR 3) (point : PR 2) (N Z x : PTm n) : Fm PTm n :=
  GaussianRootAdequacyTheorem.conclusion step a point N Z x ⋏ completionConclusion step a point N Z x

ipra_subst conclusion

theorem completed_root_adequacy (step a : PR 3) (point : PR 2) (N Z x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx] conclusion step a point N Z x :=
  .andI (GaussianRootAdequacyTheorem.root_adequacy step a point N Z x h)
    (.andI (GaussianRootDistanceCompletion.name_fast step a point N x (completion_input step a point N Z x h))
      (.andI (completed_distance_nonnegative step a point N x)
        (completed_zero_iff_polynomial_zero step a point N Z x h)))

theorem completed_root_adequacy_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract step a point (var 0) (var 1) (var 2) ⟶ conclusion step a point (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (completed_root_adequacy _ _ _ _ _ _ Prf.hyp0))

theorem completed_distance_root_equation_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract step a point (var 0) (var 1) (var 2) ⟶
      Fm.iff (GaussianRootDistanceZero.completedZero step a point (var 0) (var 2))
        (GaussianPolynomialValueName.nameZero a point (var 0) (var 1+one) (var 2))) :=
  closeUniv 3 (.impI (completed_zero_iff_polynomial_zero _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRootCompletedAdequacy
