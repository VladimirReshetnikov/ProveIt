import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicResidualRadius

/-!
# The exact monic residual radius from original Euclidean coefficient bounds

Every coefficient comparison is an original rational squared-norm comparison
with A². The actual reciprocal-Horner tail has budget A G_k/R^k for R=A+2,
proved by quantifier-free induction, without converting to L1 or enlarging A.
The original residual bound then contradicts the strict geometric gap at an
outside point. All degrees, codes, coefficients and indices remain internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanResidualRadius

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
  (qone normLower)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianMonicResidualRadius
  (euclideanCoefficientBounds subst_euclideanCoefficientBounds euclidean_coefficient_at
    euclidean_tail_bound_step euclidean_tail_bound euclidean_outside_impossible euclidean_residual_radius)
open LeanProofs.IPRA.Analysis.GaussianRadiusBudget (radius geometric)
open LeanProofs.IPRA.Analysis.GaussianReciprocalHorner (tail)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Every stored original coefficient has its actual Euclidean norm at
most A. The two scalar component denominators remain independently decoded. -/
def coefficientBounds (C A : PTm n) : Fm PTm n :=
  euclideanCoefficientBounds C A

@[simp] theorem subst_coefficientBounds {m : ℕ} (σ : Fin n → PTm m) (C A : PTm n) :
    (coefficientBounds C A).subst σ = coefficientBounds (Syn.subst σ C) (Syn.subst σ A) :=
  subst_euclideanCoefficientBounds σ C A

alias coefficient_at := euclidean_coefficient_at
alias tail_bound_step := euclidean_tail_bound_step
alias tail_bound := euclidean_tail_bound
alias outside_impossible := euclidean_outside_impossible
alias residual_radius := euclidean_residual_radius

theorem euclidean_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (var 0) ≐ succ (var 2)) ⟶ coefficientBounds (var 0) (var 3) ⟶
      bounded (var 1) one (radius (var 3)) ⟶
        bounded (tail (var 0) (var 1) (var 2) (var 4))
          (var 3*geometric (var 3) (var 4)) (pw (radius (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (tail_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem euclidean_outside_impossible_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ (length (var 0) ≐ succ (var 2)) ⟶
      (entry (var 0) zero ≐ qone) ⟶ coefficientBounds (var 0) (var 3) ⟶
        bounded (evaluate (var 0) (var 1)) one one ⟶ normLower (var 1) (radius (var 3)) ⟶ .bot) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (outside_impossible _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))))

theorem euclidean_residual_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ (length (var 0) ≐ succ (var 2)) ⟶
      (entry (var 0) zero ≐ qone) ⟶ coefficientBounds (var 0) (var 3) ⟶
        bounded (evaluate (var 0) (var 1)) one one ⟶ bounded (var 1) (var 3+two) one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI
    (residual_radius _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianEuclideanResidualRadius
