import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerNamedLowerTail
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerVaryingCutoffName

/-!
# Source-only actual varying-cutoff Euler name

The original lower and upper tail suppliers discharge every tail premise
of the checked varying-cutoff construction. Only original numerical disk,
positive denominator and positive real-part guards remain. The output is
the SAME actual PR2 name and SAME original eta/top observations at p+4,
with actual Euler evaluation precision p+top(p)+10. The checked conservative
compact modulus is retained. Identification with the original Gamma name
and the paper's sharper mesh remain separate conclusions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerImproperName

open_ipra
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerVaryingCutoffName (cells evaluationPrecision)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏ GaussianEulerLowerPowerCoefficients.source z R B A
def data (z R B A : PTm n) : PTm n := GaussianEulerVaryingCutoffName.data z R B A
def nameF : PR 2 := GaussianEulerVaryingCutoffName.nameF
def output (p z R B A : PTm n) : PTm n := GaussianEulerVaryingCutoffName.output p z R B A
def outputF : PR 5 := GaussianEulerVaryingCutoffName.outputF
def run (p z R B A : PTm n) : PTm n := PTm.app outputF ![p,z,R,B,A]
ipra_subst source
ipra_subst data
ipra_subst output

/-- The actual checked lowerData theorem discharges the sole former
tail predicate; no lower-tail or Cauchy premise is left in source. -/
theorem cauchy_input (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianEulerCutoffCauchyComparison.input z R B A :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (GaussianEulerNamedLowerTail.lower_tail_all z R B A h))

theorem name_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A) :=
  GaussianEulerVaryingCutoffName.conditional_name_regular z R B A (cauchy_input z R B A h)

theorem observations (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (ap2 nameF q (data z R B A))
      (unit p+unit q) (unit p*unit q) :=
  GaussianEulerVaryingCutoffName.name_observations p q z R B A (cauchy_input z R B A h)

theorem original_observation (p z R B A : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A) ≐ ap2 GaussianGammaEulerCompactQuadrature.nameF (p+num 4)
      (GaussianGammaEulerCompactQuadrature.data z R B p A) :=
  GaussianEulerVaryingCutoffName.name_at p z R B A

theorem actual_sampler (p z R B A : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (evaluationPrecision p A R) (cells p A R) one (width p A R) (etaDen p A R) (fixedData z B) :=
  GaussianEulerVaryingCutoffName.actual_sampler p z R B A

theorem name_canonical (p z R B A : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p (data z R B A)) :=
  GaussianEulerVaryingCutoffName.name_canonical p z R B A

theorem program_at (p z R B A : PTm n) : Γ ⊢[PRAAx] run p z R B A ≐ output p z R B A :=
  GaussianEulerVaryingCutoffName.program_at p z R B A
theorem returned_point (p z R B A : PTm n) : Γ ⊢[PRAAx] fstT (run p z R B A) ≐ ap2 nameF p (data z R B A) :=
  GaussianEulerVaryingCutoffName.returned_point p z R B A
theorem returned_clock (p z R B A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z R B A)) ≐ p+num 4 :=
  GaussianEulerVaryingCutoffName.returned_clock p z R B A
theorem returned_cells (p z R B A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p z R B A))) ≐ cells p A R :=
  GaussianEulerVaryingCutoffName.returned_cells p z R B A
theorem returned_evaluation_precision (p z R B A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p z R B A))) ≐ p+top p A R+num 10 :=
  GaussianEulerVaryingCutoffName.returned_evaluation_precision p z R B A

theorem source_only_actual_Euler_improper_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))
theorem source_only_actual_Euler_improper_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶ distanceBounded
      (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5))) (ap2 nameF (var 1) (data (var 2) (var 3) (var 4) (var 5)))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (observations _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_Euler_improper_observation_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) ≐
      ap2 GaussianGammaEulerCompactQuadrature.nameF (var 0+num 4)
        (GaussianGammaEulerCompactQuadrature.data (var 1) (var 2) (var 3) (var 0) (var 4))) :=
  closeUniv 5 (original_observation _ _ _ _ _)
theorem actual_original_Euler_improper_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4)) ≐
      GaussianCompactRiemannName.quadrature evaluatorF (evaluationPrecision (var 0) (var 4) (var 2)) (cells (var 0) (var 4) (var 2))
        one (width (var 0) (var 4) (var 2)) (etaDen (var 0) (var 4) (var 2)) (fixedData (var 1) (var 3))) :=
  closeUniv 5 (actual_sampler _ _ _ _ _)
theorem actual_original_Euler_improper_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_original_Euler_improper_precision_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ var 0+top (var 0) (var 4) (var 2)+num 10) :=
  closeUniv 5 (returned_evaluation_precision _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerImproperName
