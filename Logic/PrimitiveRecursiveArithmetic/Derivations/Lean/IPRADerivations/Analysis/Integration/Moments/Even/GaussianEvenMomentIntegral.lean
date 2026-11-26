import IPRADerivations.Analysis.Integration.Moments.Even.GaussianEvenMomentIntegrand

/-!
# Actual positive-half-line Gaussian even moments

For every internal N and positive rational damping c/d, the SAME
original quadratic improper kernel at N+1/2 is regular and equals
Gamma(N+1/2)/(2*(c/d)^(N+1/2)), using the actual inverse-factor program.
Its literal original cofinal quadrature is retained. The companion row
module identifies those kernels with u^(2N) exp(-(c/d)u²). Evaluation of
Gamma(1/2) as sqrt(pi) and whole-line reflection are separate claims.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEvenMomentIntegral

open_ipra
open GaussianGammaHalfIntegerDomain (argument radius)
open GaussianGammaIntegralCutoffs (etaDen)
open GaussianEulerQuadraticCutoffGeometry (width)
open GaussianEulerQuadraticUpperEndpoint (preimage)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev nameF : PR 2 := GaussianEulerQuadraticImproperKernel.nameF
abbrev valueF : PR 2 := GaussianEulerQuadraticGamma.productF
def data (N c d : PTm n) : PTm n := GaussianEulerQuadraticImproperKernel.data (argument N) (radius N) two two c d
def valueData (N c d : PTm n) : PTm n := GaussianEulerQuadraticGamma.productData (argument N) (radius N) two two c d
def cutoff (p N c d : PTm n) : PTm n := GaussianEulerQuadraticImproperSchedule.index p two
  (GaussianEulerQuadraticImproperKernel.invBound (argument N) two c d) c d
ipra_subst data
ipra_subst valueData
ipra_subst cutoff [GaussianEulerQuadraticImproperKernel.invBound]

theorem name_regular (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    pointCN nameF (data N c d) := GaussianEulerQuadraticImproperKernel.name_regular _ _ _ _ _ _
      (GaussianGammaHalfIntegerDomain.quadratic_source N c d hc hd)

theorem original_even_moment (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent nameF valueF (data N c d) (valueData N c d) :=
  GaussianEulerQuadraticGamma.original_kernel_is_inverse_factor_Gamma _ _ _ _ _ _
    (GaussianGammaHalfIntegerDomain.quadratic_source N c d hc hd)

theorem original_observations (p q N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data N c d)) (ap2 valueF q (valueData N c d))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_even_moment N c d hc hd)

theorem actual_quadrature (p N c d : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data N c d) ≐ GaussianCompactRiemannName.quadrature GaussianEulerQuadraticKernelCompactName.evaluatorF
      (GaussianCompactRiemannName.precision (succ p) (preimage (cutoff p N c d) two (radius N) d))
      (GaussianCompactRiemannName.mesh (succ p)
        (GaussianEulerQuadraticKernelCompactName.lipschitz (radius N) (etaDen (cutoff p N c d) two (radius N))
          (preimage (cutoff p N c d) two (radius N) d) c d) (preimage (cutoff p N c d) two (radius N) d))
      one (width (cutoff p N c d) two (radius N) d) (etaDen (cutoff p N c d) two (radius N))
      (GaussianEulerPositiveScalingIntegrand.fixedData (argument N) two c d) :=
  (GaussianEulerQuadraticImproperKernel.name_at p (argument N) (radius N) two two c d).eqTrans
    (GaussianEulerQuadraticKernelCompactName.name_at (succ p) (argument N) (radius N) two c d one
      (width (cutoff p N c d) two (radius N) d) (etaDen (cutoff p N c d) two (radius N))
      (preimage (cutoff p N c d) two (radius N) d))

theorem actual_original_positive_half_line_Gaussian_even_moment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent nameF valueF
      (data (var 0) (var 1) (var 2)) (valueData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (original_even_moment _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_positive_half_line_Gaussian_even_moment_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (name_regular _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEvenMomentIntegral
