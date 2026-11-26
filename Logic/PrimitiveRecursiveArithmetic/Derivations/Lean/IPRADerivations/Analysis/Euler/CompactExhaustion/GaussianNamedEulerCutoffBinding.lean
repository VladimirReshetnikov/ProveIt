import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianNamedEulerQuadrature
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianNamedEulerCompactModulus

/-!
# Fixed compact observations at the actual named Euler cutoffs

Every observation of the varying-cutoff integral is exactly a specified
observation of the corresponding regular fixed compact quadrature.
The original cutoff, mesh, row clock and named integrand are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerCutoffBinding

open_ipra
open GaussianNamedRightHalfPlane (radius)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianEulerCutoffCauchyComparison (clock)
open GaussianNamedEulerQuadrature (original retimed)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def compactData (f : PR 2) (p x A : PTm n) : PTm n :=
  GaussianNamedEulerCompactModulus.data f x (etaDen p (two*A) (radius f x))
    (top p (two*A) (radius f x)) (width p (two*A) (radius f x))

theorem compact_regular (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (GaussianNamedEulerCompactModulus.nameF f) (compactData f p x A) := by
  let R := radius f x
  let m := two*A
  have endBound : Γ ⊢[PRAAx] le (one+width p m R) (etaDen p m R*top p m R) :=
    le_congr (exact_right_endpoint p m R).eqSymm (.eqRefl _) (le_refl _)
  exact GaussianNamedEulerCompactModulus.name_regular f x _ _ _
    (.andI h (.andI (eta_den_positive p m R) endBound))

theorem original_named_cutoff_sample (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] original f p x A ≐
      ap2 (GaussianNamedEulerCompactModulus.nameF f) (clock p) (compactData f p x A) := by
  let R := radius f x
  let m := two*A
  let E := etaDen p m R
  let T := top p m R
  let C := width p m R
  let L := GaussianNamedEulerCompactTimeRate.gain f x E T
  let F := GaussianNamedEulerIntegrand.evaluatorF f
  let M := GaussianCompactRiemannName.mesh (clock p) L T
  have compare : Γ ⊢[PRAAx] GaussianEulerVaryingCutoffName.evaluationPrecision p m R ≐
      GaussianCompactRiemannName.precision (clock p) T := by
    unfold GaussianEulerVaryingCutoffName.evaluationPrecision GaussianCompactRiemannName.precision clock T
    ipra_ring
  have sample := GaussianCompactRiemannName.name_at (Γ := Γ) F (clock p) one C E L T x
  exact (GaussianEulerVaryingCutoffName.quadrature_precision_congr F _ _ M one C E x compare).eqTrans sample.eqSymm

theorem original_improper_at_named_cutoff (f : PR 2) (p q x A : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianNamedEulerQuadrature.nameF f) p (GaussianNamedGamma.data x A))
      (ap2 (GaussianNamedEulerCompactModulus.nameF f) q (compactData f (retimed p) x A))
      (unit (clock (retimed p))+unit q) (unit (clock (retimed p))*unit q) := by
  have eq := (GaussianNamedEulerQuadrature.name_at (Γ := Γ) f p x A).eqTrans
    (original_named_cutoff_sample f (retimed p) x A)
  exact GaussianRationalDistanceOrder.distance_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.point_at _ _ (clock (retimed p)) q (compact_regular f (retimed p) x A h))

theorem literal_named_Euler_cutoff_compact_sample_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (original f (var 0) (var 1) (var 2) ≐ ap2 (GaussianNamedEulerCompactModulus.nameF f)
        (clock (var 0)) (compactData f (var 0) (var 1) (var 2))) :=
  closeUniv 3 (original_named_cutoff_sample f _ _ _)

theorem original_improper_and_named_cutoff_compact_observations_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (pointCN f (var 2) ⟶ distanceBounded
        (ap2 (GaussianNamedEulerQuadrature.nameF f) (var 0) (GaussianNamedGamma.data (var 2) (var 3)))
        (ap2 (GaussianNamedEulerCompactModulus.nameF f) (var 1) (compactData f (retimed (var 0)) (var 2) (var 3)))
        (unit (clock (retimed (var 0)))+unit (var 1)) (unit (clock (retimed (var 0)))*unit (var 1))) :=
  closeUniv 4 (.impI (original_improper_at_named_cutoff f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerCutoffBinding
