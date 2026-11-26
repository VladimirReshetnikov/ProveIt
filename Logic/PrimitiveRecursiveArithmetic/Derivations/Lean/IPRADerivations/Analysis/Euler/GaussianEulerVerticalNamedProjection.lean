import IPRADerivations.Analysis.Euler.GaussianEulerVerticalProjection
import IPRADerivations.Analysis.Euler.GaussianEulerVerticalNativeProjection

/-!
# Exact native observations of the named real projection

The two independently decoded projected fractions are canonically equal,
even when the original complex input observation is raw. At every late
margin query, the decoded real projection keeps the ORIGINAL disk U(f,x)
and the original transferred margin 1/(2A).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedProjection

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaRealValues (axisF projection projection_represents)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianNamedRightHalfPlane (source radius numerator denominator threshold actual_late_source)
open GaussianRationalHorner (ofGaussian canonical_unique)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem projection_recode (q : PTm n) : Γ ⊢[PRAAx]
    projection (GaussianFastValueCut.recode q) ≐ projection q :=
  canonical_unique _ _ (RationalGaussianEmbedding.native (ComplexLogarithmRemainder.re (rawGaussian q))) (rawDen q)
    (RationalGaussianEmbedding.embed_canonical _) (RationalGaussianEmbedding.embed_canonical _) (raw_den_positive q)
    (projection_represents _ _ _ (GaussianFastValueCut.recode_represents q)) (projection_represents _ _ _ (raw_represents q))

theorem decoded_projection (f : PR 2) (r x : PTm n) : Γ ⊢[PRAAx]
    ofGaussian (numerator (axisF f) r x) (denominator (axisF f) r x) ≐
      ofGaussian (argument (numerator f r x)) (denominator f r x) :=
  (GaussianExponentialReference.recode_fixed _ (GaussianEulerVerticalProjection.projected_real_at f r x).andE₁).eqTrans
    ((GaussianGammaRealValues.axis_sample_at f r x).eqTrans ((projection_recode (ap2 f r x)).eqSymm.eqTrans
      (GaussianEulerVerticalNativeProjection.original_fraction_projection _ _ (raw_den_positive (ap2 f r x))).eqSymm))

theorem projected_late_source (f : PR 2) (r x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hr : Γ ⊢[PRAAx] le (threshold A) r) : Γ ⊢[PRAAx]
    GaussianEulerLowerPowerCoefficients.source (numerator (axisF f) r x) (radius f x) (denominator (axisF f) r x) (two*A) := by
  have projected := GaussianEulerVerticalProjection.projected_source f x A h
  have original := actual_late_source (axisF f) x A r projected hr
  have disk := GaussianEulerVerticalProjection.original_disk_at f r x h.andE₁
  have clear := GaussianRationalMetric.bounded_to_cleared _ _ _ _ _ (raw_den_positive (ap2 (axisF f) r x)) (le_refl one)
    (raw_represents _) disk
  have native : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (numerator (axisF f) r x)
      (radius f x*denominator (axisF f) r x) :=
    le_congr (by dsimp only [numerator]; ipra_ring) (by dsimp only [radius,denominator]; ipra_ring) clear
  exact .andI original.andE₁ (.andI (.andI original.andE₂.andE₁.andE₁ native) original.andE₂.andE₂)

theorem actual_named_vertical_projected_fraction_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ofGaussian (numerator (axisF f) (var 0) (var 1)) (denominator (axisF f) (var 0) (var 1)) ≐
      ofGaussian (argument (numerator f (var 0) (var 1))) (denominator f (var 0) (var 1))) :=
  closeUniv 2 (decoded_projection f _ _)
theorem actual_named_vertical_projection_original_disk_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source f (var 1) (var 2) ⋏ le (threshold (var 2)) (var 0)) ⟶
      GaussianEulerLowerPowerCoefficients.source (numerator (axisF f) (var 0) (var 1)) (radius f (var 1))
        (denominator (axisF f) (var 0) (var 1)) (two*var 2)) :=
  closeUniv 3 (.impI (projected_late_source f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNamedProjection
