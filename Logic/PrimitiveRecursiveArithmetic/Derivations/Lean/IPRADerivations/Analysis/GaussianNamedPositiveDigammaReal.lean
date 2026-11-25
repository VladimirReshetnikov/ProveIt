import IPRADerivations.Analysis.GaussianGammaPositiveNamedDigammaFrozen
import IPRADerivations.Analysis.GaussianGammaDigammaReal

/-!
# The real-axis name for the original positive digamma

At each precision the original digamma is close to an exactly real native
rational evaluation. Projecting the original name therefore preserves its
value, with literal canonical real observations at every clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveDigammaReal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain)
open GaussianGammaPositiveNamedDigammaFrozen (gain frozenData)
open GaussianGammaPositiveNamedRationalFreeze (clock threshold_le)
open GaussianGammaRealValues (axisF axis_regular axis_sample_at projection projection_distance)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedPositiveDigamma (source data derivativeF derivativeData)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "D" => GaussianNamedPositiveDigamma.nameF
local notation "N" => GaussianGammaDigammaNative.nameF
local notation "V" => GaussianGammaDigammaReal.nameF
local notation "vd" => GaussianGammaDigammaReal.data

abbrev nameF (f : PR 2) : PR 2 := axisF (D f)

theorem name_real (f : PR 2) (x A : PTm n) : Γ ⊢[PRAAx] realSamples (nameF f) (data f x A) :=
  GaussianEulerVerticalProjection.projected_real_samples (D f) (data f x A)

theorem name_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x A) :=
  axis_regular (D f) (data f x A) (GaussianNamedPositiveDigamma.name_regular f x A h)

private def cost (f : PR 2) (x A : PTm n) : PTm n :=
  (gain f x A+two)+(gain f x A+two)

@[simp] private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A : PTm n) :
    Syn.subst σ (cost f x A) = cost f (Syn.subst σ x) (Syn.subst σ A) := by
  simp [cost,two]

private theorem diagonal (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (D f) p (data f x A)) (ap2 (nameF f) p (data f x A))
      (cost f x A) (unit p) := by
  let k := clock f p one x A
  let a := numerator f k x
  let b := denominator f k x
  let u := data f x A
  let v := vd a b
  let z := ap2 (D f) p u
  let w := ap2 V p v
  let M := gain f x A
  have hp := unit_positive (Γ := Γ) p
  have hs := (frozen_rational_domain f k x A h (threshold_le f p one x A)).andE₁
  have native := GaussianGammaPositiveNamedDigammaFrozen.original_rate f p k x A h (le_refl k)
  have rawClose : Γ ⊢[PRAAx] independentRate (D f) V u v M (unit p) :=
    GaussianNamedRateTransport.transport (D f) N (D f) V u (frozenData f k x) u v M (unit p) hp native
      (cross_refl _ _ (GaussianNamedPositiveDigamma.name_regular f x A h))
      (cross_symm _ _ _ _ (GaussianGammaDigammaReal.original_cross a b hs))
  have near : Γ ⊢[PRAAx] distanceBounded z w (M+two) (unit p) :=
    distance_radius_mono z w _ _ _ _ (positive_product _ _ hp hp) hp
      (le_of_eq_add (d := zero) (by ipra_ring))
      (diagonal_rate (D f) V u v M (unit p) p hp rawClose)
  have hw := real_sample_at (Γ := Γ) V v p (GaussianGammaDigammaReal.name_real a b)
  have axis : Γ ⊢[PRAAx] projection w ≐ w := RationalGaussianEmbedding.canonical_axis_roundtrip w hw.andE₁ hw.andE₂
  have projected := distance_congr (.eqRefl _) axis (.eqRefl _) (.eqRefl _)
    (projection_distance z w (M+two) (unit p) hp near)
  exact distance_congr (.eqRefl _) (axis_sample_at (D f) p u).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp near (distance_symmetric _ _ _ _ hp projected))

theorem original_cross (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (D f) (nameF f) (data f x A) (data f x A) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianNamedGammaPositiveLower.subst_source,Syn.shift] using h.shift
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost f x A)
    (GaussianNamedPositiveDigamma.name_regular f x A h) (name_regular f x A h) (.allI ?_)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_cost,GaussianNamedPositiveDigamma.subst_data] using
    diagonal f (var 0) (Syn.shift x) (Syn.shift A) hs

theorem derivative_zero_equivalent (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] Fm.iff (crossEquivalent (nameF f) zeroF (data f x A) zero)
      (crossEquivalent (derivativeF f) zeroF (derivativeData x A) zero) := by
  have e := original_cross f x A h
  refine .iffI (.impI ?_) (.impI ?_)
  · exact GaussianNamedPositiveDigamma.derivative_zero_of_digamma_zero f x A h.wk
      (cross_trans _ _ _ _ _ _ e.wk Prf.hyp0)
  · exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e.wk)
      (GaussianNamedPositiveDigamma.digamma_zero_of_derivative_zero f x A h.wk Prf.hyp0)

theorem actual_original_positive_named_digamma_real_axis_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ (realSamples (nameF f) (data f (var 0) (var 1)) ⋏
        crossEquivalent (D f) (nameF f) (data f (var 0) (var 1)) (data f (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.andI (name_real f _ _) (original_cross f _ _ Prf.hyp0)))

theorem actual_original_positive_named_digamma_real_zero_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ Fm.iff (crossEquivalent (nameF f) zeroF (data f (var 0) (var 1)) zero)
        (crossEquivalent (derivativeF f) zeroF (derivativeData (var 0) (var 1)) zero)) :=
  closeUniv 2 (.impI (derivative_zero_equivalent f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveDigammaReal
