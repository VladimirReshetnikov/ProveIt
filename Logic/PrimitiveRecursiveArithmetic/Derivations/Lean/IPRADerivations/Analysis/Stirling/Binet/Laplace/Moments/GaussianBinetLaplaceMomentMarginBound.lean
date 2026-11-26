import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentMarginTail
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentImproperBound

/-!
# Uniform norm bound for the actual improper Binet moment names

Use a cofinal prefix extending beyond time one. Compact additivity
splits it at one, horizon coherence controls the early panel, and
the fixed-chart majorant controls the far panel. The bound depends
on the positive margin 1/K and on the moment order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginBound

open_ipra
open GaussianBinetLaplaceMomentFloor (gain nameF)
open GaussianBinetLaplaceMomentCompact (data regular)
open GaussianBinetLaplaceMomentImproper (cutoff cutoff_positive)
open GaussianBinetLaplaceMomentImproperBound (prefix_source unit_prefix_bound prefixGrid cofinal_refinement_error)
open GaussianBinetLaplaceMomentMarginTail (coefficient)
open GaussianBinetLaplaceMomentPrefixes (prefixData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (mesh precision)
open GaussianNameArithmetic (addF addData)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "stripSource" => GaussianBinetLaplaceStrip.source
local notation "improperF" => GaussianBinetLaplaceMomentImproper.nameF
local notation "improperData" => GaussianBinetLaplaceMomentImproper.data

def marginBound (j K : PTm n) : PTm n := two*coefficient j K+num 11

ipra_subst marginBound [two, one]

private theorem diagonal_error (a b p : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded a b (unit p+unit p) (unit p*unit p)) :
    Γ ⊢[PRAAx] distanceBounded a b two (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) h

theorem observation_bound (p j X D R K : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (ap2 improperF p (improperData j X D R)) (marginBound j K) one := by
  let C := cutoff p j D
  let L := one+C
  let x := ap2 improperF p (improperData j X D R)
  let a := data j X D R L zero one one
  let b := data j X D R L (zero+one) C one
  let c := prefixData j X D R L
  let U := unit p
  let N := two*coefficient j K
  have hp := unit_positive (Γ := Γ) p
  have hC := cutoff_positive (Γ := Γ) p j D
  have whole := prefix_source X D R L h
  have left : Γ ⊢[PRAAx] stripSource X zero D zero R L zero one one :=
    .andI h (.andI (le_refl one) (le_congr (zero_add one).eqSymm (one_mul L).eqSymm (le_add_right one C)))
  have right : Γ ⊢[PRAAx] stripSource X zero D zero R L (zero+one) C one :=
    .andI h (.andI (le_refl one) (le_congr (congrAdd (zero_add one).eqSymm (.eqRefl C)) (one_mul L).eqSymm (le_refl L)))
  have first : Γ ⊢[PRAAx] distanceBounded x (ap2 nameF p c) two U :=
    diagonal_error _ _ p (GaussianBinetLaplaceMomentImproper.late_observations p p j X D R L h (le_add_left _ _))
  have split := GaussianBinetLaplaceMomentAdditivity.additivity j X D R L zero one C one whole (le_refl one) hC
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p c) (ap2 (addF nameF nameF) p (addData a b)) two U :=
    diagonal_error _ _ p (GaussianNameEquivalence.cross_at _ _ _ _ p p split)
  have third := GaussianNameRingLaws.add_sample_error nameF nameF a b p
    (regular j X D R L zero one one left) (regular j X D R L (zero+one) C one right)
  have close : Γ ⊢[PRAAx] distanceBounded x (qadd (ap2 nameF p a) (ap2 nameF p b)) (num 7) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first second) third)
  have clocks := GaussianBinetLaplaceMomentHorizon.coherence j X D R L R one zero one one left
    (prefix_source X D R one h)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p a) (ap2 nameF p (prefixData j X D R one)) two U :=
    diagonal_error _ _ p (GaussianNameEquivalence.cross_at _ _ _ _ p p clocks)
  have firstBound : Γ ⊢[PRAAx] bounded (ap2 nameF p a) (U+two) U :=
    bound_congr (.eqRefl _) (by dsimp only [U]; ipra_ring) (mul_comm _ _ |>.eqTrans (one_mul _))
      (norm_from_distance _ _ _ _ _ _ hp (le_refl one) near (unit_prefix_bound p j X D R h))
  have secondBound : Γ ⊢[PRAAx] bounded (ap2 nameF p b) (N*U+one) U :=
    bound_congr (.eqRefl _) (by dsimp only [N,U]; ipra_ring) (by dsimp only [U]; ipra_ring)
      (GaussianBinetLaplaceMomentMarginTail.name_bound p j X D R K L (zero+one) C one right hK hmargin
        (le_congr (.eqRefl _) (zero_add one).eqSymm (le_refl one)) hC)
  have boundSum : Γ ⊢[PRAAx] bounded (qadd (ap2 nameF p a) (ap2 nameF p b)) ((N+one)*U+num 3) U :=
    bound_congr (.eqRefl _) (by dsimp only [U]; ipra_ring) (.eqRefl _)
      (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ hp firstBound secondBound)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp hp) (le_refl one)
    (by dsimp only [N,U,marginBound]; ipra_le 10*𝔞(unit p)*sl hp)
    (norm_from_distance _ _ _ _ _ _ hp hp close boundSum)

/-- The same cap, with three units for observation, applies to the
common refinement of any cofinal prefix used in the Taylor proof. -/
theorem cofinal_grid_bound (p q M N j X D R K L : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X)) (hN : Γ ⊢[PRAAx] le one N)
    (hM : Γ ⊢[PRAAx] M ≐ N*mesh p (gain j R L) L)
    (hq : Γ ⊢[PRAAx] le (precision p L) q) (hL : Γ ⊢[PRAAx] le (cutoff p j D) L) :
    Γ ⊢[PRAAx] bounded (prefixGrid q M j X D R L) (marginBound j K+num 3) one := by
  have hp := unit_positive (Γ := Γ) p
  have near := cofinal_refinement_error p q M N j X D R L h hN hM hq hL
  have cap := observation_bound p j X D R K h hK hmargin
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp (le_refl one)) (le_refl one)
    (by ipra_le 3*sl hp)
    (norm_from_distance _ _ _ _ _ _ hp (le_refl one) (distance_symmetric _ _ _ _ hp near) cap)

theorem actual_improper_Binet_moment_margin_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let p := var 0
     let j := var 1
     let X := var 2
     let D := var 3
     let R := var 4
     let K := var 5
     realSource X zero D zero R ⟶ (le one K ⋏ le D (K*X)) ⟶
       bounded (ap2 improperF p (improperData j X D R)) (marginBound j K) one) :=
  closeUniv 6 (.impI (.impI (observation_bound _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginBound
