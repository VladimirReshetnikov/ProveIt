import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentImproper
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentWidth
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence

/-!
# A uniform norm bound for the actual improper Binet moments

The original unit prefix has norm at most one. The checked tail rate
then bounds every improper observation. Any later compact prefix
retains its error bound when read on a refinement of its original
compact mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentImproperBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceMomentPrefixes (prefixData tailNumerator)
open GaussianBinetLaplaceMomentImproper (nameF data cutoff prefix_rate late_observations)
open GaussianBinetLaplaceMomentFloor (evaluatorF fixedData gain)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (quadrature mesh precision)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (rate_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "StripF" => GaussianBinetLaplaceMomentFloor.nameF

def momentBound (j D : PTm n) : PTm n := tailNumerator j D+num 3
def prefixGrid (q M j X D R L : PTm n) : PTm n :=
  quadrature evaluatorF q M (one+zero) L one (fixedData j X D R L)

@[simp] theorem subst_momentBound {m : ℕ} (σ : Fin n → PTm m) (j D : PTm n) :
    Syn.subst σ (momentBound j D) = momentBound (Syn.subst σ j) (Syn.subst σ D) := by simp [momentBound]
@[simp] theorem subst_prefixGrid {m : ℕ} (σ : Fin n → PTm m) (q M j X D R L : PTm n) :
    Syn.subst σ (prefixGrid q M j X D R L) =
      prefixGrid (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ L) := by
  simp [prefixGrid,one]

theorem prefix_source (X D R L : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X zero D zero R L zero L one :=
  .andI h (.andI (le_refl one) (le_congr (zero_add L).eqSymm (one_mul L).eqSymm (le_refl L)))

theorem unit_prefix_bound (p j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] bounded (ap2 StripF p (prefixData j X D R one)) one one := by
  have base := GaussianBinetLaplaceMomentWidth.width_bound p j X D R one zero one one (prefix_source X D R one h)
  exact bound_congr (.eqRefl _)
    ((one_mul _).eqTrans (GaussianPolynomialPerturbation.one_power j)) (.eqRefl _) base

theorem observation_bound (p j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R)) (momentBound j D) one := by
  let U := unit p
  let N := tailNumerator j D
  let x := ap2 nameF p (data j X D R)
  let y := ap2 StripF p (prefixData j X D R one)
  have hp := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ (le_refl (one : PTm n)) (positive_product _ _ hp hp)
  have near := rate_at nameF StripF (data j X D R) (prefixData j X D R one) N one p p
    (prefix_rate j X D R one h (le_refl one))
  have d : Γ ⊢[PRAAx] distanceBounded x y (N+two) one :=
    distance_radius_mono _ _ _ _ _ _ (le_congr (.eqRefl _) (by unfold GaussianNamedInverseRate.rateDenominator; ipra_ring) hD)
      (le_refl one) (by
        unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator
        ipra_le 2*𝔞(U)*sl hp) near
  have b := norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) d (unit_prefix_bound p j X D R h)
  exact bound_congr (.eqRefl _) (by dsimp only [momentBound,N]; ipra_ring) (one_mul _) b

theorem refinement_error (p q M K j X D R L : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hK : Γ ⊢[PRAAx] le one K)
    (hM : Γ ⊢[PRAAx] M ≐ K*mesh p (gain j R L) L) (hq : Γ ⊢[PRAAx] le (precision p L) q) :
    Γ ⊢[PRAAx] distanceBounded (prefixGrid q M j X D R L) (ap2 StripF p (prefixData j X D R L)) one (unit p) := by
  let x := fixedData j X D R L
  let G := gain j R L
  have src := GaussianBinetLaplaceMomentCompact.compact_input j X D R L zero L one (prefix_source X D R L h)
  have diff := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF p q K (one+zero) L one G L x src hK hq
  have first := GaussianCompactRiemannName.quadrature_index_congr evaluatorF q M (K*mesh p G L) (one+zero) L one x hM
  have second := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF p (one+zero) L one G L x
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (GaussianCompactRiemannName.dyadic_six_lower p))
    (distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _) diff)

theorem cofinal_refinement_error (p q M K j X D R L : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hK : Γ ⊢[PRAAx] le one K)
    (hM : Γ ⊢[PRAAx] M ≐ K*mesh p (gain j R L) L) (hq : Γ ⊢[PRAAx] le (precision p L) q)
    (hL : Γ ⊢[PRAAx] le (cutoff p j D) L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R)) (prefixGrid q M j X D R L) (num 3) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have first := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (late_observations p p j X D R L h hL)
  have second := distance_symmetric _ _ _ _ hp (refinement_error p q M K j X D R L h hK hM hq)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first second)

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentImproperBound
