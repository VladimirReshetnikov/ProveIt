import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.GaussianStirlingAllOrderFirstPanelName
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.FinitePanels.GaussianStirlingAllOrderPanelPartsRows

/-!
# Arbitrary fine meshes for the original first Bernoulli panel

The two finite harmonic intervals are compared through their common
multiple. This permits a single mesh across every original panel,
regardless of the separate schedules used by the native logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelCommonMesh

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qzero qadd qmul)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianStirlingAllOrderFirstPanelReadback (halfPanel harmonic_distance)
open GaussianStirlingAllOrderFirstPanelName (clock name_at point_cross)
open GaussianStirlingAllOrderFirstPanelNamed (mesh mesh_large)
open GaussianStirlingAllOrderPanelPartsRows (scalar_order_bound)
open GaussianStirlingDifference (coefficient minusOne)
open GaussianStirlingOddReadback (affine)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianNameBounds (U sample_bound)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open RationalHarmonicInterval (interval refinement)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem interval_congr (a b : PTm n) {Q R : PTm n} (h : Γ ⊢[PRAAx] Q ≐ R) :
    Γ ⊢[PRAAx] interval a b Q ≐ interval a b R := by
  simpa only [RationalHarmonicInterval.subst_interval,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (interval (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![a,b,Q]) (σ' := ![a,b,R]) (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact h)

theorem harmonic_observations (a b Q R p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le (unit p) Q) (hR : Γ ⊢[PRAAx] le (unit p) R) :
    Γ ⊢[PRAAx] distanceBounded (embed (interval a b Q)) (embed (interval a b R)) two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have h₁ := le_trans hp hQ
  have h₂ := le_trans hp hR
  have q := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ h₁ (refinement a b Q R ha hb h₁ h₂)
  have r := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ h₂ (refinement a b R Q ha hb h₂ h₁)
  have eq := embed_congr (interval_congr a b (mul_comm (Γ := Γ) Q R))
  have dq := distance_radius_mono _ _ _ _ one (unit p) h₁ hp
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm hQ) (distance_symmetric _ _ _ _ h₁ q)
  have dr := distance_radius_mono _ _ _ _ one (unit p) h₂ hp
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm hR) (distance_congr eq (.eqRefl _) (.eqRefl _) (.eqRefl _) r)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hp dq dr)

private theorem coefficient_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (coefficient A B) (A+B) one := by
  let c := fraction (two*A+B) (two*B)
  have hd : Γ ⊢[PRAAx] le one (two*B) := positive_product _ _ (by ipra_le 1) hB
  have lo := fraction_order zero one (two*A+B) (two*B) (le_refl one) hd (by ipra_le 𝔞 (two*A+B))
  have hi := fraction_order (two*A+B) (two*B) (A+B) one hd (le_refl one) (by
    ipra_le (2*𝔞 A+2*𝔞 B)*sl hB+𝔞 B)
  exact GaussianRationalReciprocal.bound_congr (GaussianEulerDecayOrder.fraction_embedding _ _ hd) (.eqRefl _) (.eqRefl _)
    (scalar_order_bound c (A+B) one (le_refl one) lo hi)

private theorem affine_distance (A B a b D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded a b two D) : Γ ⊢[PRAAx]
    distanceBounded (affine A B a) (affine A B b) (two*(A+B)) D := by
  let c := coefficient A B
  have hb : Γ ⊢[PRAAx] bounded a (U constantF a) one :=
    GaussianRationalReciprocal.bound_congr (constant_at zero a) (.eqRefl _) (.eqRefl _)
      (sample_bound constantF a zero (constant_regular a))
  have hm := GaussianNameArithmetic.product_distance c c a b zero two D (U constantF a) (A+B) hD
    (distance_refl_zero c D hD) h hb (coefficient_bound A B hB)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ minusOne minusOne _ zero D hD hm (distance_refl_zero _ _ hD))

private theorem half_to_affine (A B Q k p : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le (unit p) Q) :
    Γ ⊢[PRAAx] distanceBounded (halfPanel A B Q k)
      (affine (A+B*k) B (embed (interval ((A+B*k)+B) (A+B*k) Q))) ((A+B*k)+B) (unit p) := by
  let a := A+B*k
  let d := two*(B*succ (Q*a))
  have ha : Γ ⊢[PRAAx] le one a := le_trans hA (le_add_right A (B*k))
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ (by ipra_le 1) (positive_product _ _ hB (zero_lt_succ _))
  have Qd : Γ ⊢[PRAAx] le Q d := by
    unfold d
    ipra_le 𝔞 Q*sl ha+2*𝔞 (succ (Q*a))*sl hB+𝔞 (Q*a)+2
  have pd := le_trans hQ Qd
  exact distance_radius_mono _ _ _ _ (a+B) (unit p) hd (unit_positive p) (mul_le_mul_left (a+B) pd)
    (harmonic_distance A B Q k hA hB (le_trans (unit_positive p) hQ))

theorem half_panel_comparison (A B Q R k p : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hQ : Γ ⊢[PRAAx] le (unit p) Q) (hR : Γ ⊢[PRAAx] le (unit p) R) :
    Γ ⊢[PRAAx] distanceBounded (halfPanel A B Q k) (halfPanel A B R k)
      (LeanProofs.IPRA.PTm.num 4*((A+B*k)+B)) (unit p) := by
  let a := A+B*k
  have ha : Γ ⊢[PRAAx] le one a := le_trans hA (le_add_right A (B*k))
  have hp := unit_positive (Γ := Γ) p
  have eq := half_to_affine A B Q k p hA hB hQ
  have er := distance_symmetric _ _ _ _ hp (half_to_affine A B R k p hA hB hR)
  have eh := harmonic_observations (a+B) a Q R p (le_trans ha (le_add_right a B)) ha hQ hR
  have em := affine_distance a B _ _ _ hB hp eh
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold a; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp eq em) er)

theorem original_difference_at (A B Q k p : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le (unit p) Q) :
    Γ ⊢[PRAAx] distanceBounded (halfPanel A B Q k)
      (ap2 GaussianStirlingDifference.nameF p (GaussianStirlingDifference.data (A+B*k) B))
      (LeanProofs.IPRA.PTm.num 4*((A+B*k)+B)+two) (unit p) := by
  let a := A+B*k
  let t := clock A B k p
  let R := mesh a B t
  have hp := unit_positive (Γ := Γ) p
  have ht : Γ ⊢[PRAAx] le p t := by
    unfold t clock GaussianFastValueCut.exponent
    exact le_add_right _ _
  have hr := le_trans (GaussianExponentialReference.unit_monotone ht) (mesh_large a B t)
  have h := half_panel_comparison A B Q R k p hA hB hQ hr
  have h' := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (by ipra_le 0) (point_cross A B k p p hA hB)
  exact distance_triangle_same _ _ _ _ _ _ hp h
    (distance_congr (name_at A B k p) (.eqRefl _) (.eqRefl _) (.eqRefl _) h')

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelCommonMesh
