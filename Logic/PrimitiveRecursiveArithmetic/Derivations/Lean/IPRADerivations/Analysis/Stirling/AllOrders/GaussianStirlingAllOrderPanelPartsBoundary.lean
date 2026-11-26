import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelPartsFinite

/-!
# Uniform bound on the actual scaled adjacent boundary term

At both endpoints H vanishes exactly. The two surviving adjacent
samples are O(M^-2), cancelling the M^2 scale on the discrete boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsBoundary

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderCenteredBernoulli (sample endpoint_samples_zero)
open GaussianStirlingAllOrderBernoulliEnvelope (sample_envelope sample_congr)
open GaussianStirlingAllOrderEndpointError (endpointCoefficient endpoint_upper reflected_endpoint_upper)
open GaussianStirlingAllOrderCentralBernoulliError (radiusDenominator radius_denominator_positive)
open GaussianStirlingAllOrderPanelPartsRows (scalar_order_bound weight_bound)
open GaussianStirlingAllOrderPanelPartsFinite
  (interior interior_le_mesh profileBody profile_at weightBody weightAt weight_at parameters boundaryValue interiorDensity interior_error)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderDiscreteParts (sub adjacent crossValue)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded bounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalReciprocal (bounded_product bound_congr bounded_negative)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open RationalGaussianEmbedding (embed embed_zero embed_add embed_negative embed_multiply embed_canonical)
open RationalGaussianRealPart (embed_congr)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr multiply_congr negative_congr multiply_commutative negative_minus_multiply add_commutative)
open RationalReciprocalPowerTail (add_zero_right)
open RationalArgmin (rationalLE_congr reflexive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def boundaryCap (m e : ℕ) (B : PTm n) : PTm n :=
  two*num (endpointCoefficient m)*power e B

private theorem negative_zero : Γ ⊢[PRAAx] negative (fraction zero one : PTm n) ≐ fraction zero one :=
  (negative_minus_multiply _).eqTrans (multiply_zero_right _)

private theorem endpoint_order (m : ℕ) (hm : 0<m) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    (Γ ⊢[PRAAx] bounded (embed (sample (m+1) one M)) (num (endpointCoefficient m)) (M*M)) ∧
      (Γ ⊢[PRAAx] bounded (embed (sample (m+1) (interior M) M)) (num (endpointCoefficient m)) (M*M)) := by
  let P := M*M
  let D := radiusDenominator m M
  let K : PTm n := num (endpointCoefficient m)
  have hD := radius_denominator_positive m M hM
  have hs := endpoint_upper m hm one M hM hM
  have hf := reflected_endpoint_upper m hm one M hM hM
  have h₁ := (sample_envelope m one M hM hM).andE₁
  have h₂ := (sample_envelope m (interior M) M hM (interior_le_mesh M hM)).andE₁
  have q : Γ ⊢[PRAAx] fraction (K*(one*one)) D ≐ fraction K D := by
    exact RationalNonnegativePowers.fraction_congr (by ipra_ring) (.eqRefl _)
  have b₁ := scalar_order_bound _ _ _ hD h₁ (rationalLE_congr (.eqRefl _) q hs)
  have b₂ := scalar_order_bound _ _ _ hD h₂ (rationalLE_congr (.eqRefl _) q hf)
  have hC : Γ ⊢[PRAAx] le one (num (BernoulliBounds.bden (GaussianStirlingAllOrderCentralBernoulliError.degree m)) : PTm n) :=
    Foundations.NumeralPrimes.num_le (a := 1) (BernoulliBounds.bden_pos _)
  have hb : Γ ⊢[PRAAx] le (K*P) (K*D) := by
    unfold P D radiusDenominator
    ipra_le 𝔞 K*𝔞 M*𝔞 M*sl hC
  exact ⟨bounded_radius_mono _ _ _ _ _ hD (positive_product _ _ hM hM) hb b₁,
    bounded_radius_mono _ _ _ _ _ hD (positive_product _ _ hM hM) hb b₂⟩

private theorem cross_endpoints (m e : ℕ) (U B M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    let f := profileBody m
    let g := weightBody e
    let N := interior M
    let x := parameters U B M
    (Γ ⊢[PRAAx] crossValue f g M x zero ≐ multiply (sample (m+1) one M) (weightAt e U B M zero)) ∧
      (Γ ⊢[PRAAx] crossValue f g M x N ≐ negative (multiply (sample (m+1) N M) (weightAt e U B M M))) := by
  let y := parameters U B M
  let f := profileBody m
  let g := weightBody e
  let N := interior M
  let z : PTm n := fraction zero one
  have hs : Γ ⊢[PRAAx] succ N ≐ M :=
    (succ_eq_add_one N).eqTrans ((add_comm _ _).eqTrans (eq_add_of_le hM).eqSymm)
  have hf := endpoint_samples_zero (Γ := Γ) (m+1) M hM
  have left : Γ ⊢[PRAAx] crossValue f g M y zero ≐ multiply (sample (m+1) one M) (weightAt e U B M zero) := by
    have el : Γ ⊢[PRAAx] multiply (inst2 f (succ zero) M) (inst2 g zero y) ≐
        multiply (sample (m+1) one M) (weightAt e U B M zero) := by
      simp only [f,g,profile_at]
      exact multiply_congr (.eqRefl _) (weight_at e U B M zero)
    have er : Γ ⊢[PRAAx] multiply (inst2 f zero M) (inst2 g (succ zero) y) ≐ z := by
      simp only [f,profile_at]
      exact (multiply_congr hf.1 (.eqRefl _)).eqTrans ((multiply_commutative _ _).eqTrans (multiply_zero_right _))
    exact (add_congr el ((negative_congr er).eqTrans negative_zero)).eqTrans
      (add_zero_right _ (RationalArithmetic.multiply_guard _ _))
  have right : Γ ⊢[PRAAx] crossValue f g M y N ≐ negative (multiply (sample (m+1) N M) (weightAt e U B M M)) := by
    have ep : Γ ⊢[PRAAx] inst2 f (succ N) M ≐ z := by
      simp only [f,profile_at]
      exact (sample_congr _ hs (.eqRefl _)).eqTrans hf.2
    have eg : Γ ⊢[PRAAx] inst2 g (succ N) y ≐ weightAt e U B M M := by
      have ev := (weight_at (Γ := Γ) e U B M (succ N))
      exact ev.eqTrans (RationalNonnegativePowers.fraction_congr (.eqRefl _)
        (congrAp2 powF (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (.eqRefl _) hs))))
    have ep₁ : Γ ⊢[PRAAx] multiply (inst2 f (succ N) M) (inst2 g N y) ≐ z :=
      (multiply_congr ep (.eqRefl _)).eqTrans ((multiply_commutative _ _).eqTrans (multiply_zero_right _))
    have eg₁ : Γ ⊢[PRAAx] multiply (inst2 f N M) (inst2 g (succ N) y) ≐
        multiply (sample (m+1) N M) (weightAt e U B M M) := by
      simp only [f,profile_at]
      exact multiply_congr (.eqRefl _) eg
    exact (add_congr ep₁ (negative_congr eg₁)).eqTrans ((add_commutative _ _).eqTrans
      (add_zero_right _ (RationalArithmetic.negative_guard _)))
  exact ⟨left,right⟩

theorem original_boundary_bound (m e : ℕ) (hm : 0<m) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (embed (boundaryValue m e U B M)) (boundaryCap m e B) one := by
  let N := interior M
  let P := M*M
  let K : PTm n := num (endpointCoefficient m)
  let Bn := power e B
  let a := multiply (sample (m+1) one M) (weightAt e U B M zero)
  let b := multiply (sample (m+1) N M) (weightAt e U B M M)
  let L := fraction P one
  let S := K*Bn
  let s := sub (negative b) a
  have Hp := positive_product _ _ hM hM
  have ep := endpoint_order m hm M hM
  have hb₁ := weight_bound e U B M zero hU hM
  have hb₂ := weight_bound e U B M M hU hM
  have b₁ : Γ ⊢[PRAAx] bounded (embed a) S P :=
    bound_congr (embed_multiply _ _).eqSymm (.eqRefl _) (by unfold P; ipra_ring)
      (bounded_product _ _ _ _ _ _ Hp (le_refl one) ep.1 hb₁)
  have b₂ : Γ ⊢[PRAAx] bounded (embed b) S P :=
    bound_congr (embed_multiply _ _).eqSymm (.eqRefl _) (by unfold P; ipra_ring)
      (bounded_product _ _ _ _ _ _ Hp (le_refl one) ep.2 hb₂)
  have bs : Γ ⊢[PRAAx] bounded (embed s) (S+S) P :=
    bound_congr ((embed_add _ _).eqTrans (qadd_congr (embed_negative _) (embed_negative _))).eqSymm
      (.eqRefl _) (.eqRefl _) (bounded_sum_same _ _ _ _ _ Hp (bounded_negative _ _ _ Hp b₂) (bounded_negative _ _ _ Hp b₁))
  have bl : Γ ⊢[PRAAx] bounded (embed L) P one :=
    scalar_order_bound _ _ _ (le_refl one) (fraction_order _ _ _ _ (le_refl one) (le_refl one) (by ipra_le 𝔞 P))
      (reflexive _)
  have hmul := bounded_product _ _ _ _ _ _ (le_refl one) Hp bl bs
  have eq := cross_endpoints m e U B M hM
  have E : Γ ⊢[PRAAx] boundaryValue m e U B M ≐ multiply L s :=
    multiply_congr (.eqRefl _) (add_congr eq.2 (negative_congr eq.1))
  apply bound_congr ((embed_congr E).eqTrans (embed_multiply _ _)).eqSymm (.eqRefl _) (.eqRefl _)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) Hp) (le_refl one)
    (by unfold boundaryCap S P K Bn; ipra_le 0) hmul

theorem interior_density_bound (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (embed (interiorDensity m e U B M))
      (GaussianStirlingAllOrderPanelPartsRows.rowRadius m e U B+boundaryCap m e B) one := by
  let p := embed (interiorDensity m e U B M)
  let q := embed (boundaryValue m e U B M)
  let R := GaussianStirlingAllOrderPanelPartsRows.rowRadius m e U B
  let T := boundaryCap m e B
  let N := interior M
  let P := M*M
  have Hp := positive_product _ _ hM hM
  have Hn : Γ ⊢[PRAAx] le N P := le_trans (interior_le_mesh M hM) (by unfold P; ipra_le 𝔞 M*sl hM)
  have close := interior_error m e hm he U B M hU hM
  have cp := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ R one Hp (le_refl one)
    (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right R Hn)) (distance_symmetric _ _ _ _ Hp close)
  have b := original_boundary_bound m e hm U B M hU hM
  have hb : Γ ⊢[PRAAx] distanceBounded q qzero T one :=
    bound_congr (GaussianRationalReconstruction.qsub_zero_right q (embed_canonical _)).eqSymm (.eqRefl _) (.eqRefl _) b
  exact bound_congr (GaussianRationalReconstruction.qsub_zero_right p (embed_canonical _)) (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (le_refl one) cp hb)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsBoundary
