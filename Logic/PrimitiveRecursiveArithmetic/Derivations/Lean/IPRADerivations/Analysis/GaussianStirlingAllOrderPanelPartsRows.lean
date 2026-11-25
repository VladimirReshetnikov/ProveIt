import IPRADerivations.Analysis.GaussianStirlingAllOrderReciprocalGridError
import IPRADerivations.Analysis.GaussianStirlingAllOrderEndpointError
import IPRADerivations.Analysis.GaussianStirlingAllOrderFirstPanelReadback
import IPRADerivations.Analysis.GaussianNamedDifference

/-!
# Quantitative local residual of the original discrete parts identity

The weighted second differences use the literal centered Bernoulli
profile and the literal reciprocal-power grid. Their difference
approximates the corresponding derivative products at the same point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderCenteredBernoulli (sample)
open GaussianStirlingAllOrderBernoulliEnvelope (cap sample_envelope)
open GaussianStirlingAllOrderPanelDerivative (secondSample)
open GaussianStirlingAllOrderCentralBernoulliError (radiusNumerator radiusDenominator radius_denominator_positive)
open GaussianStirlingAllOrderDiscreteParts (sub defect secondDifference)
open GaussianStirlingAllOrderReciprocalWeightError (power weight derivative)
open GaussianStirlingAllOrderReciprocalGridError (gridDen gridCoefficient row_bounds grid_error)
open GaussianStirlingAllOrderFirstPanelReadback (upper_of_add_order)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr multiply_congr negative_congr multiply_commutative multiply_associative
  multiply_add multiply_negative add_commutative)
open RationalReciprocalPowerTail (add_zero_right)
open RationalGaussianEmbedding (embed embed_add embed_multiply embed_negative embed_zero embed_canonical)
open RationalGaussianRealPart (embed_congr)
open RationalArgmin (rationalLE rationalLE_congr transitive denominator_positive)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper_of_order radius_of_upper radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "p2" => GaussianStirlingAllOrderCentralBernoulliError.scaledSecond
local notation "w2" => GaussianStirlingAllOrderReciprocalWeightError.scaledSecond

theorem scalar_order_bound (a N D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (lo : Γ ⊢[PRAAx] rationalLE (fraction zero one) a)
    (hi : Γ ⊢[PRAAx] rationalLE a (fraction N D)) :
    Γ ⊢[PRAAx] bounded (embed a) N D := by
  let z : PTm n := fraction zero one
  have cz : Γ ⊢[PRAAx] embed z ≐ qzero := embed_zero
  have e : Γ ⊢[PRAAx] fraction N D ≐ add z (fraction N D) :=
    ((add_commutative z (fraction N D)).eqTrans
      (add_zero_right _ (RationalNormalForm.normalize_well_formed _ _ hD))).eqSymm
  have u := upper_of_add_order a z N D hD (rationalLE_congr (.eqRefl _) e hi)
  have l := upper_of_order z a N D lo
  have r := RationalGaussianNameEmbedding.distance_from_radius a z N D hD (radius_of_upper _ _ _ _ u l)
  have h := distance_congr (.eqRefl _) cz (.eqRefl _) (.eqRefl _) r
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalReconstruction.qsub_zero_right (embed a) (embed_canonical a)) (.eqRefl _) (.eqRefl _) h

def profileCap (m : ℕ) : PTm n := (numeratorOf (cap (n := n) m)).pos

private theorem natural_cap (v : PTm n) : Γ ⊢[PRAAx] rationalLE v (fraction (numeratorOf v).pos one) := by
  let E := denominatorOf v
  let x := numeratorOf v
  have hE := denominator_positive (Γ := Γ) v
  apply RationalArithmetic.order_of_representations _ _ _ _ E one
    (RationalRepresentations.represents_self v) (fraction_represents _ _ (le_refl one)) hE (le_refl one)
  apply zle_of_comb (𝔞(x.pos)*sl hE+𝔞(x.neg))
  · change ZT.toZ Γ (ZT.ofNat x.pos*ZT.ofNat E)-ZT.toZ Γ (x*ZT.ofNat one) = _
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,sl_def]
    simp only [ZT.toZ]
    ipra_simps
    unfold E x
    ring
  · exact nn_add (nn_mul (nn_term _) (nn_sl hE)) (nn_term _)

theorem profile_bound (m : ℕ) (r M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] bounded (embed (sample (m+1) r M)) (profileCap m) one := by
  have h := sample_envelope m r M hM hr
  exact scalar_order_bound _ _ _ (le_refl one) h.andE₁ (transitive h.andE₂ (natural_cap _))

theorem weight_bound (e : ℕ) (U B M r : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (embed (weight e B M (gridDen U B M r))) (power e B) one := by
  let D := gridDen U B M r
  have hd : Γ ⊢[PRAAx] le M D := by unfold D gridDen; ipra_le 𝔞 M*sl hU+𝔞 B*𝔞 r
  have hp : Γ ⊢[PRAAx] le one (power e D) := GaussianFactorBudget.power_positive _ _ (le_trans hM hd)
  have lo : Γ ⊢[PRAAx] rationalLE (fraction zero one) (weight e B M D) :=
    fraction_order _ _ _ _ (le_refl one) hp (by ipra_le 𝔞 (power e (B*M)))
  have hi : Γ ⊢[PRAAx] rationalLE (weight e B M D) (fraction (power e B) one) := by
    apply fraction_order _ _ _ _ hp (le_refl one)
    have h := mul_le_mul_right (power e B) (pw_le_pw (num e) hd)
    refine le_congr ?_ (mul_comm _ _) h
    exact (mul_comm _ _).eqTrans
      ((AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) B M (num e)).eqSymm.eqTrans (one_mul _).eqSymm)
  exact scalar_order_bound _ _ _ (le_refl one) lo hi

private theorem weight_step (e : ℕ) (U B M r : PTm n) (hr : Γ ⊢[PRAAx] le one r)
    (hB : Γ ⊢[PRAAx] le B (gridDen U B M r)) :
    (Γ ⊢[PRAAx] weight e B M (gridDen U B M (r+one)) ≐ weight e B M (gridDen U B M r+B)) ∧
      (Γ ⊢[PRAAx] weight e B M (gridDen U B M (monus r one)) ≐ weight e B M (monus (gridDen U B M r) B)) := by
  constructor
  · exact RationalNonnegativePowers.fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) (by unfold gridDen; ipra_ring))
  · apply RationalNonnegativePowers.fraction_congr (.eqRefl _)
    apply congrAp2 powF (.eqRefl _)
    have e := natEq (eq_add_of_le hr)
    have f := natEq (eq_add_of_le hB)
    apply deriveNat
    unfold gridDen at f ⊢
    ipra_simps
    linear_combination f-𝔞 B*e

def approxRow (m e : ℕ) (U B M r : PTm n) : PTm n :=
  let f := sample (m+1)
  let g := fun i => weight e B M (gridDen U B M i)
  multiply (fraction (M*M) one)
    (defect (f (monus r one) M) (f r M) (f (r+one) M) (g (monus r one)) (g r) (g (r+one)))

def targetRow (m e : ℕ) (U B M r : PTm n) : PTm n :=
  sub (multiply (secondSample m r M) (weight e B M (gridDen U B M r)))
    (multiply (sample (m+1) r M) (derivative e (gridDen U B M r) B M))

def rowRadius (m e : ℕ) (U B : PTm n) : PTm n :=
  radiusNumerator m*power e B+gridCoefficient e U B*profileCap m

private theorem embed_sub (a b : PTm n) : Γ ⊢[PRAAx] embed (sub a b) ≐ qsub (embed a) (embed b) :=
  (embed_add a (negative b)).eqTrans (qadd_congr (.eqRefl _) (embed_negative b))

private theorem embed_difference_products (a b c d : PTm n) : Γ ⊢[PRAAx]
    embed (sub (multiply a c) (multiply b d)) ≐
      qsub (GaussianRationalHorner.qmul (embed a) (embed c)) (GaussianRationalHorner.qmul (embed b) (embed d)) :=
  (embed_sub (multiply a c) (multiply b d)).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (embed_multiply a c) (embed_multiply b d))

private theorem scale_difference (s a b c d : PTm n) :
    Γ ⊢[PRAAx] multiply s (sub (multiply a c) (multiply b d)) ≐
      sub (multiply (multiply s a) c) (multiply b (multiply s d)) :=
  (multiply_add _ _ _).eqTrans
    (add_congr (multiply_associative _ _ _).eqSymm
      ((multiply_negative _ _).eqTrans (negative_congr ((multiply_associative _ _ _).eqSymm.eqTrans
        ((multiply_congr (multiply_commutative _ _) (.eqRefl _)).eqTrans (multiply_associative _ _ _))))))

private theorem fixed_product (a b c A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded a b A B) (hC : Γ ⊢[PRAAx] bounded c R one) :
    Γ ⊢[PRAAx] distanceBounded (GaussianRationalHorner.qmul a c) (GaussianRationalHorner.qmul b c) (A*R) B := by
  let V := GaussianNameBounds.U constantF b
  have hb := GaussianRationalReciprocal.bound_congr (constant_at (Γ := Γ) zero b) (.eqRefl _) (.eqRefl _)
    (GaussianNameBounds.sample_bound constantF b zero (constant_regular b))
  have u := GaussianNameArithmetic.product_distance a b c c A zero B R V hB h
    (GaussianRationalPowerDifference.distance_refl_zero c B hB) hC hb
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) u

theorem row_error (m e : ℕ) (hm : 0<m) (he : 2≤e) (U B M r : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le one r)
    (hrm : Γ ⊢[PRAAx] le r M) : Γ ⊢[PRAAx]
    distanceBounded (embed (approxRow m e U B M r)) (embed (targetRow m e U B M r)) (rowRadius m e U B) (M*M) := by
  let D := gridDen U B M r
  let P := M*M
  let S := fraction P one
  let h := sample (m+1) r M
  let w := weight e B M D
  let a := secondSample m r M
  let b := derivative e D B M
  let hx := p2 m r M
  let wx := w2 e D B M
  have Hp := positive_product _ _ hM hM
  have hi := GaussianStirlingAllOrderCentralBernoulliError.curvature_error m r M hm hM hr hrm
  have hb := radius_denominator_positive m M hM
  have hB : Γ ⊢[PRAAx] le one (num (BernoulliBounds.bden (GaussianStirlingAllOrderCentralBernoulliError.degree m)) : PTm n) :=
    Foundations.NumeralPrimes.num_le (a := 1) (BernoulliBounds.bden_pos _)
  have hRel : Γ ⊢[PRAAx] le (radiusNumerator m*P) (radiusNumerator m*radiusDenominator m M) := by
    unfold radiusDenominator P
    ipra_le 𝔞 (radiusNumerator m)*𝔞 M*𝔞 M*sl hB
  have hr₁ := RationalGaussianNameEmbedding.distance_from_radius hx a (radiusNumerator m) P Hp
    (radius_mono _ _ _ _ _ _ hb hi hRel)
  have hr₂ := RationalGaussianNameEmbedding.distance_from_radius wx b (gridCoefficient e U B) P Hp
    (grid_error e he U B M r hU hM hr hrm)
  have hw := weight_bound e U B M r hU hM
  have hh := profile_bound m r M hM hrm
  have firstProduct := fixed_product _ _ (embed w) _ P _ Hp hr₁ hw
  have secondProduct := fixed_product _ _ (embed h) _ P _ Hp hr₂ hh
  have d₂ := distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)
    (.eqRefl _) (.eqRefl _) secondProduct
  have obs := GaussianNamedDifference.difference_distance _ _ _ _ _ _ P Hp firstProduct d₂
  have ew := weight_step e U B M r hr (row_bounds U B M r hU hr hrm).andE₁
  have ew' : Γ ⊢[PRAAx] multiply S
      (secondDifference (weight e B M (gridDen U B M (monus r one))) w (weight e B M (gridDen U B M (r+one)))) ≐ wx :=
    multiply_congr (.eqRefl S) (add_congr (add_congr ew.1 ew.2) (.eqRefl (negative (add w w))))
  have e₁ : Γ ⊢[PRAAx] approxRow m e U B M r ≐ sub (multiply hx w) (multiply h wx) :=
    (scale_difference _ _ _ _ _).eqTrans (add_congr (.eqRefl _) (negative_congr (multiply_congr (.eqRefl _) ew')))
  exact distance_congr ((embed_congr e₁).eqTrans (embed_difference_products hx h w wx)).eqSymm
    (embed_difference_products a h w b).eqSymm (.eqRefl _) (.eqRefl _) obs

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsRows
