import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetSineRealDampedPanels
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetSineQuotientClock

/-!
# Uniform size of the actual sine quotient near zero frequency

Use the original exponential linear remainder on angles of size at
most one and the original unit bound on larger angles. Division by the
positive frequency then gives a linear bound in time with a dyadic
sample error, even on the first positive mesh panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineQuotientMajorant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq)
open GaussianBinetExponentialIntegralGrid (exponent row)
open GaussianBinetExponentialPanel (sample unit_bound)
open GaussianBinetImaginaryExponentialIntegral (coefficient coefficient_bound exponent_nonpositive)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianBinetSineDampedPanels (multiplier)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameEquivalence (cross_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul ofGaussian_represents)
open GaussianRationalLowerBounds (inverse_bound)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub qnegative qnegative_canonical qnegative_represents)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product bounded_sum reciprocal)
open GaussianRationalSyntheticDivision (qone qadd_sub_cancel qmul_congr qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qmul_one_right qmul_associative)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def pairDifference (p A B C : PTm n) : PTm n :=
  qsub (row p (coefficient A B (polarity true)) (C*one) one one)
    (row p (coefficient A B (polarity false)) (C*one) one one)

private theorem polarity_bit (s : Bool) : Γ ⊢[PRAAx] polarity s ≐ zero ⋎ polarity s ≐ one := by
  cases s
  · exact .orI₁ (.eqRefl _)
  · exact .orI₂ (.eqRefl _)

theorem coefficient_bound_exact (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (coefficient A B (polarity s)) A B := by
  let z := native zero A (polarity s)
  let v := ComplexLogarithmRemainder.neg z
  have h : Γ ⊢[PRAAx] normSq v ≐ A*A := (ComplexLogarithmRemainder.normSq_neg z).eqTrans
    ((GaussianLogGammaEulerResidualRadius.native_norm zero A (polarity s) (polarity_bit s)).eqTrans (by ipra_ring))
  exact bounded_of_cleared _ v B A B hB hB
    (qnegative_represents (argument zero A B (polarity s)) z B (ofGaussian_represents _ _ hB))
    (le_congr (congrMul (.eqRefl (B*B)) h.eqSymm) (by ipra_ring) (le_refl ((B*B)*(A*A))))

private theorem exponent_at_unit (c : PTm n) (hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical c) :
    Γ ⊢[PRAAx] exponent c one one ≐ c :=
  (qmul_congr (.eqRefl _) (GaussianRationalExponentialTangent.fraction_one one (le_refl one))).eqTrans (qmul_one_right c hc)

private theorem unit_input (s : Bool) (A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hC : Γ ⊢[PRAAx] le A (C*B)) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF (C*one) (coefficient A B (polarity s)) :=
  GaussianSignedNameExponentialOrder.constant_input _ _
    (bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) (coefficient_bound A B (polarity s) C hB (polarity_bit s) hC))

private theorem direct_sample (s : Bool) (p A B C : PTm n) : Γ ⊢[PRAAx]
    row p (coefficient A B (polarity s)) (C*one) one one ≐ sample p (coefficient A B (polarity s)) (C*one) :=
  congrAp2 GaussianBinetExponentialPanel.expoF (.eqRefl _)
    (congrPairT (.eqRefl _) (exponent_at_unit _ (qnegative_canonical _)))

private theorem linear_sample_bound (s : Bool) (p A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le A (C*B)) (ha : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx]
    distanceBounded (row p (coefficient A B (polarity s)) (C*one) one one) qone
      (two*A*unit p+two*B) (B*unit p) := by
  let c := coefficient A B (polarity s)
  let P := unit p
  let w := row p c (C*one) one one
  let v := sample p c one
  let g := qadd qone c
  have hP := unit_positive (Γ := Γ) p
  have hc := coefficient_bound_exact s A B hB
  have in₁ := GaussianSignedNameExponentialOrder.constant_input c one
    (bounded_radius_mono _ _ _ _ _ hB (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) ha) hc)
  have equal := GaussianExponentialRadiusIndependence.same_input_cross constantF (C*one) one c (unit_input s A B C hB hC) in₁
  have step₀ : Γ ⊢[PRAAx] distanceBounded w v two P :=
    distance_radius_mono _ _ (P+P) (P*P) two P (positive_product _ _ hP hP) hP
      (le_of_eq_add (d := zero) (by ipra_ring))
      (distance_congr (direct_sample s p A B C).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (cross_at _ _ _ _ p p equal))
  have hB₂ := positive_product _ _ hB hB
  have step₁ : Γ ⊢[PRAAx] distanceBounded v g A B :=
    distance_radius_mono _ _ (A*A) (B*B) A B hB₂ hB (by ipra_le 𝔞 A*𝔞 B*sl ha)
      (GaussianExponentialLinearRemainder.original_constant_exponential_linear_remainder c A B p hB ha hc (qnegative_canonical _))
  have eq : Γ ⊢[PRAAx] qsub g qone ≐ c :=
    qadd_sub_cancel qone c (qnegative_canonical _)
  have step₂ : Γ ⊢[PRAAx] distanceBounded g qone A B := bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) hc
  have near : Γ ⊢[PRAAx] distanceBounded v qone (two*A) B :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hB step₁ step₂)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (mul_comm _ _)
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hP hB step₀ near)

private theorem row_unit_bound (s : Bool) (p A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hC : Γ ⊢[PRAAx] le A (C*B)) :
    Γ ⊢[PRAAx] bounded (row p (coefficient A B (polarity s)) (C*one) one one) two one := by
  let c := coefficient A B (polarity s)
  have h : Γ ⊢[PRAAx] GaussianBinetExponentialPanel.nonpositive c := by
    have eq := exponent_at_unit (Γ := Γ) c (qnegative_canonical _)
    have left := congrFst eq
    exact (RationalArgmin.rationalLE_congr left (.eqRefl _)
      (exponent_nonpositive A B (polarity s) one one hB (le_refl one)))
  exact bound_congr (direct_sample s p A B C).eqSymm (.eqRefl _) (.eqRefl _)
    (unit_bound p c (C*one) (unit_input s A B C hB hC) h)

theorem pair_bound (p A B C : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hC : Γ ⊢[PRAAx] le A (C*B)) : Γ ⊢[PRAAx]
    bounded (pairDifference p A B C) (num 4*A*unit p+num 4*B) (B*unit p) := by
  let P := unit p
  let x := row p (coefficient A B (polarity true)) (C*one) one one
  let y := row p (coefficient A B (polarity false)) (C*one) one one
  let K := two*A*P+two*B
  let H := B*P
  have hP := unit_positive (Γ := Γ) p
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ hB hP
  refine .orE (le_total A B) ?_ ?_
  · have pos := linear_sample_bound true p A B C hB.wk hC.wk Prf.hyp0
    have neg := linear_sample_bound false p A B C hB.wk hC.wk Prf.hyp0
    exact bound_congr (.eqRefl _) (by dsimp only [K,P]; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ K K H hH.wk pos (distance_symmetric _ _ _ _ hH.wk neg))
  · let Δ := le B A :: Γ
    have pos := row_unit_bound true p A B C hB.wk hC.wk (Γ := Δ)
    have neg := row_unit_bound false p A B C hB.wk hC.wk (Γ := Δ)
    have raw : Δ ⊢[PRAAx] bounded (qsub x y) (num 4) one :=
      bound_congr (.eqRefl _) (by ipra_ring) (one_mul one)
        (bounded_sum x (qnegative y) two one two one (le_refl one) (le_refl one) pos
          (bounded_negative _ _ _ (le_refl one) neg))
    have hBA : Δ ⊢[PRAAx] le B A := Prf.hyp0
    have larger : Δ ⊢[PRAAx] le (num 4*H) ((num 4*A*P+num 4*B)*one) := by
      dsimp only [H,P]
      ipra_le 4*𝔞(unit p)*sl hBA+4*𝔞 B
    exact bounded_radius_mono _ _ _ _ _ (le_refl one) hH.wk larger raw

private theorem multiplier_bound_exact (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (multiplier A B) B A := by
  have inv := inverse_bound _ _ _ hA hB (GaussianBinetSineDampedTransform.coefficient_lower A B hB)
  have h₂ := le_succ_self (Γ := Γ) one
  have half := GaussianEulerExponentCompactBounds.fraction_bound one two one h₂
    (le_congr (.eqRefl _) (one_mul two).eqSymm h₂)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ B A one one hA (le_refl one) inv half)

theorem quotient_bound (p a b C A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) (hC : Γ ⊢[PRAAx] le (a*A) (C*(b*B))) : Γ ⊢[PRAAx]
    bounded (quotient p a b C A B) (num 4*(a*A)*unit p+num 4*(b*B)) ((A*b)*unit p) := by
  let P := unit p
  let E := num 4*(a*A)*P+num 4*(b*B)
  let H := (b*B)*P
  have hP := unit_positive (Γ := Γ) p
  have h := positive_product _ _ hb hB
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ h hP
  have right : Γ ⊢[PRAAx] le one ((A*b)*P) := positive_product _ _ (positive_product _ _ hA hb) hP
  have raw := bounded_product (multiplier A B) (pairDifference p (a*A) (b*B) C) B A E H hA hH
    (multiplier_bound_exact A B hA hB) (pair_bound p (a*A) (b*B) C h hC)
  have eq : Γ ⊢[PRAAx] qmul (multiplier A B) (pairDifference p (a*A) (b*B) C) ≐ quotient p a b C A B :=
    qmul_associative _ _ _
  exact bounded_radius_mono _ _ _ E ((A*b)*P) (positive_product _ _ hA hH) right
    (le_of_eq_add (d := zero) (by dsimp only [H]; ipra_ring)) (bound_congr eq (.eqRefl _) (.eqRefl _) raw)

theorem clocked_mesh_bound (p a b C T j N : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hT : Γ ⊢[PRAAx] le one T) (hj : Γ ⊢[PRAAx] le one j) (hN : Γ ⊢[PRAAx] le one N)
    (hC : Γ ⊢[PRAAx] le (a*(T*j)) (C*(b*N))) : Γ ⊢[PRAAx]
    bounded (quotient (p+N) a b C (T*j) N) (num 4*a*unit p+num 4*b) (b*unit p) := by
  let A := T*j
  let P := unit p
  let Q := unit (p+N)
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) (p+N)
  have hA : Γ ⊢[PRAAx] le one A := positive_product _ _ hT hj
  have grow : Γ ⊢[PRAAx] le (N*P) Q :=
    le_congr (.eqRefl _) ((mul_comm (unit N) P).eqTrans (pw_add two p N).eqSymm)
      (mul_le_mul_right P (le_trans (le_succ_self N) (RationalClosure.succ_le_two_pow N)))
  have big : Γ ⊢[PRAAx] le (N*P) (A*Q) :=
    le_trans grow (le_congr (one_mul Q) (.eqRefl _) (mul_le_mul_right Q hA))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hA hb) hQ)
    (positive_product _ _ hb hP)
    (by dsimp only [A,P,Q] at *; ipra_le 4*𝔞 b*𝔞 b*sl big)
    (quotient_bound (p+N) a b C A N hA hN hb hC)

end LeanProofs.IPRA.Analysis.GaussianBinetSineQuotientMajorant
