import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentImproperTaylor
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerWeightedHalfDecay
import IPRADerivations.Analysis.Integration.Moments.GaussianMomentReflection

/-!
# Actual punctured forward quotients of the improper Binet moment names

Dividing the improper right Taylor bound by the exact positive
increment gives a linear convergence rate. The normalized divided
difference and negative successor moment are the original named
programs. Rational slack removal leaves independent observation
clocks and the exact leading radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentForwardQuotient

open_ipra
open GaussianBinetLaplaceMomentImproper (nameF data regular sample_canonical)
open GaussianBinetLaplaceMomentImproperTaylor (higherBound leading linearSample)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusNumerator radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianNamedDifferenceQuotient (separated inverse)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul qzero positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative qadd_commutative qadd_zero_right qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def quotientF : PR 2 := GaussianNamedDifferenceQuotient.nameF nameF nameF
def targetF : PR 2 := negativeF nameF

def quotientData (j X D R S H Q : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data nameF nameF
    (data j (X*Q+H*D) (D*Q) S) (data j X D R) (radiusNumerator H) Q

def targetData (j X D R : PTm n) : PTm n := negativeData (data (succ j) X D R)

def linearBudget (j D H : PTm n) : PTm n := num 3*H*higherBound j D

def samplerBudget (j X D R S H Q : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.cost nameF nameF
    (data j (X*Q+H*D) (D*Q) S) (data j X D R) (radiusNumerator H) Q + num 10*Q + num 3

ipra_subst quotientData

ipra_subst targetData

ipra_subst linearBudget

ipra_subst samplerBudget

theorem positive_parameter (H Q : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx] separated (radiusNumerator H) Q :=
  .andI hQ (le_congr (.eqRefl _) (GaussianDominantPairAlgebra.radius_numerator_norm H).eqSymm
    (positive_product _ _ hH hH))

private theorem inverse_radius (H Q : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx] inverse (radiusNumerator H) Q ≐ radiusPoint Q H := by
  let v := inverse (radiusNumerator H) Q
  let c := radiusPoint H Q
  let w := radiusPoint Q H
  have e : Γ ⊢[PRAAx] qmul v c ≐ qone :=
    GaussianNamedDifferenceQuotient.actual_inverse _ _ (positive_parameter H Q hH hQ)
  have f : Γ ⊢[PRAAx] qmul c w ≐ qone :=
    (GaussianRationalPowerAlgebra.qmul_commutative c w).eqTrans (GaussianEulerWeightedHalfDecay.radius_reciprocal H Q hH hQ)
  exact (qmul_one_right v (GaussianRationalReciprocal.reciprocal_canonical _)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl v) f.eqSymm).eqTrans
      ((qmul_associative v c w).eqSymm.eqTrans
        ((qmul_congr e (.eqRefl w)).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative qone w).eqTrans
            (qmul_one_right w (GaussianRationalHorner.ofGaussian_canonical _ _ hH))))))

private theorem sub_translated (x a : PTm n) : Γ ⊢[PRAAx] qsub (qsub x a) x ≐ qnegative a := by
  change Γ ⊢[PRAAx] qadd (qadd x (qnegative a)) (qnegative x) ≐ qnegative a
  exact (qadd_congr (qadd_commutative x (qnegative a)) (.eqRefl _)).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self x)).eqTrans
        (qadd_zero_right _ (qnegative_canonical a))))

private theorem normalized_negation (z : PTm n) : Γ ⊢[PRAAx] qsub qzero z ≐ qnegative z :=
  (qadd_commutative qzero (qnegative z)).eqTrans (qadd_zero_right _ (qnegative_canonical z))

private theorem linear_quotient (x z H Q : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRationalHorner.canonical z)
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    qmul (inverse (radiusNumerator H) Q) (qsub (qsub x (qmul (radiusPoint H Q) z)) x) ≐ qsub qzero z := by
  let c := radiusPoint H Q
  let v := inverse (radiusNumerator H) Q
  have e : Γ ⊢[PRAAx] qmul v c ≐ qone :=
    GaussianNamedDifferenceQuotient.actual_inverse _ _ (positive_parameter H Q hH hQ)
  have cancel : Γ ⊢[PRAAx] qmul v (qmul c z) ≐ z := (qmul_associative v c z).eqSymm.eqTrans
    ((qmul_congr e (.eqRefl z)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone z).eqTrans (qmul_one_right z hz)))
  exact (qmul_congr (.eqRefl v) (sub_translated x (qmul c z))).eqTrans
    ((GaussianMomentReflection.negative_right_product v _).eqTrans
      ((normalized_negation _).eqSymm.eqTrans (qsub_congr (.eqRefl qzero) cancel)))

private theorem cofinal_inputs (j X D R S H Q : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero S)
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    GaussianNamedDifferenceQuotient.input nameF nameF (data j (X*Q+H*D) (D*Q) S) (data j X D R) (radiusNumerator H) Q :=
  .andI (regular _ _ _ _ h') (.andI (regular _ _ _ _ h) (positive_parameter H Q hH hQ))

theorem quotient_regular (j X D R S H Q : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero S)
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] pointCN quotientF (quotientData j X D R S H Q) :=
  GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (cofinal_inputs j X D R S H Q h h' hH hQ)

private theorem scale_observation {a b C Q p : PTm n} (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded a b C (unit p)) : Γ ⊢[PRAAx] distanceBounded a b (C*Q) (Q*unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ hQ (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) h

/-- Transfer a sampled Taylor estimate to the original named quotient.
The target may be any original moment observation, including the
successor read in a fixed base chart. -/
theorem sample_of_taylor (p a b c H Q C L : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input nameF nameF a b (radiusNumerator H) Q)
    (hz : Γ ⊢[PRAAx] pointCN nameF c) (hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p c))
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q)
    (taylor : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p a)
      (qsub (ap2 nameF p b) (qmul (radiusPoint H Q) (ap2 nameF p c)))
      (num 3*(H*H)*C*unit p+L*(Q*Q)) ((Q*Q)*unit p)) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 quotientF p (GaussianNamedDifferenceQuotient.data nameF nameF a b (radiusNumerator H) Q))
      (ap2 targetF p (negativeData c))
      (diagonalNumerator (num 3*H*C) Q
        (GaussianNamedDifferenceQuotient.cost nameF nameF a b (radiusNumerator H) Q + L*Q + num 3) p)
      (diagonalDenominator Q p) := by
  let y := ap2 nameF p a
  let x := ap2 nameF p b
  let z := ap2 nameF p c
  let v := inverse (radiusNumerator H) Q
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ hQ hp
  have den₂ := positive_product _ _ (positive_product _ _ hQ hQ) hp
  have translated : Γ ⊢[PRAAx] distanceBounded (qsub y x) (qsub (qsub x (qmul (radiusPoint H Q) z)) x)
      (num 3*(H*H)*C*unit p+L*(Q*Q)) ((Q*Q)*unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
      (GaussianNamedDifference.difference_distance _ _ x x _ zero _ den₂ taylor
        (GaussianRationalPowerDifference.distance_refl_zero x _ den₂))
  have bounded_inv : Γ ⊢[PRAAx] bounded v Q H :=
    bound_congr (inverse_radius H Q hH hQ).eqSymm (.eqRefl _) (.eqRefl _) (radius_bounded Q H hH)
  have scaled := bound_congr
    (GaussianRationalRoundedPower.multiplication_difference v (qsub y x) (qsub (qsub x (qmul (radiusPoint H Q) z)) x)).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianRationalReciprocal.bounded_product _ _ Q H _ _ hH den₂ bounded_inv translated)
  have raw := distance_congr (.eqRefl _)
    (linear_quotient x z H Q hc hH hQ) (.eqRefl _) (.eqRefl _) scaled
  have ideal : Γ ⊢[PRAAx] distanceBounded (qmul v (qsub y x)) (qsub qzero z)
      (num 3*H*C*unit p+(L*Q)*Q) (Q*unit p) := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hH den₂) den ?_ raw
    ipra_le 𝔞(L)*𝔞(Q)*𝔞(Q)*𝔞(Q)*𝔞(Q)*𝔞(unit p)*sl hH
  have observed := scale_observation hQ (GaussianNamedDifferenceQuotient.sample_error nameF nameF p a b _ _ hInput)
  have reflected := GaussianNameRingLaws.negative_sample_error nameF c p hz
  have reflected' := scale_observation hQ (distance_symmetric _ _ _ _ hp reflected)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator GaussianNameRingLaws.three; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ den (distance_triangle_same _ _ _ _ _ _ den observed ideal) reflected')

theorem quotient_sample (p j X D R S H Q : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero S)
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q) (hh : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData j X D R S H Q)) (ap2 targetF p (targetData j X D R))
      (diagonalNumerator (linearBudget j D H) Q (samplerBudget j X D R S H Q) p) (diagonalDenominator Q p) := by
  exact sample_of_taylor p _ _ _ H Q (higherBound j D) (num 10) (cofinal_inputs j X D R S H Q h h' hH hQ)
    (regular (succ j) X D R h) (sample_canonical p (succ j) X D R) hH hQ
    (GaussianBinetLaplaceMomentImproperTaylor.observation_taylor p j X D R S H Q h h' hQ hh)

theorem forward_rate (j X D R S H Q : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero S)
    (hH : Γ ⊢[PRAAx] le one H) (hQ : Γ ⊢[PRAAx] le one Q) (hh : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] independentRate quotientF targetF (quotientData j X D R S H Q) (targetData j X D R)
      (linearBudget j D H) Q := by
  apply GaussianNamedLipschitzRate.independent_rate quotientF targetF (quotientData j X D R S H Q) (targetData j X D R)
    (linearBudget j D H) Q (samplerBudget j X D R S H Q) hQ
    (quotient_regular j X D R S H Q h h' hH hQ) (negative_fast _ _ (regular (succ j) X D R h))
  refine .allI ?_
  let s (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have base : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift
  have moved : Δ ⊢[PRAAx] realSource (s X*s Q+s H*s D) zero (s D*s Q) zero (s S) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,ConciseIPRA.PTm.subst_zero,
      PTm.subst_add,PTm.subst_mul] using h'.shift
  have ph : Δ ⊢[PRAAx] le one (s H) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hH.shift
  have pq : Δ ⊢[PRAAx] le one (s Q) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hQ.shift
  have step : Δ ⊢[PRAAx] le (s H) (s Q) := by simpa [Δ,s,Fm.shift,Syn.shift] using hh.shift
  change Δ ⊢[PRAAx] distanceBounded (ap2 quotientF (var 0) (Syn.shift (quotientData j X D R S H Q)))
    (ap2 targetF (var 0) (Syn.shift (targetData j X D R)))
    (diagonalNumerator (Syn.shift (linearBudget j D H)) (s Q) (Syn.shift (samplerBudget j X D R S H Q)) (var 0))
    (diagonalDenominator (s Q) (var 0))
  rw [show Syn.shift (quotientData j X D R S H Q) = quotientData (s j) (s X) (s D) (s R) (s S) (s H) (s Q)
        from subst_quotientData _ _ _ _ _ _ _ _,
      show Syn.shift (targetData j X D R) = targetData (s j) (s X) (s D) (s R) from subst_targetData _ _ _ _ _,
      show Syn.shift (linearBudget j D H) = linearBudget (s j) (s D) (s H) from subst_linearBudget _ _ _ _,
      show Syn.shift (samplerBudget j X D R S H Q) = samplerBudget (s j) (s X) (s D) (s R) (s S) (s H) (s Q)
        from subst_samplerBudget _ _ _ _ _ _ _ _]
  exact quotient_sample (var 0) (s j) (s X) (s D) (s R) (s S) (s H) (s Q) base moved ph pq step

theorem actual_improper_Binet_moment_forward_quotient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let j := var 0
     let X := var 1
     let D := var 2
     let R := var 3
     let S := var 4
     let H := var 5
     let Q := var 6
     (realSource X zero D zero R ⋏ realSource (X*Q+H*D) zero (D*Q) zero S) ⟶
       (le one H ⋏ (le one Q ⋏ le H Q)) ⟶
        independentRate quotientF targetF (quotientData j X D R S H Q) (targetData j X D R) (linearBudget j D H) Q) :=
  closeUniv 7 (.impI (.impI (forward_rate _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentForwardQuotient
