import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetWeightedExponentialGrid
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayQuadraturePrecision

/-!
# Weighted exponential integral on the physical unit interval

The literal samples are the left-grid values of `(1/2-u) exp(-a*u/b)`.
The endpoint is the named value of
`b*((a+2*b)*exp(-a/b)-(2*b-a))/(2*a^2)` for positive `a,b`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponential

open_ipra
open GaussianBinetWeightedExponentialAlgebra (inverseScale rightCoefficient leftCoefficient)
open GaussianBinetWeightedExponentialGrid (value endpoint meshCost observationCost rowError)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerDecayMesh (observation)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "productF" => multiplyF constantF decayF
local notation "differenceF" => GaussianNamedDifference.nameF productF constantF

def source (a b : PTm n) : Fm PTm n := le one a ⋏ le one b
def productData (a b : PTm n) : PTm n := multiplyData constantF decayF (rightCoefficient a b) (decayData a b)
def differenceData (a b : PTm n) : PTm n := GaussianNamedDifference.data (productData a b) (leftCoefficient a b)
def endpointF : PR 2 := multiplyF constantF differenceF
def endpointData (a b : PTm n) : PTm n := multiplyData constantF differenceF (inverseScale a b) (differenceData a b)

ipra_subst endpointData [differenceData, productData]

private theorem product_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN productF (productData a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianEulerDecayQuadraturePrecision.observation_regular a b)

private theorem difference_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN differenceF (differenceData a b) :=
  GaussianNamedDifference.name_regular _ _ _ _ (product_regular a b) (constant_regular _)

theorem endpoint_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN endpointF (endpointData a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (difference_regular a b)

private theorem inverse_bound (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] bounded (inverseScale a b) b one := by
  have h : Γ ⊢[PRAAx] le one (two*a*a) := positive_product _ _ (positive_product _ _ (le_succ_self one) ha) ha
  exact GaussianEulerExponentCompactBounds.fraction_bound _ _ _ h
    (le_congr (one_mul b) (mul_comm _ _) (mul_le_mul_right b h))

private theorem right_bound (a b : PTm n) :
    Γ ⊢[PRAAx] bounded (rightCoefficient a b) (a+two*b) one :=
  GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (le_refl one)
    (le_of_eq_add (d := zero) (by ipra_ring))

def productCost (a b : PTm n) : PTm n := multiplyModulus constantF decayF (rightCoefficient a b) (decayData a b)+one
def endpointCost (a b : PTm n) : PTm n :=
  (multiplyModulus constantF differenceF (inverseScale a b) (differenceData a b)+one) +
    b*(num 6+(productCost a b+zero))

theorem endpoint_error (p a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] distanceBounded (ap2 endpointF p (endpointData a b)) (endpoint p a b) (endpointCost a b) (unit p) := by
  let c := rightCoefficient a b
  let d := leftCoefficient a b
  let inv := inverseScale a b
  let x := decayData a b
  have hp := unit_positive (Γ := Γ) p
  have prod : Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData a b))
      (qmul c (observation a b p)) (productCost a b) (unit p) :=
    distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
      (multiply_sample_error _ _ c x p (constant_regular _) (GaussianEulerDecayQuadraturePrecision.observation_regular a b))
  have dz := distance_congr (constant_at (Γ := Γ) p d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero d (unit p) hp)
  have diff := distance_triangle_same _ _ _ _ _ _ hp
    (GaussianNamedDifference.sample_error productF constantF (productData a b) d p (product_regular a b) (constant_regular _))
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp prod dz)
  have mul := distance_congr (Γ := Γ) (.eqRefl _) (qmul_congr (constant_at p inv) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error constantF differenceF inv (differenceData a b) p (constant_regular _) (difference_regular a b))
  exact distance_triangle_same _ _ _ _ _ _ hp mul
    (GaussianApproximateInverseDistance.multiply_distance inv _ _ b _ _ hp (inverse_bound a b ha) diff)

theorem endpoint_later (p q a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (endpoint q a b) (endpoint p a b) (b*((a+two*b)*two+zero)) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have grow := GaussianExponentialReference.unit_monotone hpq
  have near : Γ ⊢[PRAAx] distanceBounded (observation a b q) (observation a b p) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hq hp) hp
      (by ipra_le 𝔞(unit p)*sl grow)
      (point_at decayF (decayData a b) q p (GaussianEulerDecayQuadraturePrecision.observation_regular a b))
  have prod := GaussianApproximateInverseDistance.multiply_distance (rightCoefficient a b) _ _ _ _ _ hp
    (right_bound a b) near
  have diff := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp prod
    (distance_refl_zero (leftCoefficient a b) _ hp)
  exact GaussianApproximateInverseDistance.multiply_distance (inverseScale a b) _ _ b _ _ hp (inverse_bound a b ha) diff

def budget (a b : PTm n) : PTm n :=
  (b*(meshCost a b+observationCost a b)+b*((a+two*b)*two+zero))+endpointCost a b

ipra_subst budget [endpointCost, productCost, differenceData, productData, meshCost, observationCost, GaussianNameRingLaws.three, one, two]

theorem finite_error (p N a b : PTm n) (h : Γ ⊢[PRAAx] source a b)
    (haN : Γ ⊢[PRAAx] le a N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (value (p+N) N a b) (ap2 endpointF p (endpointData a b)) (budget a b) (unit p) := by
  let q := p+N
  let P := unit p
  let Q := unit q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hN := le_trans hp hpN
  have hclock : Γ ⊢[PRAAx] le (N*P) Q := by
    have grow := le_trans (le_succ_self (Γ := Γ) N) (RationalClosure.succ_le_two_pow N)
    exact le_congr (.eqRefl _) ((mul_comm (unit N) P).eqTrans (pw_add two p N).eqSymm) (mul_le_mul_right P grow)
  have est : Γ ⊢[PRAAx] distanceBounded (value q N a b) (endpoint q a b)
      (b*(meshCost a b+observationCost a b)) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN hq) hp
      (by dsimp only [rowError]; ipra_le 𝔞(b)*𝔞(meshCost a b)*𝔞(Q)*sl hpN +
        𝔞(b)*𝔞(observationCost a b)*𝔞(N)*sl hclock)
      (GaussianBinetWeightedExponentialGrid.finite_error q N a b h.andE₁ h.andE₂ hN haN)
  exact distance_triangle_same _ _ _ _ _ _ hp
    (distance_triangle_same _ _ _ _ _ _ hp est (endpoint_later p q a b h.andE₁ (le_add_right _ _)))
    (distance_symmetric _ _ _ _ hp (endpoint_error p a b h.andE₁))

def mesh (p a : PTm n) : PTm n := a+unit p
def rawSample (p a b : PTm n) : PTm n := value (p+mesh p a) (mesh p a) a b
def rawF : PR 2 := PTm.toPR (rawSample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

ipra_subst rawSample [mesh]

theorem raw_at (p a b : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (pairT a b) ≐ rawSample p a b := by
  let x := pairT a b
  have read : Γ ⊢[PRAAx] ap2 rawF p x ≐ rawSample p (fstT x) (sndT x) := by
    simpa only [rawF,ap2,subst_rawSample,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (rawSample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,x]
  exact read.eqTrans (by
    simpa only [subst_rawSample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rawSample (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![p,fstT x,sndT x]) (σ' := ![p,a,b])
        (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _))

theorem raw_error (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p (pairT a b)) (ap2 endpointF p (endpointData a b)) (budget a b) (unit p) :=
  distance_congr (raw_at p a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (finite_error p (mesh p a) a b h (le_add_right _ _) (le_add_left _ _))

private theorem raw_observations (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p (pairT a b)) (ap2 rawF q (pairT a b))
      ((budget a b+one)*(unit p+unit q)) (unit p*unit q) := by
  let K := budget a b
  let P := unit p
  let Q := unit q
  let E := P*Q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hE := positive_product _ _ hp hq
  have l := distance_radius_mono _ _ _ _ (K*Q) E hp hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (raw_error p a b h)
  have r := distance_radius_mono _ _ _ _ (K*P) E hq hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (raw_error q a b h)
  have m := point_at endpointF (endpointData a b) p q (endpoint_regular (Γ := Γ) a b)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [K,P,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE (distance_triangle_same _ _ _ _ _ _ hE l m)
      (distance_symmetric _ _ _ _ hE r))

theorem raw_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF (budget a b+one) (pairT a b) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (s a) (s b) := by
    simpa [Fm.shift,Syn.shift,s,source,one] using h.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,s,subst_budget,subst_pairT,PTm.subst_add,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    raw_observations (var 1) (var 0) (s a) (s b) hs

abbrev nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (a b : PTm n) : PTm n := GaussianFastValueCut.nameData (budget a b+one) (pairT a b)
def clock (p a b : PTm n) : PTm n := GaussianFastValueCut.exponent (budget a b+one) p

ipra_subst data [one]

theorem sample_at (p a b : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data a b) ≐ rawSample (clock p a b) a b :=
  (GaussianFastValueCut.name_at rawF (budget a b+one) (pairT a b) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p a b) a b)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))

theorem regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data a b) :=
  GaussianFastValueCut.name_fast rawF _ _ (raw_regular a b h)

private theorem error_at (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data a b)) (ap2 endpointF p (endpointData a b))
      (budget a b+two) (unit p) := by
  let s := clock p a b
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have grow := GaussianExponentialReference.unit_monotone later
  have raw := distance_congr (sample_at p a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_congr (raw_at s a b) (.eqRefl _) (.eqRefl _) (.eqRefl _) (raw_error s a b h))
  have compare := GaussianExponentialReference.dyadic_weaken _ _ _ p s later raw
  have point := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hs hp) hp
    (by ipra_le 𝔞(unit p)*sl grow) (point_at endpointF (endpointData a b) s p (endpoint_regular a b))
  exact distance_triangle_same _ _ _ _ _ _ hp compare point

theorem equivalent (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF endpointF (data a b) (endpointData a b) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget a b+two)
    (regular a b h) (endpoint_regular a b) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s a) (s b) := by
    simpa [Fm.shift,Syn.shift,s,source,one] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,subst_budget,subst_data,subst_endpointData,
    PTm.subst_add,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using error_at (var 0) (s a) (s b) hs

theorem actual_weighted_exponential_unit_integral_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ pointCN nameF (data (var 0) (var 1)) ⋏
        crossEquivalent nameF endpointF (data (var 0) (var 1)) (endpointData (var 0) (var 1))) :=
  closeUniv 2 (.impI (.andI (regular _ _ Prf.hyp0) (equivalent _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponential
