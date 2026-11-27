import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.FiniteRows.GaussianBinetLaplaceMomentCompact
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Integrands.GaussianBinetLaplaceRealFloor
import IPRADerivations.Analysis.Euler.Integration.Decay.Increments.GaussianEulerDecayGlobalIncrement
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedAxis

/-!
# A common positive decay and kernel read for the original Binet moment rows

The exact time power is unchanged. Only the two named factors are
read at a common precision. Consecutive frozen rows differ by
multiplication by the exact time, and their nonnegative real
coordinates supply the rational majorants for the Taylor remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentFrozenRows

open_ipra
open GaussianBinetKernelRows (inputData)
open GaussianBinetLaplaceDomination (realDecay realNumerator realDenominator complexClock clock_later nonnegative_real_radius)
open GaussianBinetLaplaceIntegrand (input product_at)
open GaussianBinetLaplaceMomentCompact (weight_bound)
open GaussianBinetLaplaceMomentFloor (weight clock observation)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_congr radius_multiply)
open GaussianEulerDecayGlobalIncrement (positive_observation_distance positive_observation_bound)
open GaussianNameEquivalence (point_at)
open GaussianPositiveRealArithmetic (positive positive_multiply natural_representation)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open ComplexLogarithmRemainder (normSq normSq_code)
open RationalGaussianEmbedding (native embed_from_representation canonical_axis_roundtrip)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "ExpF" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data

def weightedKernel (p j A B : PTm n) : PTm n :=
  qmul (ap2 K p (inputData A B)) (weight j A B)

def frozen (p j X D A B : PTm n) : PTm n :=
  qmul (realDecay p (X*A) (D*B)) (weightedKernel p j A B)

ipra_subst weightedKernel

ipra_subst frozen [realDecay, GaussianEulerDecayOrder.signedTime]

theorem kernel_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 K p (inputData A B)) one one :=
  bounded_radius_mono _ one (num 4) one one (by ipra_le 3) (le_refl one) (by ipra_le 3)
    (GaussianBinetKernelCoarseBound.cofinal_at p A B hB)

theorem weighted_kernel_bound (p j A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] bounded (weightedKernel p j A B) (pw T j) one :=
  bound_congr (.eqRefl _) (one_mul _) (one_mul _)
    (bounded_product _ _ one one _ one (le_refl one) (le_refl one) (kernel_bound p A B hB) (weight_bound j A B T hB hT))

theorem frozen_bound (p j X D A B T : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] bounded (frozen p j X D A B) (num 4*pw T j) one :=
  bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (bounded_product _ _ _ one _ one (le_refl one) (le_refl one)
      (positive_observation_bound p (X*A) (D*B) (positive_product _ _ hD hB))
      (weighted_kernel_bound p j A B T hB hT))

theorem frozen_positive (p j X D A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] positive (frozen p j X D A B) :=
  positive_multiply _ _
    (GaussianRealExponentialPositiveRepresentative.sample_nonnegative (GaussianEulerDecayOrder.signedTime (X*A) (D*B)) p)
    (positive_multiply _ _ (GaussianBinetLaplaceRealFloor.cofinal_kernel_floor p A B T hB hT).andE₁
      (GaussianPositiveExponentialTermBound.actual_positive_fraction (pw A j) (pw B j)
        (GaussianPolynomialPerturbation.power_positive B j hB)))

private theorem read_earlier (z w s p : PTm n) (hle : Γ ⊢[PRAAx] le p s)
    (h : Γ ⊢[PRAAx] distanceBounded z w (unit s+unit p) (unit s*unit p)) :
    Γ ⊢[PRAAx] distanceBounded z w two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have hb := GaussianExponentialReference.unit_monotone hle
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs hp) hp
    (by ipra_le 𝔞(unit p)*sl hb) h

theorem frozen_error (p j X D R T A B : PTm n) (h : Γ ⊢[PRAAx] input X zero D zero R T A B) :
    Γ ⊢[PRAAx] distanceBounded (observation p j X D R T A B) (frozen p j X D A B)
      (num 12*pw T j) (unit p) := by
  let r := clock p j T
  let s := complexClock r X zero D zero R T A B
  let a := ap2 ExpF s (expData X zero D zero R T A B)
  let b := realDecay p (X*A) (D*B)
  let k := ap2 K s (inputData A B)
  let l := ap2 K p (inputData A B)
  let w := weight j A B
  have hp := unit_positive (Γ := Γ) p
  have hb := h.andE₂.andE₁
  have ht := h.andE₂.andE₂
  have den := positive_product _ _ h.andE₁.andE₁.andE₂ hb
  have later : Γ ⊢[PRAAx] le p s := le_trans (le_add_right _ _) (clock_later r X zero D zero R T A B)
  have expError := read_earlier _ _ s p later
    (GaussianBinetSineDampedAxis.same_observation s p X D A B R T h.andE₁ hb ht)
  have decayError := distance_symmetric _ _ _ _ hp (positive_observation_distance p (X*A) (D*B) den)
  have expNear : Γ ⊢[PRAAx] distanceBounded a b (num 4) (unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hp expError decayError)
  have kernelNear : Γ ⊢[PRAAx] distanceBounded k l two (unit p) :=
    read_earlier _ _ s p later (point_at K (inputData A B) s p (GaussianBinetKernelCofinal.regular A B hb))
  have product := GaussianNameArithmetic.product_distance a b k l (num 4) two (unit p) one (num 4) hp
    expNear kernelNear (kernel_bound s A B hb) (positive_observation_bound p (X*A) (D*B) den)
  have dist : Γ ⊢[PRAAx] distanceBounded (qmul a k) (qmul b l) (num 12) (unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) product
  have scale := GaussianApproximateInverseDistance.multiply_distance w (qmul a k) (qmul b l) (pw T j) (num 12)
    (unit p) hp (weight_bound j A B T hb ht) dist
  have orig : Γ ⊢[PRAAx] observation p j X D R T A B ≐ qmul (qmul a k) w :=
    qmul_congr (product_at K r _ _) (.eqRefl _)
  exact distance_congr ((qmul_commutative w (qmul a k)).eqTrans orig.eqSymm)
    ((qmul_commutative w (qmul b l)).eqTrans (qmul_associative b l w)) (by ipra_ring) (.eqRefl _) scale

theorem weight_succ (j A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] weight (succ j) A B ≐ qmul (weight j A B) (radiusPoint A B) :=
  (radius_congr (pw_succ A j) (pw_succ B j)).eqTrans
    (radius_multiply _ _ _ _ (GaussianPolynomialPerturbation.power_positive B j hB) hB).eqSymm

theorem frozen_succ (p j X D A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] frozen p (succ j) X D A B ≐ qmul (frozen p j X D A B) (radiusPoint A B) := by
  let a := realDecay p (X*A) (D*B)
  let k := ap2 K p (inputData A B)
  let w := weight j A B
  let t := radiusPoint A B
  exact (qmul_congr (.eqRefl a) ((qmul_congr (.eqRefl k) (weight_succ j A B hB)).eqTrans
    (qmul_associative k w t).eqSymm)).eqTrans (qmul_associative a (qmul k w) t).eqSymm

theorem exact_frozen_bound (p j X D A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    let z := frozen p j X D A B
    Γ ⊢[PRAAx] bounded z (realNumerator z) (realDenominator z) := by
  let z := frozen p j X D A B
  have hE := RationalArgmin.denominator_positive (Γ := Γ) (fstT z)
  exact nonnegative_real_radius z _ _ (frozen_positive p j X D A B T hB hT) (qmul_canonical _ _) hE (le_congr (mul_comm _ _) (.eqRefl _) (le_refl _))

theorem frozen_numerator_bound (p j X D A B T : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    let z := frozen p j X D A B
    Γ ⊢[PRAAx] le (realNumerator z) ((num 4*pw T j)*realDenominator z) := by
  let z := frozen p j X D A B
  let e := realDenominator z
  let a := realNumerator z
  let c := native (ZT.ofNat a)
  have hE : Γ ⊢[PRAAx] le one e := RationalArgmin.denominator_positive _
  have hp := frozen_positive p j X D A B T hB hT
  have value := embed_from_representation (fstT z) (ZT.ofNat a) e (natural_representation _ hp.andE₂)
  have rep := GaussianRationalHorner.represents_congr (canonical_axis_roundtrip z (qmul_canonical _ _) hp.andE₁)
    (GaussianRootAlgebra.equal_refl c) (.eqRefl e) value
  have cnorm : Γ ⊢[PRAAx] normSq c ≐ a*a := by
    apply deriveNat
    simp only [c,native,normSq_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  have raw := GaussianRationalMetric.bounded_to_cleared z c e _ one hE (le_refl one) rep
    (frozen_bound p j X D A B T hD hB hT)
  exact nat_sqrt_mono (le_congr ((congrMul (.eqRefl _) cnorm).eqTrans (by ipra_ring)) (by ipra_ring) raw)

theorem frozen_higher_representation (p j X D A B T : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    let z := frozen p j X D A B
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (frozen p (succ (succ j)) X D A B))
      (ZT.ofNat (realNumerator z*(A*A))) (realDenominator z*(B*B)) := by
  let z := frozen p j X D A B
  let t := radiusPoint A B
  let c := radiusPoint (A*A) (B*B)
  have same : Γ ⊢[PRAAx] frozen p (succ (succ j)) X D A B ≐ qmul z c :=
    (frozen_succ p (succ j) X D A B hB).eqTrans
      ((qmul_congr (frozen_succ p j X D A B hB) (.eqRefl t)).eqTrans
        ((qmul_associative z t t).eqTrans (qmul_congr (.eqRefl z) (radius_multiply A B A B hB hB))))
  have hb := positive_product _ _ hB hB
  have rp := GaussianPositiveExponentialOrder.radius_real_representation (A*A) (B*B) hb
  have old := natural_representation (fstT z) (frozen_positive p j X D A B T hB hT).andE₂
  have repr := RationalRepresentations.represents_multiply _ _ _ _ _ _ old rp
  have out := (congrFst same).eqTrans (GaussianPositiveExponentialProduct.real_product z c
    (GaussianPositiveExponentialTermBound.actual_positive_fraction _ _ hb).andE₁)
  apply GaussianRationalHorner.scalar_congr out.eqSymm _ (.eqRefl _) repr
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul,realNumerator,z]

theorem actual_Binet_weighted_frozen_row_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 2) zero (var 3) zero (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (frozen (var 0) (var 1) (var 2) (var 3) (var 6) (var 7))
        (num 12*pw (var 5) (var 1)) (unit (var 0))) :=
  closeUniv 8 (.impI (frozen_error _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentFrozenRows
