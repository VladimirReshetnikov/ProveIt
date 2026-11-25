import IPRADerivations.Analysis.GaussianBinetLaplaceMomentFrozenRows
import IPRADerivations.Analysis.GaussianBinetLaplaceMomentDecay
import IPRADerivations.Analysis.GaussianNamedRealOrderTransport
import IPRADerivations.Analysis.GaussianPositiveScalarProductBound
import IPRADerivations.Analysis.RationalConvexEndpointBudget
import IPRADerivations.Analysis.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsOrder

/-!
# Uniform positive-margin domination of the Binet moment rows

Compare the two actual real decays at X/D and the fixed lower
chart 1/K. The frozen positive observations share the same
weighted Binet kernel. The existing inverse-square bound at the
fixed chart then controls the original row independently of D.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceDomination (realDecay)
open GaussianBinetLaplaceIntegrand (input)
open GaussianBinetLaplaceMomentDecay (tailScale)
open GaussianBinetLaplaceMomentFloor (observation)
open GaussianBinetLaplaceMomentFrozenRows (frozen frozen_error weightedKernel weighted_kernel_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_bounded)
open GaussianEulerDecayOrder (signedTime)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianPositiveRealArithmetic (positive positive_add)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul qzero qmul_canonical qadd_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_canonical sample_nonnegative)
open GaussianReconstructionRoots (norm_from_distance distance_zero_iff)
open RationalValueBounds (upper upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def allowance (j T : PTm n) : PTm n := num 4+num 26*pw T j

@[simp] theorem subst_allowance {m : ℕ} (σ : Fin n → PTm m) (j T : PTm n) :
    Syn.subst σ (allowance j T) = allowance (Syn.subst σ j) (Syn.subst σ T) := by
  simp [allowance]

theorem fixed_source (K : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] realSource one zero K zero (GaussianLogGammaEulerResidualRadius.radius one zero) :=
  GaussianLogGammaEulerResidualRadius.source_of_right_half_plane one zero K zero
    (.andI (.andI (le_refl one) (.orI₁ (.eqRefl zero))) hK)

theorem positive_decay_order_at (p a b c d : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (hc : Γ ⊢[PRAAx] le (a*d) (c*b)) :
    Γ ⊢[PRAAx] upper (fstT (realDecay p c d)) (fstT (realDecay p a b)) two (unit p) := by
  have left := GaussianEulerDecayOrder.original_decay_nonnegative_representative c d hd
  have right := GaussianEulerDecayOrder.original_decay_nonnegative_representative a b hb
  have h := GaussianNamedRealOrderTransport.transport_at positiveF decayF decayF positiveF
    (positiveData (signedTime c d)) (decayData c d) (decayData a b) (positiveData (signedTime a b)) p p
    left (GaussianNameEquivalence.cross_symm _ _ _ _ right)
    (GaussianEulerDecayOrder.original_decay_order a b c d hb hd hc)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) h
    (le_of_eq_add (d := zero) (by ipra_ring))

private theorem buffered_product (p j X D K T A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hK : Γ ⊢[PRAAx] le one K) (hB : Γ ⊢[PRAAx] le one B)
    (hT : Γ ⊢[PRAAx] le A (T*B)) (hmargin : Γ ⊢[PRAAx] le D (K*X))
    (N E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (href : Γ ⊢[PRAAx] bounded (frozen p j one K A B) N E) :
    Γ ⊢[PRAAx] bounded (frozen p j X D A B)
      ((two*pw T j)*E+N*unit p) (unit p*E) := by
  let x := realDecay p (X*A) (D*B)
  let y := realDecay p (one*A) (K*B)
  let w := weightedKernel p j A B
  let u := radiusPoint two (unit p)
  let v := qadd y u
  have hp := unit_positive (Γ := Γ) p
  have order : Γ ⊢[PRAAx] upper (fstT x) (fstT y) two (unit p) :=
    positive_decay_order_at p _ _ _ _ (positive_product _ _ hK hB) (positive_product _ _ hD hB)
      (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono hmargin (le_refl (A*B))))
  have uy : Γ ⊢[PRAAx] fstT u ≐ GaussianEuclideanDistanceName.fraction two (unit p) :=
    (congrFst (GaussianEulerDecayFactorBounds.fraction_is_radius_point two (unit p) hp)).eqSymm.eqTrans
      (GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part two (unit p) hp)
  have read : Γ ⊢[PRAAx] fstT v ≐ RationalArithmetic.add (fstT y) (GaussianEuclideanDistanceName.fraction two (unit p)) :=
    (RationalGaussianRealPart.real_add y u).eqTrans (RationalAlgebra.add_congr (.eqRefl _) uy)
  have step := RationalArgmin.rationalLE_congr (.eqRefl _) read.eqSymm
    (RationalConvexEndpointBudget.order_of_upper _ _ two (unit p) hp order)
  have hY := sample_nonnegative (Γ := Γ) (signedTime (one*A) (K*B)) p
  have hX := sample_nonnegative (Γ := Γ) (signedTime (X*A) (D*B)) p
  have hU := GaussianPositiveExponentialTermBound.actual_positive_fraction two (unit p) hp
  have hV := positive_add y u hY hU
  have uyDist : Γ ⊢[PRAAx] distanceBounded v y two (unit p) := by
    have raw := GaussianNameArithmetic.sum_distance y y u qzero zero two (unit p) hp
      (GaussianRationalPowerDifference.distance_refl_zero y _ hp)
      ((distance_zero_iff _ _ _ hp).iffMpr (radius_bounded two (unit p) hp))
    exact distance_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_zero_right y (sample_canonical _ _))
      (zero_add _) (.eqRefl _) raw
  have product := GaussianApproximateInverseDistance.multiply_distance w v y (pw T j) two (unit p) hp
    (weighted_kernel_bound p j A B T hB hT) uyDist
  have lower : Γ ⊢[PRAAx] bounded (qmul w y) N E :=
    bound_congr (GaussianRationalPowerAlgebra.qmul_commutative y w) (.eqRefl _) (.eqRefl _) href
  have candidate := norm_from_distance _ _ _ _ _ _ hp hE product lower
  have mono := GaussianPositiveScalarProductBound.product_bound_monotone w x v _ _ (positive_product _ _ hp hE)
    (sample_canonical _ _) (qadd_canonical _ _) hX hV.andE₁ step candidate
  exact bound_congr (GaussianRationalPowerAlgebra.qmul_commutative w x) (by ipra_ring) (.eqRefl _) mono

theorem observation_inverse_square_bound (p j X D R K T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (hK : Γ ⊢[PRAAx] le one K)
    (hmargin : Γ ⊢[PRAAx] le D (K*X)) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    bounded (observation p j X D R T A B)
      (allowance j T*(A*A)+(tailScale j K*(B*B))*unit p) (unit p*(A*A)) := by
  let S : PTm n := GaussianLogGammaEulerResidualRadius.radius one zero
  let y := observation p j one K S T A B
  let v := frozen p j one K A B
  let w := frozen p j X D A B
  let U := unit p
  let E := A*A
  let N := tailScale j K*(B*B)
  let J := pw T j
  have hp := unit_positive (Γ := Γ) p
  have hE := positive_product _ _ hA hA
  have hUE := positive_product _ _ hp hE
  have ref : Γ ⊢[PRAAx] input one zero K zero S T A B := .andI (fixed_source K hK) h.andE₂
  have base : Γ ⊢[PRAAx] bounded y (num 4*E+N*U) (U*E) :=
    GaussianBinetLaplaceMomentDecay.observation_inverse_square_bound p j one K S T A B ref hA
  have tail := frozen_error p j one K S T A B ref
  have lo : Γ ⊢[PRAAx] bounded v ((num 4+num 12*J)*E+N*U) (U*E) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp hUE) hUE
      (le_of_eq_add (d := zero) (by dsimp only [E,N,U,J]; ipra_ring))
      (norm_from_distance v y _ _ _ _ hp hUE (distance_symmetric _ _ _ _ hp tail) base)
  have middle := buffered_product p j X D K T A B h.andE₁.andE₁.andE₂ hK h.andE₂.andE₁ h.andE₂.andE₂ hmargin
    _ _ hUE lo
  have up : Γ ⊢[PRAAx] bounded w ((num 4+num 14*J)*E+N*U) (U*E) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp hUE) hUE
      (le_of_eq_add (d := zero) (by dsimp only [E,N,U,J]; ipra_ring)) middle
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp hUE) hUE
    (le_of_eq_add (d := zero) (by dsimp only [allowance,E,N,U,J]; ipra_ring))
    (norm_from_distance _ w _ _ _ _ hp hUE (frozen_error p j X D R T A B h) up)

theorem actual_weighted_Binet_margin_inverse_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let j := var 1
     let X := var 2
     let D := var 3
     let R := var 4
     let K := var 5
     let T := var 6
     let A := var 7
     let B := var 8
     input X zero D zero R T A B ⟶ (le one K ⋏ (le D (K*X) ⋏ le one A)) ⟶
        bounded (observation p j X D R T A B)
          (allowance j T*(A*A)+(tailScale j K*(B*B))*unit p) (unit p*(A*A))) :=
  closeUniv 9 (.impI (.impI (observation_inverse_square_bound _ _ _ _ _ _ _ _ _ Prf.hyp1
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginRows
