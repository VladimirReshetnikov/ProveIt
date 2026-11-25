import IPRADerivations.Analysis.GaussianBinetLaplaceMomentFrozenRows
import IPRADerivations.Analysis.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.GaussianNamedDifference

/-!
# Taylor numerator for the consecutive actual weighted Binet rows

At a positive rational base point the real forward increment acts on
the original decay factor. The exact linear term is the next time
moment times the increment. The quadratic term is three times the
squared increment times the nonnegative real coordinate of the
frozen row two orders higher. All original observation errors share
one explicit dyadic allowance.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTaylorRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceDomination (realDecay realNumerator realDenominator)
open GaussianBinetLaplaceIntegrand (input)
open GaussianBinetLaplaceMomentFloor (observation)
open GaussianBinetLaplaceMomentFrozenRows
  (frozen weightedKernel weighted_kernel_bound frozen_error frozen_succ exact_frozen_bound frozen_numerator_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded radius_multiply)
open GaussianEulerIntegrandName (decayPoint)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qadd qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_product bound_congr qone)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "decay" => GaussianEulerDecayMesh.observation

def linearObservation (p j X D R T H Q A B : PTm n) : PTm n :=
  qsub (observation p j X D R T A B)
    (qmul (radiusPoint H Q) (observation p (succ j) X D R T A B))

def allowance (j T : PTm n) : PTm n := num 48*pw T j+num 12*pw T (succ j)

def leadingNumerator (p j X D H A B : PTm n) : PTm n :=
  num 3*(H*H)*(realNumerator (frozen p j X D A B)*(A*A))

def leadingDenominator (p j X D Q A B : PTm n) : PTm n :=
  realDenominator (frozen p j X D A B)*((Q*B)*(Q*B))

@[simp] theorem subst_linearObservation {m : ℕ} (σ : Fin n → PTm m) (p j X D R T H Q A B : PTm n) :
    Syn.subst σ (linearObservation p j X D R T H Q A B) =
      linearObservation (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D)
        (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ Q) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [linearObservation]

@[simp] theorem subst_allowance {m : ℕ} (σ : Fin n → PTm m) (j T : PTm n) :
    Syn.subst σ (allowance j T) = allowance (Syn.subst σ j) (Syn.subst σ T) := by simp [allowance]

@[simp] theorem subst_leadingNumerator {m : ℕ} (σ : Fin n → PTm m) (p j X D H A B : PTm n) :
    Syn.subst σ (leadingNumerator p j X D H A B) =
      leadingNumerator (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D)
        (Syn.subst σ H) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [leadingNumerator,realNumerator,GaussianPositiveRealArithmetic.numerator,RationalSupMetric.numeratorOf]

@[simp] theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (p j X D Q A B : PTm n) :
    Syn.subst σ (leadingDenominator p j X D Q A B) =
      leadingDenominator (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D)
        (Syn.subst σ Q) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [leadingDenominator,realDenominator,RationalSupMetric.denominatorOf]

private theorem frozen_linear (p j X D H Q A B : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) :
    let z := frozen p j X D A B
    Γ ⊢[PRAAx] qmul z (qadd qone (decayPoint (H*A) (Q*B))) ≐
      qsub z (qmul (radiusPoint H Q) (frozen p (succ j) X D A B)) := by
  let z := frozen p j X D A B
  let h := radiusPoint H Q
  let t := radiusPoint A B
  have hB' := positive_product _ _ hQ hB
  have factor : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.fraction (H*A) (Q*B) ≐ qmul h t :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hB').eqTrans (radius_multiply H Q A B hQ hB).eqSymm
  have rotate : Γ ⊢[PRAAx] qmul z (qmul h t) ≐ qmul h (frozen p (succ j) X D A B) :=
    (qmul_associative z h t).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative z h) (.eqRefl t)).eqTrans
        ((qmul_associative h z t).eqTrans (qmul_congr (.eqRefl h) (frozen_succ p j X D A B hB).eqSymm)))
  have neg : Γ ⊢[PRAAx] qmul z (decayPoint (H*A) (Q*B)) ≐
      GaussianRationalMetric.qnegative (qmul h (frozen p (succ j) X D A B)) :=
    (GaussianGammaDigammaTwoShiftSecants.negative_mul z _).eqSymm.eqTrans
      (GaussianInverseBinomialRows.negative_congr ((qmul_congr (.eqRefl z) factor).eqTrans rotate))
  exact (GaussianRationalCoefficientScaling.qmul_add z qone (decayPoint (H*A) (Q*B))).eqTrans
    (qadd_congr (qmul_one_right z (qmul_canonical _ _)) neg)

private theorem shifted_product_near (p j X D H Q T A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hQ : Γ ⊢[PRAAx] le one Q)
    (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] distanceBounded (frozen p j (X*Q+H*D) (D*Q) A B)
      (qmul (frozen p j X D A B) (decay (H*A) (Q*B) p)) (num 16*pw T j) (unit p) := by
  let w := weightedKernel p j A B
  let r := realDecay p (X*A) (D*B)
  let r' := realDecay p ((X*Q+H*D)*A) ((D*Q)*B)
  let v := decay (H*A) (Q*B) p
  have f := GaussianEulerDecayGlobalIncrement.shifted_positive_product p X D H Q A B hD hQ hB
  have near := GaussianApproximateInverseDistance.multiply_distance w r' (qmul r v) (pw T j) (num 16)
    (unit p) (unit_positive p) (weighted_kernel_bound p j A B T hB hT) f
  have right : Γ ⊢[PRAAx] qmul w (qmul r v) ≐ qmul (qmul r w) v :=
    (qmul_associative w r v).eqSymm.eqTrans (qmul_congr (qmul_commutative w r) (.eqRefl v))
  exact distance_congr (qmul_commutative w r') right (by ipra_ring) (.eqRefl _) near

private theorem frozen_linear_near (p j X D H Q T A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hQ : Γ ⊢[PRAAx] le one Q)
    (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    let z := frozen p j X D A B
    let E := leadingDenominator p j X D Q A B
    Γ ⊢[PRAAx] distanceBounded (qmul z (decay (H*A) (Q*B) p))
      (qsub z (qmul (radiusPoint H Q) (frozen p (succ j) X D A B)))
      (leadingNumerator p j X D H A B*unit p+(num 8*pw T j)*E) (E*unit p) := by
  let z := frozen p j X D A B
  let N := realNumerator z
  let F := realDenominator z
  let d := Q*B
  let E := leadingDenominator p j X D Q A B
  let P := unit p
  let w := qadd qone (decayPoint (H*A) d)
  let v := decay (H*A) d p
  have hd := positive_product _ _ hQ hB
  have hf : Γ ⊢[PRAAx] le one F := RationalArgmin.denominator_positive _
  have hp := unit_positive (Γ := Γ) p
  have hdd := positive_product _ _ hd hd
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hf hdd
  have den := positive_product _ _ hE hp
  have error := GaussianEulerDecayGlobalTaylor.original_decay_linear_remainder (H*A) d p hd
  have mul := bounded_product z (qsub v w) N F _ _ hf (positive_product _ _ hdd hp)
    (exact_frozen_bound p j X D A B T hB hT) error
  have near : Γ ⊢[PRAAx] distanceBounded (qmul z v) (qmul z w)
      (leadingNumerator p j X D H A B*P+(two*N)*(d*d)) (E*P) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference z v w).eqSymm
      (by dsimp only [leadingNumerator,z,N]; ipra_ring)
      (by dsimp only [leadingDenominator,E,F,d]; ipra_ring) mul
  have cap : Γ ⊢[PRAAx] le N ((num 4*pw T j)*F) := frozen_numerator_bound p j X D A B T hD hB hT
  apply distance_congr (.eqRefl _) (frozen_linear p j X D H Q A B hQ hB) (.eqRefl _) (.eqRefl _)
  apply distance_radius_mono _ _ _ _ _ _ den den ?_ near
  change Γ ⊢[PRAAx] le ((leadingNumerator p j X D H A B*P+(two*N)*(d*d))*(E*P))
    ((leadingNumerator p j X D H A B*P+(num 8*pw T j)*E)*(E*P))
  have dEq : Γ ⊢[PRAAx] E ≐ F*(d*d) := .eqRefl _
  have ep := natEq (Γ := Γ) dEq
  ipra_le 2*𝔞(d)*𝔞(d)*𝔞(E)*𝔞(P)*sl cap with 8*𝔞(pw T j)*𝔞(E)*𝔞(P)*ep

private theorem common_denominator (z w A E p : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] distanceBounded z w A (unit p)) :
    Γ ⊢[PRAAx] distanceBounded z w (A*E) (E*unit p) := by
  have hP := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ hP (positive_product _ _ hE hP)
    (le_of_eq_add (d := zero) (by ipra_ring)) h

theorem observation_taylor (p j X D R S T H Q A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B)
    (h' : Γ ⊢[PRAAx] input (X*Q+H*D) zero (D*Q) zero S T A B)
    (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    let E := leadingDenominator p j X D Q A B
    Γ ⊢[PRAAx] distanceBounded (observation p j (X*Q+H*D) (D*Q) S T A B)
      (linearObservation p j X D R T H Q A B)
      (leadingNumerator p j X D H A B*unit p+allowance j T*E) (E*unit p) := by
  let E := leadingDenominator p j X D Q A B
  let F := realDenominator (frozen p j X D A B)
  let d := Q*B
  let c := radiusPoint H Q
  let old := observation p j X D R T A B
  let old' := observation p (succ j) X D R T A B
  let z := frozen p j X D A B
  let z' := frozen p (succ j) X D A B
  let W := pw T j
  let V := pw T (succ j)
  have hD := h.andE₁.andE₁.andE₂
  have hB := h.andE₂.andE₁
  have hT := h.andE₂.andE₂
  have hd := positive_product _ _ hQ hB
  have hf : Γ ⊢[PRAAx] le one F := RationalArgmin.denominator_positive _
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hf (positive_product _ _ hd hd)
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ he hp
  have r₁ := common_denominator _ _ _ E p he (frozen_error p j _ _ S T A B h')
  have r₂ := common_denominator _ _ _ E p he (shifted_product_near p j X D H Q T A B hD hQ hB hT)
  have r₃ := frozen_linear_near p j X D H Q T A B hD hQ hB hT
  have step : Γ ⊢[PRAAx] bounded c one one :=
    bounded_radius_mono _ H Q one one hQ (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) hH) (radius_bounded H Q hQ)
  have oldNear : Γ ⊢[PRAAx] distanceBounded old z (num 12*W) (unit p) := frozen_error p j X D R T A B h
  have nextNear : Γ ⊢[PRAAx] distanceBounded (qmul c old') (qmul c z') (num 12*V) (unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (one_mul _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance c old' z' one (num 12*V) (unit p) hp step
        (frozen_error p (succ j) X D R T A B h))
  have right := GaussianNamedDifference.difference_distance old z (qmul c old') (qmul c z')
    (num 12*W) (num 12*V) (unit p) hp oldNear nextNear
  have r₄ := common_denominator _ _ _ E p he (distance_symmetric _ _ _ _ hp right)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [allowance,W,V]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den (distance_triangle_same _ _ _ _ _ _ den
      (distance_triangle_same _ _ _ _ _ _ den r₁ r₂) r₃) r₄)

theorem actual_weighted_Binet_Taylor_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let X := var 2
     let D := var 3
     let T := var 6
     let H := var 7
     let Q := var 8
     let A := var 9
     let B := var 10
     let E := leadingDenominator (var 0) (var 1) X D Q A B
     (input X zero D zero (var 4) T A B ⋏ input (X*Q+H*D) zero (D*Q) zero (var 5) T A B) ⟶
       (le one Q ⋏ le H Q) ⟶
       distanceBounded (observation (var 0) (var 1) (X*Q+H*D) (D*Q) (var 5) T A B)
         (linearObservation (var 0) (var 1) X D (var 4) T H Q A B)
         (leadingNumerator (var 0) (var 1) X D H A B*unit (var 0)+allowance (var 1) T*E)
         (E*unit (var 0))) :=
  closeUniv 11 (.impI (.impI (observation_taylor _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTaylorRows
