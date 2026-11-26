import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalDerivativeAlgebra
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalSecondDerivativeStep
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteFactorialDenominator

/-!
# Exact low-degree coefficients of the corrected Barnes logarithm row

The literal degree-two local logarithm polynomial plus the original
correction difference has the stored Barnes first-derivative row as
its linear coefficient and half the stored second-derivative row as
its quadratic coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalQuadraticBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmName (baseNumerator baseDenominator base_positive)
open GaussianBarnesCanonicalDeflatedFactor (inverseInteger)
open GaussianBarnesCanonicalDerivativeAlgebra (linearTerm localQuadratic correctionDifference cancellation)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalRelativeStep (source numerator denominator denominator_positive relative)
open GaussianBarnesCanonicalRelativeTaylor (step quadraticError recover_step)
open GaussianDominantPairAlgebra (radiusPoint radius_multiply radius_congr)
open GaussianEulerIncompleteFactorialDenominator (radius_rescale)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique qadd qmul qmul_canonical)
open GaussianRationalInverseQuadraticAlgebra (cancel_nested_product)
open GaussianRationalMetric (qsub)
open GaussianRationalPowerAlgebra (qmul_commutative power_two)
open GaussianRationalReciprocal (qone reciprocal power)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "second" => GaussianBarnesCanonicalSecondDerivativeRow.value
local notation "logValue" => GaussianFiniteLogarithmPolynomial.value

def secondCoefficient (z B k : PTm n) : PTm n := qmul (radiusPoint one two) (second z B k)

def secondTerm (z h B k : PTm n) : PTm n :=
  qmul (secondCoefficient z B k) (power (ofGaussian h B) two)

@[simp] theorem subst_secondCoefficient {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (secondCoefficient z B k) = secondCoefficient (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [secondCoefficient,one,two]

@[simp] theorem subst_secondTerm {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (secondTerm z h B k) = secondTerm (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [secondTerm,two]

private theorem exchange (a b c d : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul a b) (qmul c d) ≐ qmul (qmul a c) (qmul b d) := by
  have middle := (qmul_associative (Γ := Γ) b c d).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative b c) (.eqRefl d)).eqTrans (qmul_associative c b d))
  exact (qmul_associative a b (qmul c d)).eqTrans
    ((qmul_congr (.eqRefl a) middle).eqTrans (qmul_associative a c (qmul b d)).eqSymm)

private theorem radius_cancel (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qmul (radiusPoint k two) (inverseInteger k) ≐ radiusPoint one two := by
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  exact (radius_multiply k two one k h2 hk).eqTrans
    ((radius_congr (mul_comm k one) (.eqRefl _)).eqTrans (radius_rescale one two k h2 hk))

theorem quadratic_error (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] quadraticError z h B k ≐ secondTerm z h B k := by
  let a := base z B k
  let i := reciprocal a
  let b := ofGaussian h B
  let g := step h B k
  let v := relative z h B k
  let t := inverseInteger k
  let Q := qmul b b
  let G := qmul g g
  let I := qmul i i
  let r := qsub qone I
  let K := radiusPoint k two
  let L : PTm n := radiusPoint one two
  have hB := hs.andE₁.andE₁
  have hk := hs.andE₁.andE₂.andE₁
  have vCanon := ofGaussian_canonical (numerator z h B k) (denominator z B k)
    (denominator_positive z R B k hs.andE₁)
  have inv := (qmul_commutative i a).eqTrans (GaussianBarnesCanonicalSecondDerivativeRow.reciprocal_base z R B k hs.andE₁)
  have rel : Γ ⊢[PRAAx] v ≐ qmul g i :=
    ((qmul_congr (.eqRefl i) (recover_step z h R B k H hs).eqSymm).eqTrans
      (cancel_nested_product i a v vCanon inv)).eqSymm.eqTrans (qmul_commutative i g)
  have sq : Γ ⊢[PRAAx] qmul v v ≐ qmul G I := (qmul_congr rel rel).eqTrans (exchange g i g i)
  have difference : Γ ⊢[PRAAx] qsub G (qmul v v) ≐ qmul G r :=
    (qsub_congr (qmul_one_right G (qmul_canonical g g)).eqSymm sq).eqTrans (multiplication_difference G qone I)
  have change_step : Γ ⊢[PRAAx] qmul b t ≐ g := GaussianBarnesCanonicalSecondDerivativeStep.step_factor h B k hB hk
  have gsq : Γ ⊢[PRAAx] G ≐ qmul Q (qmul t t) :=
    (qmul_congr change_step.eqSymm change_step.eqSymm).eqTrans (exchange b t b t)
  have scale : Γ ⊢[PRAAx] qmul K G ≐ qmul (qmul L t) Q :=
    (qmul_congr (.eqRefl K) (gsq.eqTrans (qmul_commutative Q (qmul t t)))).eqTrans
      ((qmul_associative K (qmul t t) Q).eqSymm.eqTrans
        (qmul_congr ((qmul_associative K t t).eqSymm.eqTrans (qmul_congr (radius_cancel k hk) (.eqRefl t))) (.eqRefl Q)))
  have powers := power_two b (ofGaussian_canonical h B hB)
  exact (qmul_congr (.eqRefl K) difference).eqTrans
    ((qmul_associative K G r).eqSymm.eqTrans
      ((qmul_congr scale (.eqRefl r)).eqTrans
        ((qmul_associative (qmul L t) Q r).eqTrans
          ((exchange L t Q r).eqTrans
            ((qmul_commutative (qmul L Q) (qmul t r)).eqTrans
              ((qmul_associative (qmul t r) L Q).eqSymm.eqTrans
                (qmul_congr (qmul_commutative (qmul t r) L) powers.eqSymm)))))))

theorem low_terms (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) : Γ ⊢[PRAAx]
    qadd (qmul (radiusPoint k one) (logValue two (relative z h B k))) (correctionDifference z h B k) ≐
      qadd (linearTerm z h B k) (secondTerm z h B k) := by
  let a := numerator z h B k
  let D := denominator z B k
  have hd := denominator_positive z R B k hs.andE₁
  have hbase := base_positive D hd
  have p : Γ ⊢[PRAAx] logValue two (relative z h B k) ≐ GaussianBarnesCanonicalCubicName.base a D :=
    canonical_unique _ _ (baseNumerator a D) (baseDenominator D)
      (GaussianRationalFiniteSum.sum_canonical GaussianFiniteLogarithmPolynomial.sourceTerm two (relative z h B k))
      (ofGaussian_canonical _ _ hbase) hbase
      (GaussianFiniteLogarithmSampler.base_represents a D hd) (ofGaussian_represents _ _ hbase)
  have start : Γ ⊢[PRAAx] qmul (radiusPoint k one) (logValue two (relative z h B k)) ≐ localQuadratic z h B k :=
    qmul_congr (.eqRefl _) p
  exact (qadd_congr start (.eqRefl _)).eqTrans ((cancellation z h R B k H hs).eqTrans
    (qadd_congr (.eqRefl _) (quadratic_error z h R B k H hs)))

theorem actual_Barnes_corrected_quadratic_terms_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     source z h R B k H ⟶
       (qadd (qmul (radiusPoint k one) (logValue two (relative z h B k))) (correctionDifference z h B k) ≐
         qadd (linearTerm z h B k) (secondTerm z h B k))) :=
  closeUniv 6 (.impI (low_terms _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalQuadraticBinding
