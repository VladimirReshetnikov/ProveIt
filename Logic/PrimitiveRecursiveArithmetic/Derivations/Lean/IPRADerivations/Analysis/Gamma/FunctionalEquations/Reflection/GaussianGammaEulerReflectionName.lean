import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaEulerReflectionHead
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerReciprocalInverse
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Integration.Moments.GaussianMomentReflection

/-!
# Finite Euler reflection for the original approximant names

The logarithmic exponents at z/B and −z/B are additive inverses. Their
exponentials cancel, so the product of the actual reciprocal Euler
approximant names is the constant paired head −(z/B)² S_N(z/B).
At the certified pole-free inputs, the actual Euler Gamma names therefore
satisfy the cleared finite reflection law with that same product.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerReflectionName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerReflectionHead (denominator returned_pairing)
open GaussianGammaFiniteApproximantName
  (logF logExponentF logExponentData log_exponent_regular exponential_input
    exponentialInputData qF qData q_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData euler_regular euler_product)
open GaussianGammaReciprocalInverse (named_product_exchange inverse_pairs constant_inverse)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData oneF one_fast
  multiply_sample_error negative_sample_error equivalent_of_envelope multiply_one)
open GaussianRationalHorner
  (qmul qzero ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique)
open GaussianRationalMetric (qnegative qnegative_represents qnegative_canonical qsub distanceBounded)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianInverseBinomialRows (negative_congr)
open GaussianNamedDifference (negative_distance)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "gneg" => ComplexLogarithmRemainder.neg

def exponentF : PR 2 := GaussianRadiusExponentialName.nameF logExponentF

theorem fraction_negation (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (gneg z) B ≐ qnegative (ofGaussian z B) :=
  canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hB) (qnegative_canonical _) hB
    (ofGaussian_represents _ _ hB) (qnegative_represents _ _ _ (ofGaussian_represents _ _ hB))

private theorem qsub_zero_neg (a : PTm n) : Γ ⊢[PRAAx] qsub qzero a ≐ qnegative a :=
  qzero_add _ (qnegative_canonical _)

private def oppositeBudget (f : PR 2) (x a : PTm n) : PTm n :=
  (multiplyModulus f constantF x (qnegative a)+one) +
    ((multiplyModulus f constantF x a+one)+GaussianNameRingLaws.three)

private theorem opposite_sample (f : PR 2) (x a p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (multiplyF f constantF) p (multiplyData f constantF x (qnegative a)))
      (ap2 (negativeF (multiplyF f constantF)) p (negativeData (multiplyData f constantF x a)))
      (oppositeBudget f x a) (unit p) := by
  let F := multiplyF f constantF
  let A := multiplyData f constantF x a
  let u := ap2 f p x
  have hA := multiply_fast f constantF x a hf (constant_regular a)
  have plus : Γ ⊢[PRAAx] distanceBounded (ap2 F p A) (qmul u a)
      (multiplyModulus f constantF x a+one) (unit p) :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr
    (.eqRefl _) (constant_at p a)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error f constantF x a p hf (constant_regular a))
  let A' := multiplyData f constantF x (qnegative a)
  let u' := ap2 (negativeF F) p (negativeData A)
  let v := qnegative (ap2 F p A)
  let w := qnegative (qmul u a)
  let C := multiplyModulus f constantF x (qnegative a)+one
  let D := multiplyModulus f constantF x a+one
  let t : PTm n := GaussianNameRingLaws.three
  have minus : Γ ⊢[PRAAx] distanceBounded (ap2 F p A') (qmul u (qnegative a)) C (unit p) :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr
      (.eqRefl _) (constant_at p (qnegative a))) (.eqRefl _) (.eqRefl _)
      (multiply_sample_error f constantF x (qnegative a) p hf (constant_regular _))
  have conversion : Γ ⊢[PRAAx] qmul u (qnegative a) ≐ qnegative (qmul u a) :=
    GaussianMomentReflection.negative_right_product u a
  have compared : Γ ⊢[PRAAx] distanceBounded u' v t (unit p) :=
    distance_congr (.eqRefl _) (qsub_zero_neg (ap2 F p A))
    (.eqRefl _) (.eqRefl _) (negative_sample_error F A p hA)
  have ne : Γ ⊢[PRAAx] distanceBounded v w D (unit p) :=
    negative_distance (ap2 F p A) (qmul u a) D (unit p) (unit_positive p) plus
  have negBound := distance_triangle_same u' v w t D (unit p) (unit_positive p) compared ne
  have raw := GaussianNameRingLaws.through_identity (ap2 F p A') u' (qmul u (qnegative a)) w
    C (t+D) (unit p) (unit_positive p) minus negBound conversion
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold oppositeBudget C D t; ipra_ring) (.eqRefl _) raw

theorem opposite_constant_product (f : PR 2) (x a : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f constantF) (negativeF (multiplyF f constantF))
      (multiplyData f constantF x (qnegative a)) (negativeData (multiplyData f constantF x a)) := by
  apply equivalent_of_envelope _ _ _ _ (oppositeBudget f x a)
    (multiply_fast _ _ _ _ hf (constant_regular _))
    (GaussianNameRingLaws.negative_fast _ _ (multiply_fast _ _ _ _ hf (constant_regular _)))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  simpa only [oppositeBudget,GaussianRationalMetric.subst_qnegative,GaussianNameArithmetic.subst_multiplyData,
    GaussianNameArithmetic.subst_multiplyModulus,GaussianNameRingLaws.subst_negativeData,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,GaussianNameRingLaws.three,Syn.shift] using
    opposite_sample f (Syn.shift x) (Syn.shift a) (var 0) hs

theorem reflected_exponent (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent logExponentF (negativeF logExponentF)
      (logExponentData (gneg z) B N) (negativeData (logExponentData z B N)) := by
  have point := negative_congr (fraction_negation z B hB)
  have regular := GaussianGammaFiniteApproximantName.log_regular N hN
  have replace := multiply_cross logF logF constantF constantF N N _ _
    regular regular (constant_regular _) (constant_regular _) (cross_refl _ _ regular) (constant_data_cross _ _ point)
  have ref := opposite_constant_product logF N (qnegative (ofGaussian z B))
    regular
  exact cross_trans _ _ _ _ _ _ replace ref

theorem reflected_exponential (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF exponentF exponentF) oneF
      (multiplyData exponentF exponentF (exponentialInputData logExponentF (logExponentData z B N))
        (exponentialInputData logExponentF (logExponentData (gneg z) B N))) (logExponentData z B N) := by
  let f := logExponentF
  let X := logExponentData z B N
  let Y := logExponentData (gneg z) B N
  let R := GaussianNameBounds.U f X
  let S := GaussianNameBounds.U f Y
  let E := GaussianRadiusExponentialName.nameF
  let D : PTm n → PTm n → PTm n := GaussianRadiusExponentialName.data
  have hX := exponential_input f X (log_exponent_regular z B N hN)
  have hY := exponential_input f Y (log_exponent_regular (gneg z) B N hN)
  have hneg := GaussianExponentialInverse.negative_input f R X hX
  have compare := GaussianExponentialRadiusIndependence.independent_radii_proper f (negativeF f) S R
    Y (negativeData X) hY hneg (reflected_exponent z B N hB hN)
  have lift := multiply_cross (E f) (E f) (E f) (E (negativeF f)) (D R X) (D R X) (D S Y) (D R (negativeData X))
    (GaussianRadiusExponentialName.name_regular _ _ _ hX) (GaussianRadiusExponentialName.name_regular _ _ _ hX)
    (GaussianRadiusExponentialName.name_regular _ _ _ hY) (GaussianRadiusExponentialName.name_regular _ _ _ hneg)
    (cross_refl _ _ (GaussianRadiusExponentialName.name_regular _ _ _ hX)) compare
  exact cross_trans _ _ _ _ _ _ lift (GaussianExponentialInverse.exponential_inverse f R X hX)

def qPairF : PR 2 := multiplyF qF qF

def qPairData (z B N : PTm n) : PTm n := multiplyData qF qF (qData z B N) (qData (gneg z) B N)

theorem reciprocal_Euler_pair (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent qPairF constantF (qPairData z B N) (denominator z B N) := by
  let C := constantF
  let E := exponentF
  let D := denominator z B N
  let A := GaussianGammaEulerHead.run z B N
  let B' := GaussianGammaEulerHead.run (gneg z) B N
  let X := exponentialInputData logExponentF (logExponentData z B N)
  let Y := exponentialInputData logExponentF (logExponentData (gneg z) B N)
  let ref := logExponentData z B N
  have hX : Γ ⊢[PRAAx] pointCN E X := GaussianRadiusExponentialName.name_regular _ _ _
    (exponential_input _ _ (log_exponent_regular z B N hN))
  have hY : Γ ⊢[PRAAx] pointCN E Y := GaussianRadiusExponentialName.name_regular _ _ _
    (exponential_input _ _ (log_exponent_regular (gneg z) B N hN))
  have exchange := named_product_exchange C E C E A X B' Y
    (constant_regular _) hX (constant_regular _) hY
  have head := cross_trans _ _ _ _ _ _ (constant_product_cross A B')
    (constant_data_cross _ _ (returned_pairing z B N hB))
  have lift := multiply_cross (multiplyF C C) C (multiplyF E E) oneF
    (multiplyData C C A B') D (multiplyData E E X Y) D
    (multiply_fast _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
    (multiply_fast _ _ _ _ hX hY) (one_fast _) head
    (cross_trans _ _ _ _ _ _ (reflected_exponential z B N hB hN)
      (GaussianBoundedInverseApartness.ones_equivalent ref D))
  exact cross_trans _ _ _ _ _ _ exchange
    (cross_trans _ _ _ _ _ _ lift (multiply_one C D (constant_regular D)))

def eulerPairF : PR 2 := multiplyF eulerF eulerF

def eulerPairData (z R B d N : PTm n) : PTm n :=
  multiplyData eulerF eulerF (eulerData z R B d N) (eulerData (gneg z) R B d N)

def source (z R B a d N : PTm n) : Fm PTm n :=
  GaussianGammaEulerReciprocalInverse.source z R B a d N ⋏
    GaussianGammaEulerReciprocalInverse.source (gneg z) R B a d N

theorem Euler_reflection (z R B a d N : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF eulerPairF) oneF
      (multiplyData constantF eulerPairF (denominator z B N) (eulerPairData z R B d N)) (qData z B N) := by
  let P := qData z B N
  let Q := qData (gneg z) B N
  let U := eulerData z R B d N
  let V := eulerData (gneg z) R B d N
  let D := denominator z B N
  have hB := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  have hN := (GaussianGammaFoldedMajorantExponent.tail_source z R B N
    (GaussianGammaEulerReciprocalInverse.folded_source z R B a d N hs.andE₁)).andE₂.andE₁
  have hP := q_regular z B N hN
  have hQ := q_regular (gneg z) B N hN
  have hU := euler_regular z R B a d N hs.andE₁
  have hV := euler_regular (gneg z) R B a d N hs.andE₂
  have p := euler_product z R B a d N hs.andE₁
  have q := cross_trans _ _ _ _ _ _ (euler_product (gneg z) R B a d N hs.andE₂)
    (GaussianBoundedInverseApartness.ones_equivalent Q P)
  have paired := inverse_pairs qF qF eulerF eulerF P Q U V P hP hQ hU hV p q
  have hUV := multiply_fast _ _ _ _ hU hV
  have lift := multiply_cross constantF qPairF eulerPairF eulerPairF D (qPairData z B N)
    (eulerPairData z R B d N) (eulerPairData z R B d N)
    (constant_regular _) (multiply_fast _ _ _ _ hP hQ) hUV hUV
    (cross_symm _ _ _ _ (reciprocal_Euler_pair z B N hB hN)) (cross_refl _ _ hUV)
  exact cross_trans _ _ _ _ _ _ lift paired

theorem Euler_reflection_value (z R B a d N : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d N) :
    Γ ⊢[PRAAx] crossEquivalent eulerPairF constantF (eulerPairData z R B d N)
      (GaussianRationalReciprocal.reciprocal (denominator z B N)) := by
  let D := denominator z B N
  let G := eulerPairF
  let x := eulerPairData z R B d N
  let U := GaussianNameBounds.U G x
  let h := GaussianBoundedInverseApartness.height constantF G D x U
  have hD : Γ ⊢[PRAAx] pointCN constantF D := constant_regular _
  have hx : Γ ⊢[PRAAx] pointCN G x := multiply_fast _ _ _ _
    (euler_regular z R B a d N hs.andE₁) (euler_regular (gneg z) R B a d N hs.andE₂)
  have disk : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples G x U one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,GaussianRootApproximationWitness.pointBounds,
      U,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using GaussianNameBounds.all_samples_bounded G x hx
  have pair := cross_trans _ _ _ _ _ _ (Euler_reflection z R B a d N hs)
    (GaussianBoundedInverseApartness.ones_equivalent (qData z B N) D)
  have inverse := GaussianBoundedInverseApartness.bounded_inverse_correct constantF G D x U one
    (GaussianNameBounds.U_positive G x) (le_refl one) hD hx disk pair
  have lower : Γ ⊢[PRAAx] GaussianNameReciprocal.lower D (unit h) :=
    GaussianNameReciprocal.lower_congr (constant_at _ D) (.eqRefl _) inverse.andE₁.andE₂
  have norm := GaussianNameReciprocal.lower_norm_positive _ _ (unit_positive h) lower
  have exactProduct := constant_inverse D (GaussianRationalReciprocal.reciprocal D) D
    (GaussianRationalReciprocal.reciprocal_identity D norm)
  have ref := GaussianBoundedInverseApartness.reciprocal_matches_inverse constantF constantF h D
    (GaussianRationalReciprocal.reciprocal D) hD (constant_regular _) inverse.andE₁.andE₂ exactProduct
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ inverse.andE₂) ref

theorem original_reciprocal_Euler_pair_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent qPairF constantF
      (qPairData (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (reciprocal_Euler_pair _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_finite_Euler_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent (multiplyF constantF eulerPairF) oneF
        (multiplyData constantF eulerPairF (denominator (var 0) (var 2) (var 5))
          (eulerPairData (var 0) (var 1) (var 2) (var 4) (var 5))) (qData (var 0) (var 2) (var 5))) :=
  closeUniv 6 (.impI (Euler_reflection _ _ _ _ _ _ Prf.hyp0))

theorem original_finite_Euler_reflection_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent eulerPairF constantF (eulerPairData (var 0) (var 1) (var 2) (var 4) (var 5))
        (GaussianRationalReciprocal.reciprocal (denominator (var 0) (var 2) (var 5)))) :=
  closeUniv 6 (.impI (Euler_reflection_value _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerReflectionName
