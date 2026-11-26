import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorBufferEvaluation
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorFrozen
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeExponentTaylor

/-!
# Horner approximation for the original Barnes exponent increment

The stored polynomial groups the frozen prefactor, the finite quadratic
correction and the retained logarithm by degree. Its original Horner
evaluation has the same error bound as the finite rational formula.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorHorner

open_ipra
open GaussianBarnesCanonicalExponentTaylor (nameF data headPolynomial)
open GaussianBarnesCanonicalExponentTaylorBuffer
  (buffer linearCoefficient quadraticCoefficient prefactorLinear prefactorQuadratic)
open GaussianBarnesCanonicalExponentTaylorBufferEvaluation (expanded evaluate_eq)
open GaussianBarnesCanonicalExponentTaylorFrozen (rationalPolynomial numerator denominator rational_rate_of_cutoff)
open GaussianBarnesCanonicalCorrectedMercatorCofinal (input cutoff freezeDenominator cutoff_budget)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefactor
  (negativeHalf quadraticCoefficientF quadraticCoefficientData)
open GaussianBarnesCanonicalPrefactorExponentDerivative (squareStep twicePoint)
open GaussianBarnesCanonicalHeadCorrectionDerivative (halfSquare slope)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents)
open GaussianGammaCanonicalExponent (constantF harmonicPoint)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianRationalHorner (ofGaussian evaluate qadd qmul qmul_canonical ofGaussian_canonical positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalSumAlgebra (qadd_associative shuffle_four)
open GaussianRationalReciprocal (power)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalPowerAlgebra (qmul_commutative power_two)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianEulerIncompleteFactorialCombination (right_distribute)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem move_factor (a b c : PTm n) :
    Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul (qmul a c) b :=
  (qmul_congr (.eqRefl _) (qmul_commutative b c)).eqTrans (qmul_associative a c b).eqSymm

private theorem combine_weights (a b c d x y : PTm n) :
    Γ ⊢[PRAAx] qadd (qadd (qmul a x) (qmul b y)) (qadd (qmul c x) (qmul d y)) ≐
      qadd (qmul (qadd a c) x) (qmul (qadd b d) y) :=
  (qadd_associative (qadd (qmul a x) (qmul b y)) (qmul c x) (qmul d y)).eqSymm.eqTrans
    ((shuffle_four (qmul a x) (qmul b y) (qmul c x) (qmul d y)).eqTrans
      (qadd_congr (right_distribute a c x).eqSymm (right_distribute b d y).eqSymm))

private theorem halve_fraction (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (radiusPoint one two) (ofGaussian h B) ≐ ofGaussian h (two*B) := by
  let t := radiusNumerator (one : PTm n)
  let u := radiusPoint (one : PTm n) two
  let d := ofGaussian h B
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have den := positive_product two B ht hB
  have raw := GaussianRationalHorner.qmul_represents u d t h two B ht hB
    (radius_represents one two ht) (GaussianRationalHorner.ofGaussian_represents h B hB)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.mul t h) h := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [t,radiusNumerator,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,
        ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;>
      (try ipra_simps) <;> ring
  exact GaussianRationalHorner.canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ den) den
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (.eqRefl _) raw)
    (GaussianRationalHorner.ofGaussian_represents _ _ den)

private theorem prefactor_expansion (q z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    let a := ofGaussian h B
    let s := ap2 GaussianStirlingConstant.nameF q (GaussianStirlingConstant.nameData zero)
    let g := ap2 quadraticCoefficientF q quadraticCoefficientData
    Γ ⊢[PRAAx] qadd (qmul a s) (qmul negativeHalf (qadd a (qmul (squareStep z h B) g))) ≐
      qadd (qmul (prefactorLinear q z B) a) (qmul (prefactorQuadratic q) (power a two)) := by
  let a := ofGaussian h B
  let b := power a two
  let s := ap2 GaussianStirlingConstant.nameF q (GaussianStirlingConstant.nameData zero)
  let g := ap2 quadraticCoefficientF q quadraticCoefficientData
  let t := twicePoint z B
  let v : PTm n := negativeHalf
  let w := qadd qone (qmul t g)
  have ha := ofGaussian_canonical h B hB
  have sq : Γ ⊢[PRAAx] squareStep z h B ≐ qadd (qmul a t) b :=
    (GaussianBarnesCanonicalRelativeExponentTaylor.square_expansion z h B hB).eqTrans
      (qadd_congr (.eqRefl _) (power_two a ha).eqSymm)
  have spread : Γ ⊢[PRAAx] qmul (squareStep z h B) g ≐ qadd (qmul a (qmul t g)) (qmul b g) :=
    (qmul_congr sq (.eqRefl g)).eqTrans ((right_distribute (qmul a t) b g).eqTrans
      (qadd_congr (qmul_associative a t g) (.eqRefl _)))
  have combine : Γ ⊢[PRAAx] qmul a w ≐ qadd a (qmul a (qmul t g)) :=
    (qmul_add a qone (qmul t g)).eqTrans (qadd_congr (qmul_one_right a ha) (.eqRefl _))
  have inner : Γ ⊢[PRAAx] qadd a (qmul (squareStep z h B) g) ≐ qadd (qmul a w) (qmul b g) :=
    (qadd_congr (.eqRefl a) spread).eqTrans
      ((qadd_associative a (qmul a (qmul t g)) (qmul b g)).eqSymm.eqTrans (qadd_congr combine.eqSymm (.eqRefl _)))
  have correction : Γ ⊢[PRAAx] qmul v (qadd a (qmul (squareStep z h B) g)) ≐
      qadd (qmul (qmul v w) a) (qmul (qmul v g) b) :=
    (qmul_congr (.eqRefl v) inner).eqTrans
      ((qmul_add v (qmul a w) (qmul b g)).eqTrans (qadd_congr (move_factor v a w) (move_factor v b g)))
  exact (qadd_congr (qmul_commutative a s) correction).eqTrans
    ((qadd_associative (qmul s a) (qmul (qmul v w) a) (qmul (qmul v g) b)).eqSymm.eqTrans
      (qadd_congr (right_distribute s (qmul v w) a).eqSymm (.eqRefl _)))

private theorem head_expansion (z h R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    let a := ofGaussian h B
    Γ ⊢[PRAAx] headPolynomial z h R B ≐ qadd (qmul (slope z B (initial R)) a)
      (qmul (qmul (radiusPoint one two) (harmonicPoint (initial R))) (power a two)) := by
  let a := ofGaussian h B
  let b := power a two
  let u : PTm n := radiusPoint one two
  let t := harmonicPoint (initial R)
  have half : Γ ⊢[PRAAx] halfSquare h B ≐ qmul u b :=
    (qmul_congr (.eqRefl a) (halve_fraction h B hB).eqSymm).eqTrans
    ((qmul_commutative a (qmul u a)).eqTrans
      ((qmul_associative u a a).eqTrans (qmul_congr (.eqRefl u)
        (power_two a (ofGaussian_canonical h B hB)).eqSymm)))
  have term : Γ ⊢[PRAAx] qmul (halfSquare h B) t ≐ qmul (qmul u t) b :=
    (qmul_congr half (.eqRefl t)).eqTrans
      ((qmul_associative u b t).eqTrans (move_factor u b t))
  exact qadd_congr (qmul_commutative a (slope z B (initial R))) term

theorem expanded_from_frozen (q z h R B r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalPolynomial q z h R B r M ≐ expanded q z h R B r M := by
  let a := ofGaussian h B
  let b := power a two
  let l := slope z B (initial R)
  let t : PTm n := qmul (radiusPoint one two) (harmonicPoint (initial R))
  let f := GaussianBarnesCanonicalDerivativeTail.value z B (initial R) r
  let g := qmul (radiusPoint one two) (GaussianBarnesCanonicalSecondDerivativeTail.value z B (initial R) r)
  let v := GaussianBarnesCanonicalHigherMercatorTranspose.polynomial z h B (initial R) r M
  let p := prefactorLinear q z B
  let u := prefactorQuadratic q
  let e := qadd (qmul (qadd p l) a) (qmul (qadd u t) b)
  let d := qadd (qmul f a) (qmul g b)
  have first := prefactor_expansion q z h B hB
  have second := head_expansion z h R B hB
  have prefixEq := (qadd_congr first second).eqTrans (combine_weights p u l t a b)
  have tailEq : Γ ⊢[PRAAx] GaussianBarnesCanonicalCorrectedMercatorPrefix.polynomial z h B (initial R) r M ≐ qadd d v :=
    qadd_congr (qadd_congr (qmul_commutative a f) (.eqRefl _)) (.eqRefl _)
  have third : Γ ⊢[PRAAx] qadd e (qadd d v) ≐ expanded q z h R B r M :=
    (qadd_associative e d v).eqSymm.eqTrans (qadd_congr (combine_weights (qadd p l) (qadd u t) f g a b) (.eqRefl _))
  exact (qadd_congr prefixEq tailEq).eqTrans third

def hornerValue (q z h R B r M : PTm n) : PTm n :=
  evaluate (buffer q z R B r M) (ofGaussian h B)

theorem horner_rationalPolynomial (q z h R B r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] hornerValue q z h R B r M ≐ rationalPolynomial q z h R B r M :=
  (evaluate_eq q z h R B r M hB).eqTrans (expanded_from_frozen q z h R B r M hB).eqSymm

theorem rate_of_cutoff (p q z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H)
    (hr : Γ ⊢[PRAAx] le (cutoff p R) (freezeDenominator R r)) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (hornerValue q z h R B r M)
      (numerator p q z h R B H r M) (denominator p q R B M) := by
  let K := numerator p q z h R B H r M
  let D := denominator p q R B M
  have eq := (horner_rationalPolynomial q z h R B r M hs.andE₁.andE₁).eqSymm
  have moved := Prf.eqSubst1 (Γ := Γ) (independentRate nameF constantF (Syn.shift (data z h R B))
    (var 0) (Syn.shift K) (Syn.shift D)) eq
      (by simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using
        rational_rate_of_cutoff p q z h R B H r M hs hr)
  simpa only [subst_independentRate,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using moved

theorem actual_Barnes_full_exponent_Horner_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let q := var 1
     let z := var 2
     let h := var 3
     let R := var 4
     let B := var 5
     let H := var 6
     let M := var 7
     let r := cutoff p R
     input (previous M) z h R B H ⟶ independentRate nameF constantF (data z h R B) (hornerValue q z h R B r M)
       (numerator p q z h R B H r M) (denominator p q R B M)) :=
  closeUniv 8 (.impI (rate_of_cutoff _ _ _ _ _ _ _ _ _ Prf.hyp0 (cutoff_budget _ _)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorHorner
