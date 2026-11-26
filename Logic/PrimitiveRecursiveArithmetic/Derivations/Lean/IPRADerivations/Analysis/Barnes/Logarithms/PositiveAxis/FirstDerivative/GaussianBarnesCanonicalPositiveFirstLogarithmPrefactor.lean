import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveFirstLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.SecondDerivative.GaussianBarnesCanonicalPositiveSecondLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdDerivativePositiveMargin
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedSumDifference

/-!
# Exact affine increment of the original Barnes prefactor derivative

The first-derivative program keeps its original linear and quadratic
exponent data. Its exact named difference is the physical step times
the original negative coefficient −(1+γ).
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor

open_ipra
open ComplexLogarithmRemainder (add oneCode scale)
open GaussianBarnesCanonicalPrefactor (linearF correctionF polynomialF quadraticF negativeHalf
  quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorInverse (exponentF)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf linearOf quadraticOf polynomialOf correctionOf twicePoint)
open GaussianBarnesCanonicalPositiveFirstLogarithm (prefactorData prefactor_regular)
open GaussianBarnesCanonicalPositiveSecondLogarithm (coefficientF coefficientData coefficient_regular)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (step shifted_center)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaTwoShiftNamedSize (constant_product)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameConjugation (equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_zero_left multiply_associative zeroF zero_at zero_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents
  qadd qadd_canonical qadd_represents qmul qzero represents_congr)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right qone qone_canonical)
open GaussianReciprocalHorner (qadd_zero_right qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "Q" => quadraticCoefficientF
local notation "E" => exponentF
local notation "K" => coefficientF
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

private theorem negative_half_twice : Γ ⊢[PRAAx] qmul (negativeHalf : PTm n) (qadd qone qone) ≐ minusOne := by
  let f := GaussianPositiveRationalLogarithm.fraction (one : PTm n) two
  let a := GaussianDominantPairAlgebra.radiusNumerator (one : PTm n)
  let h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have hread := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) one two h2
  have hfa := represents_congr hread.eqSymm (GaussianRootAlgebra.equal_refl a) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_represents one two h2)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (add a a) (scale two oneCode) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [a,GaussianDominantPairAlgebra.radiusNumerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.re_one,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat]
      ipra_simps
      ring
    · simp only [a,GaussianDominantPairAlgebra.radiusNumerator,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.im_one,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
      ipra_simps
      ring
  have halves : Γ ⊢[PRAAx] qadd f f ≐ qone :=
    canonical_unique _ _ _ two (qadd_canonical _ _) qone_canonical h2
      (represents_congr (.eqRefl _) e (.eqRefl _) (qadd_represents f f a a two h2 hfa hfa))
      (GaussianRationalReciprocal.qone_represents_scaled two)
  have hf : Γ ⊢[PRAAx] GaussianRationalHorner.canonical f := ofGaussian_canonical _ _ h2
  have sum : Γ ⊢[PRAAx] qmul f (qadd qone qone) ≐ qone :=
    (GaussianRationalCoefficientScaling.qmul_add f qone qone).eqTrans
      ((qadd_congr (qmul_one_right f hf) (qmul_one_right f hf)).eqTrans halves)
  exact (GaussianInverseBinomialRows.negative_product f (qadd qone qone)).eqSymm.eqTrans
    (GaussianInverseBinomialRows.negative_congr sum)

private theorem constant_zero (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent C zeroF qzero x := by
  apply equal_samples_cross _ _ _ _ (constant_regular _) (zero_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_qzero] using
    (constant_at (var 0) qzero).eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm

private theorem annihilate (f : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C f) zeroF (multiplyData C f qzero x) y := by
  apply equal_samples_cross _ _ _ _ (multiply_fast _ _ _ _ (constant_regular _) h) (zero_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianNameArithmetic.subst_multiplyData,
    GaussianRationalHorner.subst_qzero] using
    (GaussianGammaRationalWendelBoundary.zero_product_at f (var 0) qzero (Syn.shift x) (.eqRefl _)).eqTrans
      (zero_at (var 0) (Syn.shift y)).eqSymm

private theorem coefficient_sample (p : PTm n) : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
    (ap2 (multiplyF C Q) p (multiplyData C Q minusOne quadraticCoefficientData))
    (ap2 K p coefficientData)
    (multiplyModulus C Q minusOne quadraticCoefficientData+one+GaussianNameRingLaws.three) (unit p) := by
  let q : PTm n := quadraticCoefficientData
  let s := ap2 Q p q
  have raw := GaussianNameRingLaws.multiply_sample_error (Γ := Γ) C Q minusOne q p (constant_regular _) quadratic_coefficient_regular
  have eq := (qmul_congr (constant_at (Γ := Γ) p (minusOne : PTm n)) (.eqRefl s)).eqTrans (negative_as_minusOne s).eqSymm
  have left := distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _) raw
  have right := distance_congr (.eqRefl _)
    (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical s))
    (.eqRefl _) (.eqRefl _) (GaussianNameRingLaws.negative_sample_error (Γ := Γ) Q q p quadratic_coefficient_regular)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) left
    (distance_symmetric _ _ _ _ (unit_positive p) right)

private theorem coefficient_mul : Γ ⊢[PRAAx] crossEquivalent (multiplyF C Q) K
    (multiplyData C Q minusOne quadraticCoefficientData : PTm n) coefficientData := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _
    (multiplyModulus C Q minusOne quadraticCoefficientData+one+GaussianNameRingLaws.three)
    (multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular) coefficient_regular
  refine .allI ?_
  simpa [Syn.shift,minusOne,quadraticCoefficientData,GaussianNameRingLaws.three,one,two] using (coefficient_sample (Γ := Γ.map Fm.shift) (var 0))

theorem basis : Γ ⊢[PRAAx] crossEquivalent E K (exponentOf (qzero : PTm n) (qadd qone qone)) coefficientData := by
  let d : PTm n := qadd qone qone
  let q : PTm n := quadraticCoefficientData
  let u := quadraticOf d
  let v := polynomialOf qzero d
  let w := correctionOf qzero d
  let t := multiplyData C quadraticF negativeHalf u
  have qr : Γ ⊢[PRAAx] pointCN quadraticF u := multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular
  have pr : Γ ⊢[PRAAx] pointCN polynomialF v := add_fast _ _ _ _ (constant_regular _) qr
  have hr := constant_regular (Γ := Γ) (negativeHalf : PTm n)
  have prep := add_cross C zeroF quadraticF quadraticF qzero u u u (constant_regular _) (zero_fast _) qr qr
    (constant_zero u) (cross_refl _ _ qr)
  have pe := cross_trans _ _ _ _ _ _ prep (add_zero_left quadraticF u qr)
  have strip := multiply_cross C C polynomialF quadraticF negativeHalf negativeHalf v u hr hr pr qr
    (cross_refl _ _ hr) pe
  have assoc := (multiply_associative C C Q negativeHalf d q hr (constant_regular _) quadratic_coefficient_regular)
  have scaled := multiply_cross (multiplyF C C) C Q Q (multiplyData C C negativeHalf d)
    minusOne q q (multiply_fast _ _ _ _ hr (constant_regular _)) (constant_regular _)
    quadratic_coefficient_regular quadratic_coefficient_regular
    (constant_product _ _ _ negative_half_twice) (cross_refl _ _ quadratic_coefficient_regular)
  have cr : Γ ⊢[PRAAx] pointCN correctionF w := multiply_fast _ _ _ _ hr pr
  have linear : Γ ⊢[PRAAx] pointCN linearF (linearOf (qzero : PTm n)) :=
    multiply_fast _ _ _ _ (constant_regular _) (GaussianStirlingConstant.name_regular zero)
  have changed := add_cross linearF zeroF correctionF correctionF (linearOf qzero) w w w linear (zero_fast _) cr cr
    (annihilate GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero) w (GaussianStirlingConstant.name_regular zero))
    (cross_refl _ _ cr)
  have corr := cross_trans _ _ _ _ _ _ strip (cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ t assoc) (cross_trans _ _ _ _ _ _ scaled coefficient_mul))
  exact cross_trans _ _ _ _ _ _ changed (cross_trans _ _ _ _ _ _ (add_zero_left correctionF w cr) corr)

theorem exponent_step (A B C' : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (twicePoint (center A B) B)
      (qadd (ofGaussian (step A C') B) (ofGaussian (step A C') B)) ≐ twicePoint (center C' B) B := by
  let z := center A B
  let w := center C' B
  let h := step A C'
  let a := ofGaussian z B
  let s := ofGaussian h B
  let c := ofGaussian w B
  have add_exact : Γ ⊢[PRAAx] qadd a s ≐ c :=
    canonical_unique _ _ w B (qadd_canonical _ _) (ofGaussian_canonical _ _ hB) hB
      (represents_congr (.eqRefl _) (shifted_center A C' B) (.eqRefl _)
        (qadd_represents a s z h B hB (ofGaussian_represents z B hB) (ofGaussian_represents h B hB)))
      (ofGaussian_represents w B hB)
  exact (GaussianRationalFiniteSum.add_shuffle a a s s).eqTrans (qadd_congr add_exact add_exact)

theorem increment (A C' B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (Diff E E) (multiplyF C K)
      (dd (prefactorData C' B) (prefactorData A B))
      (multiplyData C K (ofGaussian (step A C') B) coefficientData) := by
  let s := ofGaussian (step A C') B
  let a := prefactorData A B
  let c := prefactorData C' B
  let u := exponentOf qzero (qadd s s)
  let d : PTm n := qadd qone qone
  have ra := prefactor_regular (Γ := Γ) A B
  have rc := prefactor_regular (Γ := Γ) C' B
  have ru := GaussianBarnesCanonicalPrefactorExponentDerivative.regular (Γ := Γ) qzero (qadd s s)
  have re := GaussianBarnesCanonicalPrefactorExponentDerivative.regular (Γ := Γ) qzero d
  have rs := constant_regular (Γ := Γ) s
  have plus := GaussianBarnesCanonicalPrefactorExponentDerivative.add_entries qone (twicePoint (center A B) B)
    qzero (qadd s s) qone (twicePoint (center C' B) B) (qadd_zero_right _ qone_canonical) (exponent_step A B C' hB)
  have replace := GaussianGammaRationalWendelBoundary.difference_cross E (addF E E) E E c (addData a u) a a
    rc (add_fast _ _ _ _ ra ru) ra ra (cross_symm _ _ _ _ plus) (cross_refl _ _ ra)
  have cancel := GaussianNamedSumDifference.cancel_added E E a u ra ru
  have smul : Γ ⊢[PRAAx] qmul s d ≐ qadd s s :=
    (GaussianRationalCoefficientScaling.qmul_add s qone qone).eqTrans
      (qadd_congr (qmul_one_right s (ofGaussian_canonical _ _ hB)) (qmul_one_right s (ofGaussian_canonical _ _ hB)))
  have embed := GaussianBarnesCanonicalPrefactorExponentDerivative.scale_entries s qzero d qzero (qadd s s)
    (qmul_zero_right s) smul
  have mul := multiply_cross C C E K s s (exponentOf qzero d) coefficientData rs rs re coefficient_regular
    (cross_refl _ _ rs) basis
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ cancel
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ embed) mul))

theorem actual_Barnes_positive_logarithm_first_prefactor_increment_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let A := var 0
       let C' := var 1
       let B := var 2
       le one B ⟶ crossEquivalent (Diff E E) (multiplyF C K)
         (dd (prefactorData C' B) (prefactorData A B))
         (multiplyData C K (ofGaussian (step A C') B) coefficientData)) :=
  closeUniv 3 (.impI (increment _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor
