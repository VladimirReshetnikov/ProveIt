import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmExponentialIdentity
import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianNamedExponentialQuarterUniqueness
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# Multiplicative increments of the original local Mercator names

If the three half-disk arguments satisfy
`(1+a)(1+b)=1+c`, the actual local logarithm of `1+c` is the sum
of the two actual local logarithms. Every observation of the difference
lies in the radius-three disk, so the existing exponential injectivity
applies to these exact names.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmMultiplicativeIncrement

open_ipra
open GaussianFiniteLogarithmCompositionTail (linearValue)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLocalLogarithmName (source point pointF data point_unit_disk name_regular original_exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedExponentialQuarterUniqueness (lateRadius)
open GaussianRationalHorner (ofGaussian qmul qmul_canonical)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_sum)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => pointF
local notation "S" => addF L L
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "DF" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "base" z:max d:max => linearValue (ofGaussian z d)

private theorem constant_product (a b : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) constantF
      (multiplyData constantF constantF a b) (qmul a b) := by
  apply equal_samples_cross _ _ _ _ (multiply_fast _ _ _ _ (constant_regular a) (constant_regular b)) (constant_regular _)
  refine .allI ?_
  let x := Syn.shift a
  let y := Syn.shift b
  let p : PTm (n+1) := var 0
  let s := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF constantF x y) p
  have raw : Γ.map Fm.shift ⊢[PRAAx] ap2 (multiplyF constantF constantF) p
      (multiplyData constantF constantF x y) ≐ qmul x y :=
    (GaussianNameArithmetic.multiply_at constantF constantF x y p).eqTrans
      ((GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)).eqTrans
        (qmul_congr (constant_at s x) (constant_at s y)))
  simpa only [pointwiseEqual,x,y,p,Syn.shift,GaussianNameArithmetic.subst_multiplyData,GaussianRationalHorner.subst_qmul] using
    raw.eqTrans (constant_at p (qmul x y)).eqSymm

theorem exponential_base_cross (z R D : PTm n) (hs : Γ ⊢[PRAAx] source z R D) :
    Γ ⊢[PRAAx] crossEquivalent (E L) constantF (ed one (data z R D)) (base z D) := by
  let x := data z R D
  let a := ofGaussian z D
  let G := GaussianFiniteLogarithmCompositionName.constantF
  have target : Γ ⊢[PRAAx] crossEquivalent G constantF a (linearValue a) := by
    apply equal_samples_cross G constantF a (linearValue a) (GaussianFiniteLogarithmCompositionName.constant_regular _)
      (constant_regular _)
    refine .allI ?_
    let p : PTm (n+1) := var 0
    let y := Syn.shift a
    simpa only [pointwiseEqual,Syn.shift,y,p,G,GaussianFiniteLogarithmCompositionName.constant,
      GaussianFiniteLogarithmCompositionTail.subst_linearValue] using
      (GaussianFiniteLogarithmCompositionName.constant_at p y).eqTrans (constant_at p (linearValue y)).eqSymm
  let U := GaussianUnitDiskExponentialName.nameF L
  exact cross_trans _ _ _ _ _ _ (cross_symm U (E L) _ _
    (GaussianExponentialRadiusIndependence.original_unit_cross L x (original_exponential_input z R D hs)))
    (cross_trans _ _ _ _ _ _ (GaussianLocalLogarithmExponentialIdentity.source_cross z R D hs) target)

private theorem difference_bound_at (p a A I b B J c C K : PTm n)
    (ha : Γ ⊢[PRAAx] source a A I) (hb : Γ ⊢[PRAAx] source b B J) (hc : Γ ⊢[PRAAx] source c C K) :
    Γ ⊢[PRAAx] bounded (ap2 (DF S L) p (dd (addData (data a A I) (data b B J)) (data c C K))) (num 3) one := by
  let x := data a A I
  let y := data b B J
  let z := data c C K
  let xy := addData x y
  let s := GaussianFastValueCut.exponent two p
  let t := GaussianFastValueCut.exponent two s
  let u := GaussianFastValueCut.exponent (one+one) s
  have addRead := GaussianExponentialReference.add_sample (Γ := Γ) L L x y s
  have addBound : Γ ⊢[PRAAx] bounded (ap2 S s xy) two one :=
    bound_congr addRead.eqSymm (by ipra_ring) (by ipra_ring)
      (bounded_sum _ _ one one one one (le_refl one) (le_refl one) (point_unit_disk t a A I ha) (point_unit_disk t b B J hb))
  have negRead := GaussianRealNameExponentialUnitReflection.negative_sample_at (Γ := Γ) L s z
  have negBound : Γ ⊢[PRAAx] bounded (ap2 (negativeF L) s (negativeData z)) one one :=
    bound_congr negRead.eqSymm (.eqRefl _) (.eqRefl _) (bounded_negative _ _ _ (le_refl one) (point_unit_disk u c C K hc))
  have observed := GaussianExponentialReference.add_sample (Γ := Γ) S (negativeF L) xy (negativeData z) p
  exact bound_congr observed.eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_sum _ _ two one one one (le_refl one) (le_refl one) addBound negBound)

private theorem difference_late (a A I b B J c C K : PTm n)
    (ha : Γ ⊢[PRAAx] source a A I) (hb : Γ ⊢[PRAAx] source b B J) (hc : Γ ⊢[PRAAx] source c C K) :
    Γ ⊢[PRAAx] lateRadius (DF S L) (dd (addData (data a A I) (data b B J)) (data c C K)) zero := by
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := le zero (var 0) :: Γ.map Fm.shift
  have ha' : Δ ⊢[PRAAx] source (sh a) (sh A) (sh I) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift.wk
  have hb' : Δ ⊢[PRAAx] source (sh b) (sh B) (sh J) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hb.shift.wk
  have hc' : Δ ⊢[PRAAx] source (sh c) (sh C) (sh K) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift.wk
  simpa only [lateRadius,Syn.shift,sh,GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_addData,
    GaussianLocalLogarithmName.subst_data,ConciseIPRA.PTm.subst_zero] using
    difference_bound_at (var 0) (sh a) (sh A) (sh I) (sh b) (sh B) (sh J) (sh c) (sh C) (sh K) ha' hb' hc'

theorem add_cross (a A I b B J c C K : PTm n)
    (ha : Γ ⊢[PRAAx] source a A I) (hb : Γ ⊢[PRAAx] source b B J) (hc : Γ ⊢[PRAAx] source c C K)
    (he : Γ ⊢[PRAAx] qmul (base a I) (base b J) ≐ base c K) :
    Γ ⊢[PRAAx] crossEquivalent S L (addData (data a A I) (data b B J)) (data c C K) := by
  let x := data a A I
  let y := data b B J
  let z := data c C K
  let X := ed one x
  let Y := ed one y
  let P := multiplyF (E L) (E L)
  let Q := multiplyF constantF constantF
  let d := addData x y
  let e := multiplyData (E L) (E L) X Y
  let f := multiplyData constantF constantF (base a I) (base b J)
  let u := GaussianExponentialRadiusIndependence.radius_one_input (Γ := Γ) L
  have ax := u x (original_exponential_input a A I ha)
  have ay := u y (original_exponential_input b B J hb)
  have az := u z (original_exponential_input c C K hc)
  have axr := GaussianRadiusExponentialName.name_regular L one x ax
  have ayr := GaussianRadiusExponentialName.name_regular L one y ay
  have left := GaussianExponentialAddition.exponential_add_cross L L one x y (le_refl one) ax ay
  have mul := GaussianGammaAdjacentCutoff.multiply_cross (E L) constantF (E L) constantF X (base a I) Y (base b J)
    axr (constant_regular _) ayr (constant_regular _) (exponential_base_cross a A I ha) (exponential_base_cross b B J hb)
  let w := qmul (base a I) (base b J)
  have eq := GaussianGammaInputProperness.code_data_cross constantF w (base c K) (constant_regular _) (constant_regular _) he
  have main : Γ ⊢[PRAAx] crossEquivalent (E S) (E L) (ed (one+one) d) (ed one z) :=
    cross_trans (E S) P (E L) _ e _ (cross_symm _ _ _ _ left)
      (cross_trans P Q (E L) e f _ mul
        (cross_trans Q constantF (E L) f w _ (constant_product (base a I) (base b J))
          (cross_trans constantF constantF (E L) w (base c K) _ eq (cross_symm _ _ _ _ (exponential_base_cross c C K hc)))))
  exact GaussianNamedExponentialQuarterUniqueness.injective S L (one+one) one d z zero
    (GaussianExponentialReference.add_input L L one x y ax ay) az
    (difference_late a A I b B J c C K ha hb hc) main

theorem increment_cross (a A I b B J c C K : PTm n)
    (ha : Γ ⊢[PRAAx] source a A I) (hb : Γ ⊢[PRAAx] source b B J) (hc : Γ ⊢[PRAAx] source c C K)
    (he : Γ ⊢[PRAAx] qmul (base a I) (base b J) ≐ base c K) :
    Γ ⊢[PRAAx] crossEquivalent (DF L L) L (dd (data c C K) (data a A I)) (data b B J) := by
  let x := data a A I
  let y := data b B J
  let z := data c C K
  have hx := name_regular a A I ha
  have hy := name_regular b B J hb
  have hz := name_regular c C K hc
  have e := add_cross b B J a A I c C K hb ha hc ((qmul_commutative _ _).eqTrans he)
  exact cross_trans (DF L L) (DF S L) L _ (dd (addData y x) x) _
    (GaussianNamedDifferenceQuotientProperness.difference_proper L S L L z (addData y x) x x hz
      (add_fast _ _ _ _ hy hx) hx hx (cross_symm _ _ _ _ e) (cross_refl _ _ hx))
    (GaussianNamedStrictOrderDifference.sum_sub_right L L y x hy hx)

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmMultiplicativeIncrement
