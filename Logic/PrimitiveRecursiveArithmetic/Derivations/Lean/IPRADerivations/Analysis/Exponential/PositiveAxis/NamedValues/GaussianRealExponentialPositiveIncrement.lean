import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder

/-!
# Actual real exponential order under a nonnegative named increment

The comparison is derived at the exact shared addition clock: a unit
product retimes the left input to that same clock. Its sample is at most
the actual normalized sum because the actual increment sample is
nonnegative. Exponential order and original input properness then retain
both original exponential observations and their independently supplied
radius certificates. No output-order law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRealExponentialPositiveIncrement

open_ipra
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianNamedPositiveExponentialOrder (positiveSamples positive_at sampleOrder realOrder)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (qadd)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev retimedF (f : PR 2) : PR 2 := GaussianBoundedConstantProductName.nameF f
def retimedData (x : PTm n) : PTm n := GaussianBoundedConstantProductName.data two qone x
ipra_subst retimedData

theorem unit_bound : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (qone : PTm n) two one :=
  GaussianCoefficientNameBounds.bounded_radius_mono_one (le_succ_self one) GaussianRationalReciprocal.qone_bounded

theorem retimed_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (retimedF f) (retimedData x) :=
  GaussianBoundedConstantProductName.name_regular f two qone x (.andI hf unit_bound)

theorem retimed_at (f : PR 2) (p x : PTm n) (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    ap2 (retimedF f) p (retimedData x) ≐ ap2 f (GaussianFastValueCut.exponent two p) x :=
  (GaussianBoundedConstantProductName.sample_at f p two qone x).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (real_sample_at f x _ hr).andE₁))

theorem retimed_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx] crossEquivalent f (retimedF f) x (retimedData x) := by
  refine .allI (.allI ?_)
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have fs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (sh x) := by simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realSamples f (sh x) := by simpa [Fm.shift,Syn.shift,sh] using hr.shift.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let t := GaussianFastValueCut.exponent two q
  have coarse := GaussianRationalDistanceOrder.distance_at_earlier_precisions p q p t (le_refl p) (le_add_right _ _)
    (GaussianNameEquivalence.point_at f (sh x) p t fs)
  simpa only [crossEquivalent,subst_retimedData,Syn.shift,sh,p,q] using
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (retimed_at f q (sh x) rs).eqSymm (.eqRefl _) (.eqRefl _) coarse

theorem sum_real_at (f g : PR 2) (p x y : PTm n) (fr : Γ ⊢[PRAAx] realSamples f x)
    (gr : Γ ⊢[PRAAx] realSamples g y) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (addF f g) p (addData x y)) ⋏
      RationalGaussianEmbedding.axis (ap2 (addF f g) p (addData x y)) := by
  let t := GaussianFastValueCut.exponent two p
  have read : Γ ⊢[PRAAx] ap2 (addF f g) p (addData x y) ≐ qadd (ap2 f t x) (ap2 g t y) := (GaussianNameArithmetic.add_at f g x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  exact .andI (GaussianRationalHorner.canonical_congr read (GaussianRationalHorner.qadd_canonical _ _))
    (RationalGaussianEmbedding.axis_congr read.eqSymm
      (RationalGaussianEmbedding.axis_add _ _ (real_sample_at f x t fr).andE₂ (real_sample_at g y t gr).andE₂))

theorem input_sample_order (f g : PR 2) (p x y : PTm n) (fr : Γ ⊢[PRAAx] realSamples f x)
    (gp : Γ ⊢[PRAAx] positiveSamples g y) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 (retimedF f) p (retimedData x))) (fstT (ap2 (addF f g) p (addData x y))) := by
  let t := GaussianFastValueCut.exponent two p
  have order := GaussianPositiveExponentialProduct.scalar_le_add (fstT (ap2 f t x)) (fstT (ap2 g t y))
    (real_sample_at f x t fr).andE₁.andE₂.andE₁ (positive_at g y t gp).andE₂
  have right : Γ ⊢[PRAAx] fstT (ap2 (addF f g) p (addData x y)) ≐ RationalArithmetic.add (fstT (ap2 f t x)) (fstT (ap2 g t y)) := (congrFst ((GaussianNameArithmetic.add_at f g x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))).eqTrans
      (RationalGaussianRealPart.real_add _ _)
  exact RationalArgmin.rationalLE_congr (congrFst (retimed_at f p x fr)).eqSymm right.eqSymm order

theorem exponential_order (f g : PR 2) (R S x y : PTm n)
    (fi : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (_gn : Γ ⊢[PRAAx] pointCN g y)
    (si : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (addF f g) S (addData x y))
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (gp : Γ ⊢[PRAAx] positiveSamples g y) : Γ ⊢[PRAAx]
    realOrder (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.nameF (addF f g))
      (GaussianRadiusExponentialName.data R x) (GaussianRadiusExponentialName.data S (addData x y)) := by
  let F := retimedF f
  let X := retimedData x
  let G := addF f g
  let Y := addData x y
  let U := GaussianNameBounds.U F X
  let V := U+S
  have fn := retimed_regular f x fi.andE₁
  have ri := GaussianGammaFiniteApproximantName.exponential_input F X fn
  have lwide := GaussianExponentialRadiusIndependence.input_widen F U V X ri (le_add_right U S)
  have rwide := GaussianExponentialRadiusIndependence.input_widen G S V Y si (le_add_left S U)
  have freal : Γ ⊢[PRAAx] realSamples F X := by
    refine .allI ?_
    have rs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using fr.shift
    have read := retimed_at f (var 0) (Syn.shift x) rs
    simpa only [realSamples,Syn.shift,subst_retimedData,X,F] using
      Prf.andI (GaussianRationalHorner.canonical_congr read (real_sample_at f (Syn.shift x) _ rs).andE₁)
        (RationalGaussianEmbedding.axis_congr read.eqSymm (real_sample_at f (Syn.shift x) _ rs).andE₂)
  have greal : Γ ⊢[PRAAx] realSamples G Y := by
    refine .allI ?_
    have fs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using fr.shift
    have gs : Γ.map Fm.shift ⊢[PRAAx] realSamples g (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using gr.shift
    simpa only [realSamples,Syn.shift,GaussianNameArithmetic.subst_addData,G,Y] using sum_real_at f g (var 0) (Syn.shift x) (Syn.shift y) fs gs
  have ordered : Γ ⊢[PRAAx] sampleOrder F G X Y := by
    refine .allI ?_
    have fs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using fr.shift
    have gs : Γ.map Fm.shift ⊢[PRAAx] positiveSamples g (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using gp.shift
    simpa only [sampleOrder,Syn.shift,subst_retimedData,GaussianNameArithmetic.subst_addData,F,G,X,Y] using
      input_sample_order f g (var 0) (Syn.shift x) (Syn.shift y) fs gs
  have exactOrder := GaussianSignedNameExponentialOrder.original_signed_name_order F G V X Y lwide rwide freal greal ordered
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper f F R V x X fi lwide (retimed_cross f x fi.andE₁ fr)
  have right := GaussianExponentialRadiusIndependence.same_input_cross G V S Y rwide si
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left right exactOrder

theorem actual_real_exponential_nonnegative_increment_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRadiusExponentialName.input f (var 0) (var 2) ⟶ pointCN g (var 3) ⟶
      GaussianRadiusExponentialName.input (addF f g) (var 1) (addData (var 2) (var 3)) ⟶
      realSamples f (var 2) ⟶ realSamples g (var 3) ⟶ positiveSamples g (var 3) ⟶
      realOrder (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.nameF (addF f g))
        (GaussianRadiusExponentialName.data (var 0) (var 2)) (GaussianRadiusExponentialName.data (var 1) (addData (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI
    (exponential_order f g _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianRealExponentialPositiveIncrement
