import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# Product rule for constant-coefficient named differences

At a separated native Gaussian increment, this identifies the original
normalized quotient of two constant-scaled names with the sum of a scaled
quotient and a scaled lower endpoint. The coefficients can be arbitrary
raw rational terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianNamedConstantCoefficientDifferenceProduct

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianBoundedConstantProductName (constantF constant_regular constant_at)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (three)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qmul qmul_canonical ofGaussian)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data
local notation "qs" => GaussianNamedDifferenceQuotient.separated
local notation "inv" => GaussianNamedDifferenceQuotient.inverse
local notation "qc" => GaussianNamedDifferenceQuotient.cost
local notation "MF" => multiplyF constantF
local notation "md" => multiplyData constantF

def lhsF (f g : PR 2) : PR 2 := QF (MF f) (MF g)
def lhsData (f g : PR 2) (c1 c0 x y h D : PTm n) : PTm n :=
  qd (MF f) (MF g) (md f c1 x) (md g c0 y) h D

def rhsF (f g : PR 2) : PR 2 := addF (MF (QF f g)) (MF g)
def rhsData (f g : PR 2) (c1 cDelta x y h D : PTm n) : PTm n :=
  addData (md (QF f g) c1 (qd f g x y h D)) (md g cDelta y)

ipra_subst lhsData

ipra_subst rhsData

theorem lhs_regular (f g : PR 2) (c1 c0 x y h D : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] qs h D) : Γ ⊢[PRAAx] pointCN (lhsF f g) (lhsData f g c1 c0 x y h D) :=
  GaussianNamedDifferenceQuotient.name_regular (MF f) (MF g) (md f c1 x) (md g c0 y) h D
    (.andI (multiply_fast constantF f c1 x (constant_regular c1) hx)
      (.andI (multiply_fast constantF g c0 y (constant_regular c0) hy) hs))

theorem rhs_regular (f g : PR 2) (c1 cDelta x y h D : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] qs h D) : Γ ⊢[PRAAx] pointCN (rhsF f g) (rhsData f g c1 cDelta x y h D) :=
  add_fast (MF (QF f g)) (MF g) (md (QF f g) c1 (qd f g x y h D)) (md g cDelta y)
    (multiply_fast constantF (QF f g) c1 (qd f g x y h D) (constant_regular c1)
      (GaussianNamedDifferenceQuotient.name_regular f g x y h D (.andI hx (.andI hy hs))))
    (multiply_fast constantF g cDelta y (constant_regular cDelta) hy)

theorem raw_product_rule (c1 c0 cDelta u v h D : PTm n) (hs : Γ ⊢[PRAAx] qs h D)
    (hDelta : Γ ⊢[PRAAx] qsub c1 c0 ≐ qmul (ofGaussian h D) cDelta) : Γ ⊢[PRAAx]
    qmul (inv h D) (qsub (qmul c1 u) (qmul c0 v)) ≐
      qadd (qmul c1 (qmul (inv h D) (qsub u v))) (qmul cDelta v) := by
  let delta := ofGaussian h D
  let inverse := inv h D
  have coefficient : Γ ⊢[PRAAx] qmul v (qsub c1 c0) ≐ qmul delta (qmul cDelta v) :=
    (qmul_commutative _ _).eqTrans
      ((qmul_congr hDelta (.eqRefl _)).eqTrans (qmul_associative delta cDelta v))
  have split : Γ ⊢[PRAAx] qsub (qmul c1 u) (qmul c0 v) ≐
      qadd (qmul c1 (qsub u v)) (qmul delta (qmul cDelta v)) :=
    (qsub_congr (qmul_commutative c1 u) (qmul_commutative c0 v)).eqTrans
      ((GaussianRationalPowerDifference.product_difference u v c1 c0).eqTrans
        (qadd_congr (qmul_commutative _ _) coefficient))
  have swap := (qmul_associative (Γ := Γ) inverse c1 (qsub u v)).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative _ _) (.eqRefl _)).eqTrans (qmul_associative c1 inverse (qsub u v)))
  have cancel := GaussianRationalInverseQuadraticAlgebra.cancel_nested_product inverse delta (qmul cDelta v)
    (qmul_canonical cDelta v) (GaussianNamedDifferenceQuotient.actual_inverse h D hs)
  exact (qmul_congr (.eqRefl _) split).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add inverse _ _).eqTrans (qadd_congr swap cancel))

private def productBudget (f : PR 2) (c x : PTm n) : PTm n :=
  multiplyModulus constantF f c x+one

def budget (f g : PR 2) (c1 c0 cDelta x y h D : PTm n) : PTm n :=
  (qc (MF f) (MF g) (md f c1 x) (md g c0 y) h D+D*(productBudget f c1 x+productBudget g c0 y))+
    ((three+(productBudget (QF f g) c1 (qd f g x y h D)+productBudget g cDelta y))+
      GaussianGeneralFTAConstants.ceilL1 c1*qc f g x y h D)

private theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2)
    (c1 c0 cDelta x y h D : PTm n) :
    Syn.subst σ (budget f g c1 c0 cDelta x y h D) =
      budget f g (Syn.subst σ c1) (Syn.subst σ c0) (Syn.subst σ cDelta) (Syn.subst σ x)
        (Syn.subst σ y) (Syn.subst σ h) (Syn.subst σ D) := by simp [budget,productBudget,three]

private theorem product_sample_error (f : PR 2) (c x p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (MF f) p (md f c x)) (qmul c (ap2 f p x)) (productBudget f c x) (unit p) :=
  distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF f c x p (constant_regular _) hx)

theorem product_rule_at (f g : PR 2) (c1 c0 cDelta x y h D p : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] qs h D)
    (hDelta : Γ ⊢[PRAAx] qsub c1 c0 ≐ qmul (ofGaussian h D) cDelta) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (lhsF f g) p (lhsData f g c1 c0 x y h D))
      (ap2 (rhsF f g) p (rhsData f g c1 cDelta x y h D)) (budget f g c1 c0 cDelta x y h D) (unit p) := by
  let q := qd f g x y h D
  have hp := unit_positive (Γ := Γ) p
  have upper := multiply_fast constantF f c1 x (constant_regular c1) hx
  have lower := multiply_fast constantF g c0 y (constant_regular c0) hy
  have original := GaussianNamedDifferenceQuotient.sample_error (MF f) (MF g) p
    (md f c1 x) (md g c0 y) h D (.andI upper (.andI lower hs))
  have difference := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp
    (product_sample_error f c1 x p hx) (product_sample_error g c0 y p hy)
  have scaled := GaussianNamedDifferenceQuotient.scale_distance (inv h D) _ _ D _ _ hp
    (GaussianNamedDifferenceQuotient.inverse_bound h D hs) difference
  have lhs := distance_triangle_same _ _ _ _ _ _ hp original scaled
  have native := Prf.andI hx (.andI hy hs)
  have hq := GaussianNamedDifferenceQuotient.name_regular f g x y h D native
  have left := multiply_fast constantF (QF f g) c1 q (constant_regular c1) hq
  have right := multiply_fast constantF g cDelta y (constant_regular cDelta) hy
  have sum := GaussianNameRingLaws.add_sample_error (MF (QF f g)) (MF g)
    (md (QF f g) c1 q) (md g cDelta y) p left right
  have factors := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hp
    (product_sample_error (QF f g) c1 q p hq) (product_sample_error g cDelta y p hy)
  have subtotal := distance_triangle_same _ _ _ _ _ _ hp sum factors
  have quotient := GaussianNamedDifferenceQuotient.sample_error f g p x y h D native
  have factor := GaussianNamedDifferenceQuotient.scale_distance c1 _ _ _ _ _ hp
    (GaussianGeneralFTAConstants.ceil_norm_bound c1) quotient
  have rhs := distance_triangle_same _ _ _ _ _ _ hp subtotal (GaussianNameRingLaws.sum_left_error _ _ _ _ _ hp factor)
  exact GaussianNameRingLaws.through_identity _ _ _ _ _ _ _ hp lhs rhs
    (raw_product_rule c1 c0 cDelta (ap2 f p x) (ap2 g p y) h D hs hDelta)

theorem product_rule (f g : PR 2) (c1 c0 cDelta x y h D : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] qs h D)
    (hDelta : Γ ⊢[PRAAx] qsub c1 c0 ≐ qmul (ofGaussian h D) cDelta) : Γ ⊢[PRAAx]
    crossEquivalent (lhsF f g) (rhsF f g) (lhsData f g c1 c0 x y h D) (rhsData f g c1 cDelta x y h D) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (budget f g c1 c0 cDelta x y h D)
    (lhs_regular f g c1 c0 x y h D hx hy hs) (rhs_regular f g c1 cDelta x y h D hx hy hs) (.allI ?_)
  have sx : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hx.shift
  have sy : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by
    simpa only [Fm.shift,subst_pointCN,Syn.shift] using hy.shift
  have sh : Γ.map Fm.shift ⊢[PRAAx] qs (Syn.shift h) (Syn.shift D) := by
    simpa only [Fm.shift,GaussianNamedDifferenceQuotient.subst_separated,Syn.shift] using hs.shift
  have sd : Γ.map Fm.shift ⊢[PRAAx]
      qsub (Syn.shift c1) (Syn.shift c0) ≐ qmul (ofGaussian (Syn.shift h) (Syn.shift D)) (Syn.shift cDelta) := by
    simpa [Fm.shift,Syn.shift] using hDelta.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_lhsData,subst_rhsData,subst_budget] using
    product_rule_at f g (Syn.shift c1) (Syn.shift c0) (Syn.shift cDelta) (Syn.shift x) (Syn.shift y)
      (Syn.shift h) (Syn.shift D) (var 0) sx sy sh sd

end LeanProofs.IPRA.Analysis.GaussianNamedConstantCoefficientDifferenceProduct
