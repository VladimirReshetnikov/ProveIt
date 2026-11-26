import IPRADerivations.Analysis.Names.GoldenRatio.GaussianNamedGoldenRatioUniqueness
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# The positive golden-ratio equation in product form

The original named equations (z(z-1)=1) and (z²=z+1) are
equivalent by the named ring laws. On certified positive real names
they characterize the same independent golden-ratio name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast zeroF zero_fast zero_at oneF one_fast one_at)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNamedGoldenRatio (onePoint)
open GaussianNamedGoldenRatioUniqueness (quadratic)
open GaussianRationalHorner (qzero ofGaussian)
open GaussianRationalReciprocal (qone)
open GaussianRationalMetric (qsub)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (scale oneCode)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def minusOne : PTm n := qsub qzero qone
def minusF (f : PR 2) : PR 2 := addF f constantF
def minusData (x : PTm n) : PTm n := addData x minusOne
def productF (f : PR 2) : PR 2 := multiplyF f (minusF f)
def productData (f : PR 2) (x : PTm n) : PTm n := multiplyData f (minusF f) x (minusData x)
def equation (f : PR 2) (x : PTm n) : Fm PTm n :=
  crossEquivalent (productF f) constantF (productData f x) qone

private theorem constant_zero (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF zeroF qzero x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (zero_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_qzero] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) qzero).eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm

private theorem zero_at_other_data (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y :=
  cross_trans zeroF constantF zeroF x qzero y (cross_symm _ _ _ _ (constant_zero x)) (constant_zero y)

private theorem constant_one (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalReciprocal.subst_qone] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) qone).eqTrans (one_at (var 0) (Syn.shift x)).eqSymm

private theorem one_eq : Γ ⊢[PRAAx] (onePoint : PTm n) ≐ qone := by
  exact GaussianRationalHorner.canonical_unique _ _ (scale one oneCode) one
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _)
    (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
    (GaussianRationalReciprocal.qone_represents_scaled one)

private theorem undo_add (f k : PR 2) (x z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN k z) :
    Γ ⊢[PRAAx] crossEquivalent (addF (addF f k) (negativeF k)) f
      (addData (addData x z) (negativeData z)) x := by
  let T := addF k (negativeF k)
  let t := addData z (negativeData z)
  let Z := zeroF
  have neg := negative_fast k z hk
  have assoc := GaussianNameRingLaws.add_associative f k (negativeF k) x z (negativeData z) hf hk neg
  have undo := cross_trans T Z Z t z x (GaussianNameRingLaws.add_negative k z hk) (zero_at_other_data z x)
  have lift := add_cross f f T Z x x t x hf hf (add_fast _ _ _ _ hk neg) (zero_fast _) (cross_refl _ _ hf) undo
  exact cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ lift (GaussianNameRingLaws.add_zero f x hf))

private theorem cancel_add (f g k : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hk : Γ ⊢[PRAAx] pointCN k z)
    (h : Γ ⊢[PRAAx] crossEquivalent (addF f k) (addF g k) (addData x z) (addData y z)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  let H := negativeF k
  let w := negativeData z
  have hw := negative_fast k z hk
  have lift := add_cross (addF f k) (addF g k) H H (addData x z) (addData y z) w w
    (add_fast _ _ _ _ hf hk) (add_fast _ _ _ _ hg hk) hw hw h (cross_refl _ _ hw)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (undo_add f k x z hf hk))
    (cross_trans _ _ _ _ _ _ lift (undo_add g k y z hg hk))

private theorem restore (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (addF (minusF f) constantF) f (addData (minusData x) qone) x := by
  let C := addF constantF constantF
  let d : PTm n := addData minusOne qone
  have hneg : Γ ⊢[PRAAx] pointCN constantF (minusOne : PTm n) := constant_regular _
  have hOne : Γ ⊢[PRAAx] pointCN constantF (qone : PTm n) := constant_regular _
  have a := GaussianNameRingLaws.add_associative f constantF constantF x minusOne qone hf hneg hOne
  have eq : Γ ⊢[PRAAx] GaussianRationalHorner.qadd (minusOne : PTm n) qone ≐ qzero :=
    (GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianNameRingLaws.additive_inverse_value qone)
  have h := cross_trans C constantF zeroF d qzero x (constant_sum _ _ _ eq) (constant_zero x)
  have tr := add_cross f f C zeroF x x d x hf hf (add_fast _ _ _ _ hneg hOne) (zero_fast _)
    (cross_refl _ _ hf) h
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ tr (GaussianNameRingLaws.add_zero f x hf))

theorem rearranged (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) (addF (productF f) f)
      (multiplyData f f x x) (addData (productData f x) x) := by
  let m := minusData x
  let F := minusF f
  let S := addF F constantF
  let s := addData m qone
  have hOne : Γ ⊢[PRAAx] pointCN constantF (qone : PTm n) := constant_regular _
  have hm : Γ ⊢[PRAAx] pointCN F m := add_fast f constantF x minusOne hf (constant_regular _)
  have hs : Γ ⊢[PRAAx] pointCN S s := add_fast F constantF m qone hm hOne
  have forward := GaussianGammaAdjacentCutoff.multiply_cross f f f S x x x s hf hf hf hs
    (cross_refl _ _ hf) (cross_symm _ _ _ _ (restore f x hf))
  have dist := GaussianNameRingLaws.distributive f F constantF x m qone hf hm hOne
  have convert := GaussianGammaAdjacentCutoff.multiply_cross f f constantF oneF x x qone x hf hf hOne (one_fast _)
    (cross_refl _ _ hf) (constant_one x)
  have removed := cross_trans _ _ _ _ _ _ convert (GaussianNameRingLaws.multiply_one f x hf)
  have hp : Γ ⊢[PRAAx] pointCN (productF f) (productData f x) := multiply_fast f F x m hf hm
  have plus := add_cross (productF f) (productF f) (multiplyF f constantF) f (productData f x) (productData f x)
    (multiplyData f constantF x qone) x hp hp (multiply_fast _ _ _ _ hf hOne) hf
    (cross_refl _ _ hp) removed
  exact cross_trans _ _ _ _ _ _ forward (cross_trans _ _ _ _ _ _ dist plus)

private theorem reverse_sum (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (addF f constantF) (addF constantF f) (addData x onePoint) (addData qone x) := by
  have constants := GaussianGammaWeierstrassApproximant.constant_data_cross (onePoint : PTm n) qone (one_eq (Γ := Γ))
  have first := add_cross f f constantF constantF x x onePoint qone hf hf
    (constant_regular _) (constant_regular _) (cross_refl _ _ hf) constants
  exact cross_trans _ _ _ _ _ _ first (GaussianNameRingLaws.add_commutative f constantF x qone hf (constant_regular _))

theorem product_implies_quadratic (f : PR 2) (x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] equation f x) : Γ ⊢[PRAAx] quadratic f x := by
  have hprod := multiply_fast f (minusF f) x (minusData x) hf (add_fast _ _ _ _ hf (constant_regular _))
  have plus := add_cross (productF f) constantF f f (productData f x) qone x x
    hprod (constant_regular _) hf hf he (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ (rearranged f x hf)
    (cross_trans _ _ _ _ _ _ plus (cross_symm _ _ _ _ (reverse_sum f x hf)))

theorem quadratic_implies_product (f : PR 2) (x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (he : Γ ⊢[PRAAx] quadratic f x) : Γ ⊢[PRAAx] equation f x := by
  have hprod := multiply_fast f (minusF f) x (minusData x) hf (add_fast _ _ _ _ hf (constant_regular _))
  have sum := cross_trans (multiplyF f f) (addF f constantF) (addF constantF f)
    (multiplyData f f x x) (addData x onePoint) (addData qone x) he (reverse_sum f x hf)
  have join := cross_trans (addF (productF f) f) (multiplyF f f) (addF constantF f)
    (addData (productData f x) x) (multiplyData f f x x) (addData qone x)
    (cross_symm _ _ _ _ (rearranged f x hf)) sum
  exact cancel_add (productF f) constantF f (productData f x) qone x hprod (constant_regular _) hf join

theorem actual_named_golden_ratio_product_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ Fm.iff (equation f (var 0)) (quadratic f (var 0))) :=
  closeUniv 1 (.impI (Prf.iffI (.impI (product_implies_quadratic f _ Prf.hyp1 Prf.hyp0))
    (.impI (quadratic_implies_product f _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioProduct
