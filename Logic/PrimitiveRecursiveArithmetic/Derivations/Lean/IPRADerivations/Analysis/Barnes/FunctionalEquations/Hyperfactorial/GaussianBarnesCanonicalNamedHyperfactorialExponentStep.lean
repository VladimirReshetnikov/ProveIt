import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalNamedHyperfactorial
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Recurrence.GaussianLogGammaEulerNamedRecurrence
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-! # The hyperfactorial exponent recurrence on actual regular names -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialExponentStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalNamedHyperfactorial (exponentF exponentData exponent_regular)
open GaussianBarnesCanonicalOrdinaryUpperGrowth (minusOne)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianLogGammaEulerNamed (source)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative add_negative zeroF zero_fast zero_at
  multiply_one_left oneF one_fast one_at negativeF negativeData negative_fast distributive right_distributive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianRationalHorner (qadd qzero ofGaussian)
open GaussianRationalSyntheticDivision (qone)
open ComplexLogarithmRemainder (oneCode zeroCode scale)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianLogGammaEulerNamed.nameF
local notation "Ld" => GaussianLogGammaEulerNamed.data
local notation "T" => GaussianRightHalfPlaneLogarithmNamed.nameF
local notation "Td" => GaussianRightHalfPlaneLogarithmNamed.data
local notation "Df" => GaussianNamedDifference.nameF
local notation "Dd" => GaussianNamedDifference.data

def stepExponentF (f : PR 2) : PR 2 := multiplyF f (T f)
def stepExponentData (f : PR 2) (x M R : PTm n) : PTm n := multiplyData f (T f) x (Td x M R)
def incrementF (f : PR 2) : PR 2 := addF (L f) (stepExponentF f)
def incrementData (f : PR 2) (x M R : PTm n) : PTm n := addData (Ld x M R) (stepExponentData f x M R)
def totalF (f : PR 2) : PR 2 := addF (exponentF f) (incrementF f)
def totalData (f : PR 2) (x M R : PTm n) : PTm n := addData (exponentData f x M R) (incrementData f x M R)

private theorem unit_sum : Γ ⊢[PRAAx] qadd (qone : PTm n) minusOne ≐ qzero := by
  let m : PTm n := ComplexLogarithmRemainder.neg oneCode
  let a := ComplexLogarithmRemainder.add (scale one oneCode) m
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal a zeroCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [a,m,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,GaussianRootAlgebra.re_zero,
        GaussianRootAlgebra.im_zero] <;> ipra_simps <;> ring
  have hsum := GaussianRationalHorner.qadd_represents qone minusOne (scale one oneCode) m one (le_refl one)
    (GaussianRationalReciprocal.qone_represents_scaled (Γ := Γ) one)
    (GaussianRationalHorner.ofGaussian_represents m one (le_refl one))
  exact GaussianRationalHorner.canonical_unique _ _ zeroCode one (GaussianRationalHorner.qadd_canonical _ _)
    GaussianRationalSyntheticDivision.qzero_canonical (le_refl _)
    (GaussianRationalHorner.represents_congr (.eqRefl _) eq (.eqRefl _) hsum) (GaussianRationalHorner.zero_represents one)

private theorem zero_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF zeroF qzero x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (zero_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_qzero] using
    (constant_at (var 0) qzero).eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm

private theorem one_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent constantF oneF qone x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (one_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalSyntheticDivision.subst_qone] using
    (constant_at (var 0) qone).eqTrans (one_at (var 0) (Syn.shift x)).eqSymm

private theorem cancel_constants (f : PR 2) (x a b : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x)
    (h : Γ ⊢[PRAAx] qadd a b ≐ qzero) :
    Γ ⊢[PRAAx] crossEquivalent (addF (addF f constantF) constantF) f (addData (addData x a) b) x := by
  let C := constantF
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have sum := cross_trans _ _ _ _ _ _ (constant_sum a b qzero h) (zero_constant x)
  have replace := add_cross f f (addF C C) zeroF x x (addData a b) x
    hx hx (add_fast _ _ _ _ ha hb) (zero_fast x) (cross_refl _ _ hx) sum
  exact cross_trans _ _ _ _ _ _ (add_associative f C C x a b hx ha hb)
    (cross_trans _ _ _ _ _ _ replace (GaussianNameRingLaws.add_zero f x hx))

theorem shifted_center_is_input (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (addF (shiftF f) constantF) f (addData (shiftData x) minusOne) x :=
  cancel_constants f x qone minusOne hx unit_sum

theorem restored_center (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (shiftF (addF f constantF)) f (shiftData (addData x minusOne)) x :=
  cancel_constants f x minusOne qone hx
    ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans unit_sum)

private theorem add_back (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (addF (Df f g) g) f (addData (Dd x y) y) x := by
  let neg := negativeF g
  let w := negativeData y
  have hr := negative_fast g y hg
  have hb := add_fast neg g w y hr hg
  have comm := add_commutative neg g w y hr hg
  have canc := cross_trans _ _ _ _ _ _ comm (add_negative g y hg)
  have zs : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF y x := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast y) (zero_fast x)
    refine .allI ?_
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
      (zero_at (var 0) (Syn.shift y)).eqTrans (zero_at (var 0) (Syn.shift x)).eqSymm
  have replace := add_cross f f (addF neg g) zeroF x x (addData w y) x
    hf hf hb (zero_fast x) (cross_refl _ _ hf) (cross_trans _ _ _ _ _ _ canc zs)
  exact cross_trans _ _ _ _ _ _ (add_associative f neg g x w y hf hr hg)
    (cross_trans _ _ _ _ _ _ replace (GaussianNameRingLaws.add_zero f x hf))

theorem logarithm_sum (f : PR 2) (x M R S : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlane.radius (shiftF f) (shiftData x)) S) :
    Γ ⊢[PRAAx] crossEquivalent (L (shiftF f)) (addF (L f) (T f)) (Ld (shiftData x) M S)
      (addData (Ld x M R) (Td x M R)) := by
  let fs := shiftF f
  let xs := shiftData x
  let u := Ld x M R
  let v := Ld xs M S
  let w := Td x M R
  have hu := GaussianLogGammaEulerNamed.name_regular f x M R h
  have hv := GaussianLogGammaEulerNamed.name_regular fs xs M S
    (GaussianLogGammaEulerShiftedChart.shift_source f x M R S h hS)
  have hw := GaussianRightHalfPlaneLogarithmNamed.name_regular f x M R h
  have diff := GaussianNamedDifference.name_regular (L fs) (L f) v u hv hu
  have move := add_cross (Df (L fs) (L f)) (T f) (L f) (L f) (Dd v u) w u u diff hw hu hu
    (GaussianLogGammaEulerNamedRecurrence.recurrence f x M R S h hS) (cross_refl _ _ hu)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (add_back (L fs) (L f) v u hv hu))
    (cross_trans _ _ _ _ _ _ move (add_commutative (T f) (L f) w u hw hu))

theorem step_exponent_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (stepExponentF f) (stepExponentData f x M R) :=
  multiply_fast _ _ _ _ h.andE₁.andE₁ (GaussianRightHalfPlaneLogarithmNamed.name_regular f x M R h)

private theorem weighted_log_split (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (L f)) (addF (exponentF f) (L f))
      (multiplyData f (L f) x (Ld x M R)) (addData (exponentData f x M R) (Ld x M R)) := by
  let F := addF f constantF
  let y := addData x minusOne
  let l := Ld x M R
  let e := exponentData f x M R
  have hx := h.andE₁.andE₁
  have hy := add_fast f constantF x minusOne hx (constant_regular _)
  have hl := GaussianLogGammaEulerNamed.name_regular f x M R h
  have h1 := constant_regular (Γ := Γ) (qone : PTm n)
  have replace := multiply_cross f (shiftF F) (L f) (L f) x (shiftData y) l l
    hx (add_fast F constantF y qone hy h1) hl hl
    (cross_symm _ _ _ _ (restored_center f x hx)) (cross_refl _ _ hl)
  have dist := right_distributive F constantF (L f) y qone l hy h1 hl
  have unit := multiply_cross constantF oneF (L f) (L f) qone l l l
    h1 (one_fast l) hl hl (one_constant l) (cross_refl _ _ hl)
  have collapse := cross_trans _ _ _ _ _ _ unit (multiply_one_left (L f) l hl)
  have he := exponent_regular f x M R h
  have together := add_cross (exponentF f) (exponentF f) (multiplyF constantF (L f)) (L f) e e
    (multiplyData constantF (L f) qone l) l he he (multiply_fast _ _ _ _ h1 hl) hl (cross_refl _ _ he) collapse
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ dist together)

theorem exponent_step (f : PR 2) (x M R S : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlane.radius (shiftF f) (shiftData x)) S) :
    Γ ⊢[PRAAx] crossEquivalent (exponentF (shiftF f)) (totalF f) (exponentData (shiftF f) (shiftData x) M S)
      (totalData f x M R) := by
  let fs := shiftF f
  let xs := shiftData x
  let l := Ld x M R
  let ls := Ld xs M S
  let t := Td x M R
  let r := stepExponentData f x M R
  have hx := h.andE₁.andE₁
  have hs := GaussianLogGammaEulerShiftedChart.shift_source f x M R S h hS
  have h1 := add_fast fs constantF xs minusOne hs.andE₁.andE₁ (constant_regular _)
  have hl := GaussianLogGammaEulerNamed.name_regular f x M R h
  have hls := GaussianLogGammaEulerNamed.name_regular fs xs M S hs
  have ht := GaussianRightHalfPlaneLogarithmNamed.name_regular f x M R h
  have replace := multiply_cross (addF fs constantF) f (L fs) (addF (L f) (T f))
    (addData xs minusOne) x ls (addData l t) h1 hx hls (add_fast _ _ _ _ hl ht)
    (shifted_center_is_input f x hx) (logarithm_sum f x M R S h hS)
  have expand := distributive f (L f) (T f) x l t hx hl ht
  have he := exponent_regular f x M R h
  have hr := step_exponent_regular f x M R h
  have split := add_cross (multiplyF f (L f)) (addF (exponentF f) (L f)) (stepExponentF f) (stepExponentF f)
    (multiplyData f (L f) x l) (addData (exponentData f x M R) l) r r
    (multiply_fast _ _ _ _ hx hl) (add_fast _ _ _ _ he hl) hr hr
    (weighted_log_split f x M R h) (cross_refl _ _ hr)
  have group := add_associative (exponentF f) (L f) (stepExponentF f) (exponentData f x M R) l r he hl hr
  exact cross_trans _ _ _ _ _ _ replace
    (cross_trans _ _ _ _ _ _ expand (cross_trans _ _ _ _ _ _ split group))

theorem actual_original_named_Barnes_hyperfactorial_exponent_step_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0; let M := var 1; let R := var 2; let S := var 3
       source f x M R ⟶ le (GaussianNamedRightHalfPlane.radius (shiftF f) (shiftData x)) S ⟶
         crossEquivalent (exponentF (shiftF f)) (totalF f) (exponentData (shiftF f) (shiftData x) M S)
          (totalData f x M R)) :=
  closeUniv 4 (.impI (.impI (exponent_step f _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialExponentStep
