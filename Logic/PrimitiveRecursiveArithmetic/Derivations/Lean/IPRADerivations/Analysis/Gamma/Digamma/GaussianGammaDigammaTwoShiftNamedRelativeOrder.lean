import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftNamedLogOrder
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftNamedExponential

/-!
# The exact relative two-shift bound on regular real names

When the original real names satisfy 4 A(A+1) ≤ x, each repaired chart
also satisfies the exact relative-error threshold. Uniform exponential
readback and affine cap readback remove the remaining dyadic errors
from the original normalized Gamma ratio between 1 ± 8 A(A+1)/x.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedRelativeOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftNamedWindow (source orders sum_rate constant_self_rate)
open GaussianGammaDigammaTwoShiftNamedRepairedChart (actual_chart chart capBudget quotientBudget sizeOrder)
open GaussianGammaDigammaTwoShiftRationalWindow (coefficient positive_endpoint)
open GaussianGammaDigammaTwoShiftExponentialCaps (lower upperPoint)
open GaussianGammaDigammaTwoShiftNamedLogOrder (negative_constant_rate)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalHorner (positive_product qadd)
open GaussianRationalMetric (qnegative)
open GaussianRationalReciprocal (qone)
open RationalValueBounds (upper)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianGammaDigammaTwoShiftNamedBinding.quotientLogF
local notation "FD" => GaussianGammaDigammaTwoShiftNamedBinding.quotientLogData
local notation "E" => GaussianGammaDigammaTwoShiftNamedBinding.quotientF
local notation "ED" => GaussianGammaDigammaTwoShiftNamedBinding.quotientData
local notation "C" => GaussianGammaDigammaTwoShiftNamedCap.nameF
local notation "CD" => GaussianGammaDigammaTwoShiftNamedCap.data
local notation "Q" => GaussianGammaDigammaTwoShiftBinding.quotientLogF
local notation "QD" => GaussianGammaDigammaTwoShiftBinding.quotientLogData
local notation "Z" => GaussianGammaDigammaTwoShiftBinding.quotientF
local notation "ZD" => GaussianGammaDigammaTwoShiftBinding.quotientData
local notation "U" => GaussianNameBounds.U
local notation "expF" => GaussianRadiusExponentialName.nameF
local notation "expD" => GaussianGammaFiniteApproximantName.exponentialInputData

def doubledF (g : PR 2) : PR 2 := addF g g
def doubledData (x : PTm n) : PTm n := addData x x
def lowerF (g : PR 2) : PR 2 := addF constantF (negativeF (doubledF g))
def upperF (g : PR 2) : PR 2 := addF constantF (doubledF g)
def lowerData (x : PTm n) : PTm n := addData qone (negativeData (doubledData x))
def upperData (x : PTm n) : PTm n := addData qone (doubledData x)

@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (lowerData x) = lowerData (Syn.subst σ x) := by simp [lowerData,doubledData]

@[simp] theorem subst_upperData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (upperData x) = upperData (Syn.subst σ x) := by simp [upperData,doubledData]

private theorem doubled_rate (g : PR 2) (x K B A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D) (hg : Γ ⊢[PRAAx] pointCN g x)
    (h : Γ ⊢[PRAAx] independentRate g constantF x (fraction K B) A D) :
    Γ ⊢[PRAAx] independentRate (doubledF g) constantF (doubledData x) (fraction (two*K) B) (A+A) D := by
  have eq := (GaussianRationalQuadratureSquareCells.fraction_add_same K K B hb).eqTrans
    (GaussianStirlingRationalTelescopers.fraction_same (K+K) B (two*K) B hb hb (by ipra_ring))
  exact sum_rate g g x x (fraction K B) (fraction K B) (fraction (two*K) B) A A D hg hg hd h h eq

theorem lower_rate (g : PR 2) (x K B A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D) (hg : Γ ⊢[PRAAx] pointCN g x)
    (h : Γ ⊢[PRAAx] independentRate g constantF x (fraction K B) A D) :
    Γ ⊢[PRAAx] independentRate (lowerF g) constantF (lowerData x) (lower K B) (A+A) D := by
  let G := doubledF g
  let X := doubledData x
  let r := fraction (two*K) B
  have reg : Γ ⊢[PRAAx] pointCN G X := add_fast _ _ _ _ hg hg
  have twoRate := doubled_rate g x K B A D hb hd hg h
  have neg := negative_constant_rate G X r (A+A) D hd reg twoRate
  have hNeg := GaussianNameRingLaws.negative_fast G X reg
  have raw := sum_rate constantF (negativeF G) qone (negativeData X) qone (qnegative r) (lower K B) zero (A+A) D
    (constant_regular _) hNeg hd (constant_self_rate _ _ hd) neg (.eqRefl _)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ (zero+(A+A)) D (A+A) D (zero_add _) (.eqRefl _) raw

theorem upper_rate (g : PR 2) (x K B A D : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D) (hg : Γ ⊢[PRAAx] pointCN g x)
    (h : Γ ⊢[PRAAx] independentRate g constantF x (fraction K B) A D) :
    Γ ⊢[PRAAx] independentRate (upperF g) constantF (upperData x) (upperPoint K B) (A+A) D := by
  let G := doubledF g
  let X := doubledData x
  let r := fraction (two*K) B
  have reg : Γ ⊢[PRAAx] pointCN G X := add_fast _ _ _ _ hg hg
  have twoRate := doubled_rate g x K B A D hb hd hg h
  have raw := sum_rate constantF G qone X qone r (upperPoint K B) zero (A+A) D
    (constant_regular _) reg hd (constant_self_rate _ _ hd) twoRate (.eqRefl _)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ (zero+(A+A)) D (A+A) D (zero_add _) (.eqRefl _) raw

private theorem exponential_rate (f g : PR 2) (x y A D : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hd : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] independentRate (expF f) (expF g) (expD f x) (expD g y) (factor (U f x+A+two)*A) D := by
  let R := U f x+A+two
  let P := GaussianRadiusExponentialName.data R x
  let Q' := GaussianRadiusExponentialName.data R y
  have hX := GaussianGammaFiniteApproximantName.exponential_input f x hf
  have hY := GaussianGammaFiniteApproximantName.exponential_input g y hg
  have hc := GaussianExponentialRadiusIndependence.input_widen f (U f x) R x hX
    (le_trans (le_add_right _ _) (le_add_right _ _))
  have he : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input g R y :=
    .andI hg (GaussianNamedUniformRateClosure.sample_bound_of_rate g f y x (U f x) A D hd
      (GaussianNameBounds.all_samples_bounded _ _ hf) (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ hd h))
  have near := GaussianRadiusExponentialLipschitzRate.independent_rate f g R x y A D
    (.andI hd (.andI hc (.andI he h)))
  exact GaussianNamedRateTransport.transport (expF f) (expF g) (expF f) (expF g) P Q' (expD f x) (expD g y)
    (factor R*A) D hd near (GaussianExponentialRadiusIndependence.same_input_cross f (U f x) R x hX hc)
    (GaussianExponentialRadiusIndependence.same_input_cross g (U g y) R y hY he)

def relativeBudget (f g h j : PR 2) (x y z w M : PTm n) : PTm n :=
  let A := quotientBudget f g h j x y z w M
  factor (U (F f g h) (FD f g h x y z M)+A+two)*A

def relativeRate (f g h j : PR 2) (x y z w M : PTm n) : Fm PTm n :=
  realOrder (lowerF (C f j)) (E f g h) (lowerData (CD f j x w M)) (ED f g h x y z M) ⋏
    realOrder (E f g h) (upperF (C f j)) (ED f g h x y z M) (upperData (CD f j x w M))

def frozenRate (f g h j : PR 2) (s x y z w M : PTm n) : Fm PTm n :=
  let a := chart f g h j s x y z w M
  let k := coefficient a.denominator a.shiftBound
  let b := a.base*a.denominator
  let v := ED f g h x y z M
  let c := CD f j x w M
  let A := relativeBudget f g h j x y z w M
  let B := capBudget f j x w M
  independentRate (E f g h) Z v (ZD a.base a.denominator a.left a.right) A (unit s) ⋏
    (independentRate (lowerF (C f j)) constantF (lowerData c) (lower k b) (B+B) (unit s) ⋏
      (independentRate (upperF (C f j)) constantF (upperData c) (upperPoint k b) (B+B) (unit s) ⋏
        GaussianGammaDigammaTwoShiftRationalRate.relativeRate a.base a.denominator a.left a.right a.shiftBound))

theorem frozen_relative_rate (f g h j : PR 2) (s x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w)
    (hsize : Γ ⊢[PRAAx] sizeOrder f j x w) :
    Γ ⊢[PRAAx] frozenRate f g h j s x y z w M := by
  let a := chart f g h j s x y z w M
  let k := coefficient a.denominator a.shiftBound
  let b := a.base*a.denominator
  let B := capBudget f j x w M
  have read := actual_chart f g h j s x y z w M hs ho
  have hD := unit_positive (Γ := Γ) s
  have input := read.andE₁
  have hf := input.andE₁
  have hb := hf.andE₂
  have bp := positive_product _ _ hf.andE₁ hb
  have hc := positive_endpoint a.base a.denominator a.shiftBound a.left hb input.andE₂.andE₂.andE₁ input.andE₂.andE₂.andE₂.andE₁
  have hd := positive_endpoint a.base a.denominator a.shiftBound a.right hb input.andE₂.andE₂.andE₁ input.andE₂.andE₂.andE₂.andE₂
  have actual : Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftNamedFreeze.source f g h x y z M :=
    .andI hs.andE₁ (.andI hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁)
  have realLog := GaussianGammaDigammaTwoShiftNamedBinding.quotient_log_regular f g h x y z M actual
  have chartLog := GaussianGammaDigammaTwoShiftBinding.quotient_log_regular a.base a.denominator a.left a.right hf hc hd
  have exp := exponential_rate (F f g h) Q (FD f g h x y z M) (QD a.base a.denominator a.left a.right)
    (quotientBudget f g h j x y z w M) (unit s) realLog chartLog hD read.andE₂.andE₁
  have cap := GaussianGammaDigammaTwoShiftNamedCap.name_regular f j x w M hs.andE₁ hs.andE₂.andE₂.andE₂.andE₁.andE₁
  have atCap := read.andE₂.andE₂.andE₁
  have rel := GaussianGammaDigammaTwoShiftRationalRate.two_shift_relative_rate a.base a.denominator a.left a.right a.shiftBound
    input (read.andE₂.andE₂.andE₂.impE hsize)
  exact .andI exp (.andI (lower_rate (C f j) (CD f j x w M) k b B (unit s) bp hD cap atCap)
    (.andI (upper_rate (C f j) (CD f j x w M) k b B (unit s) bp hD cap atCap) rel))

theorem lower_observation (f g h j : PR 2) (p q x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w)
    (hsize : Γ ⊢[PRAAx] sizeOrder f j x w) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (lowerF (C f j)) p (lowerData (CD f j x w M))))
      (fstT (ap2 (E f g h) q (ED f g h x y z M))) (unit p+unit q) (unit p*unit q) := by
  let A := relativeBudget f g h j x y z w M
  let B := capBudget f j x w M
  let c := lowerData (CD f j x w M)
  let v := ED f g h x y z M
  let G := lowerF (C f j)
  let s := GaussianNamedCofinalOrder.clock G (E f g h) p q c v (B+B) A
  let a := chart f g h j s x y z w M
  let b := lower (coefficient a.denominator a.shiftBound) (a.base*a.denominator)
  let d := ZD a.base a.denominator a.left a.right
  have read := frozen_relative_rate f g h j s x y z w M hs ho hsize
  have right := GaussianNamedRateComposition.symmetric (E f g h) Z v d A (unit s) (unit_positive s) read.andE₁
  exact GaussianNamedCofinalOrder.observation G constantF Z (E f g h) p q c b d v (B+B) A
    read.andE₂.andE₁ right read.andE₂.andE₂.andE₂.andE₁

theorem upper_observation (f g h j : PR 2) (p q x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w)
    (hsize : Γ ⊢[PRAAx] sizeOrder f j x w) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (E f g h) p (ED f g h x y z M)))
      (fstT (ap2 (upperF (C f j)) q (upperData (CD f j x w M)))) (unit p+unit q) (unit p*unit q) := by
  let A := relativeBudget f g h j x y z w M
  let B := capBudget f j x w M
  let c := upperData (CD f j x w M)
  let v := ED f g h x y z M
  let G := upperF (C f j)
  let s := GaussianNamedCofinalOrder.clock (E f g h) G p q v c A (B+B)
  let a := chart f g h j s x y z w M
  let b := upperPoint (coefficient a.denominator a.shiftBound) (a.base*a.denominator)
  let d := ZD a.base a.denominator a.left a.right
  have read := frozen_relative_rate f g h j s x y z w M hs ho hsize
  have right := GaussianNamedRateComposition.symmetric G constantF c b (B+B) (unit s) (unit_positive s) read.andE₂.andE₂.andE₁
  exact GaussianNamedCofinalOrder.observation (E f g h) Z constantF G p q v d b c A (B+B)
    read.andE₁ right read.andE₂.andE₂.andE₂.andE₂

theorem exact_relative_order (f g h j : PR 2) (x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w)
    (hsize : Γ ⊢[PRAAx] sizeOrder f j x w) :
    Γ ⊢[PRAAx] relativeRate f g h j x y z w M := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f g h j (sh x) (sh y) (sh z) (sh w) (sh M) :=
    by simpa only [Fm.shift,Syn.shift,sh,GaussianGammaDigammaTwoShiftNamedWindow.subst_source] using hs.shift.shift
  have os : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] orders f g h j (sh x) (sh y) (sh z) (sh w) :=
    by simpa only [Fm.shift,Syn.shift,sh,GaussianGammaDigammaTwoShiftNamedWindow.subst_orders] using ho.shift.shift
  have si : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] sizeOrder f j (sh x) (sh w) :=
    by simpa only [Fm.shift,Syn.shift,sh,GaussianGammaDigammaTwoShiftNamedRepairedChart.subst_sizeOrder] using hsize.shift.shift
  refine .andI (.allI (.allI ?_)) (.allI (.allI ?_))
  · simpa only [realOrder,Syn.shift,sh,subst_lowerData,GaussianGammaDigammaTwoShiftNamedBinding.subst_quotientData,
      GaussianGammaDigammaTwoShiftNamedCap.subst_data] using lower_observation f g h j (var 1) (var 0) (sh x) (sh y) (sh z) (sh w) (sh M) ss os si
  · simpa only [realOrder,Syn.shift,sh,subst_upperData,GaussianGammaDigammaTwoShiftNamedBinding.subst_quotientData,
      GaussianGammaDigammaTwoShiftNamedCap.subst_data] using upper_observation f g h j (var 1) (var 0) (sh x) (sh y) (sh z) (sh w) (sh M) ss os si

theorem actual_original_named_two_shift_relative_rate_closed (f g h j : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f g h j (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ orders f g h j (var 0) (var 1) (var 2) (var 3) ⟶
        sizeOrder f j (var 0) (var 3) ⟶ relativeRate f g h j (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (exact_relative_order f g h j _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedRelativeOrder
