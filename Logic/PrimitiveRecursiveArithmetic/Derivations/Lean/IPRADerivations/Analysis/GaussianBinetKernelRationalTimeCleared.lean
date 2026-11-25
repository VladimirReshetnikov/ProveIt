import IPRADerivations.Analysis.GaussianBinetKernelFrozenHyperbolic
import IPRADerivations.Analysis.GaussianBinetKernelImaginaryRatioCofinal
import IPRADerivations.Analysis.GaussianNamedUniformRateClosure

/-!
# Cleared elementary Binet kernel at every rational time

For fixed (t=A/B), the original cofinal Binet kernel satisfies
`(t/2) cosh(t/2) = sinh(t/2) (1+t² K(t))`. The rational frozen ratios
`t/(2π_k)` enter only in the proof. The two fixed sides contain the original
kernel and original exponentials at the exact rational half-time.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelRationalTimeCleared

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetKernelFrozenHyperbolic
  (fixedSinhF fixedSinhData fixedCoshF fixedCoshData fixed_sinh_regular fixed_cosh_regular scaleBudget hyperbolicBudget)
open GaussianBinetKernelImaginaryRatioCofinal
  (referenceClock frozenNumerator frozenDenominator frozen_source fixedFactorF fixedFactorData timeSquareF timeSquareData)
open GaussianBinetKernelImaginaryRatioRows (ratioRadius)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNameRingLaws (one_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedUniformRateClosure (productBudget same_denominator_product)
open GaussianSineProductImaginaryCoshIdentity (coshF coshData cosh_regular)
open GaussianSineProductImaginaryHyperbolic (sinhF sinhData expF expData)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Scale" => GaussianPiRationalScale.nameF
local notation "CothLeft" => GaussianSineProductImaginaryCothExpansion.leftF
local notation "CothRight" => GaussianSineProductImaginaryCothExpansion.rightF
local notation "CothFactor" => GaussianSineProductImaginaryCothExpansion.factorF
local notation "factorData" => GaussianSineProductImaginaryCothExpansion.factorData
local notation "clearLeft" => GaussianSineProductImaginaryCothExpansion.leftData
local notation "clearRight" => GaussianSineProductImaginaryCothExpansion.rightData
local notation "kernelBudget" => GaussianBinetKernelImaginaryRatioCofinal.budget

def halfTime (A B : PTm n) : PTm n := GaussianPiRationalScale.point false A (two*B)
def leftF : PR 2 := multiplyF constantF fixedCoshF
def leftData (A B : PTm n) : PTm n := multiplyData constantF fixedCoshF (halfTime A B) (fixedCoshData A B)
def rightF : PR 2 := multiplyF fixedSinhF fixedFactorF
def rightData (A B : PTm n) : PTm n := multiplyData fixedSinhF fixedFactorF (fixedSinhData A B) (fixedFactorData A B)
def leftBudget (A B : PTm n) : PTm n :=
  productBudget (scaleBudget A) (hyperbolicBudget A) (U fixedCoshF (fixedCoshData A B)) (U constantF (halfTime A B))
def rightBudget (A B : PTm n) : PTm n :=
  productBudget (hyperbolicBudget A) (kernelBudget A) (U fixedFactorF (fixedFactorData A B)) (U fixedSinhF (fixedSinhData A B))
def budget (A B : PTm n) : PTm n := leftBudget A B+rightBudget A B

theorem fixed_factor_regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pointCN fixedFactorF (fixedFactorData A B) :=
  add_fast _ _ _ _ (one_fast _) (multiply_fast _ _ _ _ (constant_regular _) (GaussianBinetKernelCofinal.regular A B hB))

private theorem frozen_sinh_regular (a b R x : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] le a (R*b)) : Γ ⊢[PRAAx] pointCN sinhF (sinhData a b R x) := by
  have exp (s : Bool) := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianPiRationalScale.exponential_input s a b R x hb ha)
  exact multiply_fast _ _ _ _ (constant_regular _) (GaussianNamedDifference.name_regular _ _ _ _ (exp true) (exp false))

private theorem reduce_clock (F G : PR 2) (x y C p A : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F G x y C (unit (referenceClock p A))) :
    Γ ⊢[PRAAx] independentRate G F y x C (unit p) := by
  let k := referenceClock p A
  have hpk : Γ ⊢[PRAAx] le p k := le_trans (le_succ_self p) (le_add_right _ _)
  have mono : Γ ⊢[PRAAx] le (unit p) (unit k) := GaussianBalancedRadiusArithmetic.unit_monotone p k hpk
  have hyp := le_mul_mono (le_refl C) mono
  have hr := GaussianNamedRateRadius.weaken F G x y C (unit k) C (unit p) (unit_positive k) (unit_positive p) hyp h
  exact GaussianNamedRateComposition.symmetric F G x y C (unit p) (unit_positive p) hr

theorem dyadic_rate (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] independentRate leftF rightF (leftData A B) (rightData A B) (budget A B) (unit p) := by
  let k := referenceClock p A
  let a := frozenNumerator p A
  let b := frozenDenominator p A B
  let R := ratioRadius A
  let f := halfTime A B
  let c := fixedCoshData A B
  let s := fixedSinhData A B
  let y := fixedFactorData A B
  let u := GaussianPiRationalScale.data false a b R zero
  let v := coshData a b R zero
  let w := sinhData a b R zero
  let d := factorData a b R
  let E := unit p
  have src := frozen_source p A B hB
  have hR := src.andE₁
  have hb := src.andE₂.andE₁
  have hm := src.andE₂.andE₂
  have ha := le_trans (le_add_right _ _) hm
  have hE : Γ ⊢[PRAAx] le one E := unit_positive p
  have hf := constant_regular (Γ := Γ) f
  have hc := fixed_cosh_regular A B hB
  have hs := fixed_sinh_regular A B hB
  have hy := fixed_factor_regular A B hB
  have hu := GaussianPiRationalScale.regular false a b R zero hb ha
  have hv := cosh_regular a b R zero hb ha
  have hw := frozen_sinh_regular a b R zero hb ha
  have hd := GaussianSineProductImaginaryCothExpansion.factor_regular a b R hb ha
  have rateScale := reduce_clock _ _ u f (scaleBudget A) p A
    (GaussianBinetKernelFrozenHyperbolic.frozen_scale_rate false k A B hB)
  have rateCosh := reduce_clock _ _ v c (hyperbolicBudget A) p A
    (GaussianBinetKernelFrozenHyperbolic.frozen_cosh_rate k A B hB)
  have rateSinh := reduce_clock _ _ w s (hyperbolicBudget A) p A
    (GaussianBinetKernelFrozenHyperbolic.frozen_sinh_rate k A B hB)
  have rateFactor := GaussianBinetKernelImaginaryRatioCofinal.factor_rate p A B hB
  have left : Γ ⊢[PRAAx] independentRate leftF CothLeft (leftData A B) (clearLeft a b R zero) (leftBudget A B) E :=
    same_denominator_product constantF fixedCoshF Scale coshF f c u v _ _ E _ _ hE hf hc hu hv
      (all_samples_bounded _ _ hc) (all_samples_bounded _ _ hf) rateScale rateCosh
  have right : Γ ⊢[PRAAx] independentRate rightF CothRight (rightData A B) (clearRight a b R zero) (rightBudget A B) E :=
    same_denominator_product fixedSinhF fixedFactorF sinhF CothFactor s y w d _ _ E _ _ hE hs hy hw hd
      (all_samples_bounded _ _ hy) (all_samples_bounded _ _ hs) rateSinh rateFactor
  have eql := GaussianSineProductImaginaryCothExpansion.cleared_expansion a b R zero hR hb hm
  have back := GaussianNamedRateComposition.symmetric rightF CothRight (rightData A B) (clearRight a b R zero) _ E hE right
  have fixed := GaussianNamedRateTransport.transport CothRight rightF CothLeft rightF _ _ _ _
    (rightBudget A B) E hE back eql (cross_refl _ _ (multiply_fast _ _ _ _ hs hy))
  exact GaussianNamedRateComposition.same_denominator leftF CothLeft rightF _ _ _ _ E _ hE left fixed

theorem cleared_kernel (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent leftF rightF (leftData A B) (rightData A B) := by
  apply GaussianNamedUniformRateClosure.equivalent _ _ _ _ (budget A B)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (z : PTm n) := Syn.shift z
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  simpa [GaussianNamedUniformRateClosure.family,Δ,sh,Syn.shift,leftData,rightData,halfTime,budget,leftBudget,rightBudget,
    productBudget,GaussianBinetKernelImaginaryRatioCofinal.fixedFactorData,
    GaussianBinetKernelImaginaryRatioCofinal.timeSquareData,GaussianBinetKernelImaginaryRatioCofinal.budget,
    ratioRadius,two,one] using dyadic_rate (var 0) (sh A) (sh B) bs

theorem actual_cleared_elementary_Binet_kernel_rational_time_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 1) ⟶ crossEquivalent leftF rightF (leftData (var 0) (var 1)) (rightData (var 0) (var 1))) :=
  closeUniv 2 (.impI (cleared_kernel _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelRationalTimeCleared
