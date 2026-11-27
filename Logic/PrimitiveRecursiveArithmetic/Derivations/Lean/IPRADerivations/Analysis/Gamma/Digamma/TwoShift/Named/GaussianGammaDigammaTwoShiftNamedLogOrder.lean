import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedRepairedChart
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.Rates.GaussianGammaDigammaTwoShiftRationalRate
import IPRADerivations.Analysis.Names.Order.GaussianNamedCofinalOrder
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderLinear
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCompactRate

/-!
# The exact logarithmic two-shift bound on regular real names

The ordinary named shift window supplies a repaired rational chart at
the exact internal gap-removal clock. The original logarithmic quotient
lies between the negative and positive original cap names
4 A(A+1)/x, including equality in any window guard.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedLogOrder

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftNamedWindow (source orders)
open GaussianGammaDigammaTwoShiftNamedRepairedChart (actual_chart chart capBudget quotientBudget)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (qnegative qnegative_canonical qsub)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianGammaDigammaTwoShiftNamedBinding.quotientLogF
local notation "FD" => GaussianGammaDigammaTwoShiftNamedBinding.quotientLogData
local notation "C" => GaussianGammaDigammaTwoShiftNamedCap.nameF
local notation "CD" => GaussianGammaDigammaTwoShiftNamedCap.data
local notation "Q" => GaussianGammaDigammaTwoShiftBinding.quotientLogF
local notation "QD" => GaussianGammaDigammaTwoShiftBinding.quotientLogData
local notation "R" => GaussianGammaDigammaTwoShiftCapRepair.cap

theorem negative_constant_rate (g : PR 2) (x a A D : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hg : Γ ⊢[PRAAx] pointCN g x)
    (h : Γ ⊢[PRAAx] independentRate g constantF x a A D) :
    Γ ⊢[PRAAx] independentRate (negativeF g) constantF (negativeData x) (qnegative a) A D := by
  have neg := GaussianEulerPowerScalingCompactRate.negative_rate g constantF x a A D hg (constant_regular a) hd h
  have norm : Γ ⊢[PRAAx] qsub qzero a ≐ qnegative a :=
    GaussianRationalSyntheticDivision.qzero_add _ (qnegative_canonical _)
  have bind : Γ ⊢[PRAAx] crossEquivalent (negativeF constantF) constantF (negativeData a) (qnegative a) :=
    cross_trans (negativeF constantF) constantF constantF (negativeData a) (qsub qzero a) (qnegative a)
      (GaussianNamedRealOrderLinear.negative_constant a)
      (GaussianSignedNameExponentialOrder.constant_equal_cross (qsub qzero a) (qnegative a) norm)
  exact GaussianNamedRateTransport.transport (negativeF g) (negativeF constantF) (negativeF g) constantF
    (negativeData x) (negativeData a) (negativeData x) (qnegative a) A D hd neg
    (cross_refl _ _ (negative_fast g x hg))
    (cross_symm _ _ _ _ bind)

def logRate (f g h j : PR 2) (x y z w M : PTm n) : Fm PTm n :=
  realOrder (negativeF (C f j)) (F f g h) (negativeData (CD f j x w M)) (FD f g h x y z M) ⋏
    realOrder (F f g h) (C f j) (FD f g h x y z M) (CD f j x w M)

theorem lower_observation (f g h j : PR 2) (p q x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (negativeF (C f j)) p (negativeData (CD f j x w M))))
      (fstT (ap2 (F f g h) q (FD f g h x y z M))) (unit p+unit q) (unit p*unit q) := by
  let U := capBudget f j x w M
  let V := quotientBudget f g h j x y z w M
  let c := CD f j x w M
  let v := FD f g h x y z M
  let G := negativeF (C f j)
  let s := GaussianNamedCofinalOrder.clock G (F f g h) p q (negativeData c) v U V
  let a := chart f g h j s x y z w M
  let b := R a.base a.denominator a.shiftBound
  let d := QD a.base a.denominator a.left a.right
  have hD := unit_positive (Γ := Γ) s
  have read := actual_chart f g h j s x y z w M hs ho
  have reg := GaussianGammaDigammaTwoShiftNamedCap.name_regular f j x w M hs.andE₁ hs.andE₂.andE₂.andE₂.andE₁.andE₁
  have l := negative_constant_rate (C f j) c b U (unit s) hD reg read.andE₂.andE₂.andE₁
  have r := GaussianNamedRateComposition.symmetric (F f g h) Q v d V (unit s) hD read.andE₂.andE₁
  have order := GaussianGammaDigammaTwoShiftRationalRate.two_shift_log_rate a.base a.denominator a.left a.right a.shiftBound read.andE₁
  exact GaussianNamedCofinalOrder.observation G constantF Q (F f g h) p q (negativeData c) (qnegative b) d v U V l r order.andE₁

theorem upper_observation (f g h j : PR 2) (p q x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (F f g h) p (FD f g h x y z M)))
      (fstT (ap2 (C f j) q (CD f j x w M))) (unit p+unit q) (unit p*unit q) := by
  let U := capBudget f j x w M
  let V := quotientBudget f g h j x y z w M
  let c := CD f j x w M
  let v := FD f g h x y z M
  let s := GaussianNamedCofinalOrder.clock (F f g h) (C f j) p q v c V U
  let a := chart f g h j s x y z w M
  let b := R a.base a.denominator a.shiftBound
  let d := QD a.base a.denominator a.left a.right
  have hD := unit_positive (Γ := Γ) s
  have read := actual_chart f g h j s x y z w M hs ho
  have r := GaussianNamedRateComposition.symmetric (C f j) constantF c b U (unit s) hD read.andE₂.andE₂.andE₁
  have order := GaussianGammaDigammaTwoShiftRationalRate.two_shift_log_rate a.base a.denominator a.left a.right a.shiftBound read.andE₁
  exact GaussianNamedCofinalOrder.observation (F f g h) Q constantF (C f j) p q v d b c V U read.andE₂.andE₁ r order.andE₂

theorem exact_log_order (f g h j : PR 2) (x y z w M : PTm n)
    (hs : Γ ⊢[PRAAx] source f g h j x y z w M) (ho : Γ ⊢[PRAAx] orders f g h j x y z w) :
    Γ ⊢[PRAAx] logRate f g h j x y z w M := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f g h j (sh x) (sh y) (sh z) (sh w) (sh M) :=
    by simpa only [Fm.shift,Syn.shift,sh,GaussianGammaDigammaTwoShiftNamedWindow.subst_source] using hs.shift.shift
  have os : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] orders f g h j (sh x) (sh y) (sh z) (sh w) :=
    by simpa only [Fm.shift,Syn.shift,sh,GaussianGammaDigammaTwoShiftNamedWindow.subst_orders] using ho.shift.shift
  refine .andI (.allI (.allI ?_)) (.allI (.allI ?_))
  · simpa only [realOrder,Syn.shift,sh,GaussianNameRingLaws.subst_negativeData,
      GaussianGammaDigammaTwoShiftNamedBinding.subst_quotientLogData,GaussianGammaDigammaTwoShiftNamedCap.subst_data] using
      lower_observation f g h j (var 1) (var 0) (sh x) (sh y) (sh z) (sh w) (sh M) ss os
  · simpa only [realOrder,Syn.shift,sh,GaussianGammaDigammaTwoShiftNamedBinding.subst_quotientLogData,
      GaussianGammaDigammaTwoShiftNamedCap.subst_data] using
      upper_observation f g h j (var 1) (var 0) (sh x) (sh y) (sh z) (sh w) (sh M) ss os

theorem actual_original_named_two_shift_logarithmic_rate_closed (f g h j : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f g h j (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ orders f g h j (var 0) (var 1) (var 2) (var 3) ⟶
        logRate f g h j (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (exact_log_order f g h j _ _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedLogOrder
