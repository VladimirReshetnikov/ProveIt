import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupBracketIncrements
import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupFactorialNormalization

/-!
# The exact finite Bohr–Mollerup enclosure

On the original positive rational presentation, f(x) lies between the
literal paper brackets. The finite recurrence identifies both the
integer factorial term and the actual shifted logarithm subtraction.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketEnclosure

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupBlockChord (source)
open GaussianBohrMollerupBracketEndpoints (baseF baseData bracketF lowerData upperData endpointData sumData sum_regular)
open GaussianBohrMollerupBracketIncrements (incrementF incrementData boundData)
open GaussianBohrMollerupChords (base translated base_source translated_source)
open GaussianBohrMollerupPresentation (Presentation argument laws observe_value)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaRationalWendelBoundary (difference_cross)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative negativeF negativeData negative_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (fractional_regular)
open GaussianNamedRealOrderTransport (transport)
open GaussianNaturalScaleProductName (productF)
open GaussianNamedStrictOrderDifference (sum_sub_right)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "logData" => GaussianHarmonicLogarithmName.data
local notation "Sum" => GaussianBohrMollerupBracketEndpoints.sumF
local notation "W" => productF H

private theorem plus_difference (F : PR 2) (x y : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN F y) :
    Γ ⊢[PRAAx] crossEquivalent (addF F (D F F)) F (addData y (dd x y)) x := by
  let N := negativeF F
  let w := negativeData y
  have hw := negative_fast F y hy
  have first := cross_symm _ _ _ _ (add_associative F F N y x w hy hx hw)
  have second := add_cross (addF F F) (addF F F) N N (addData y x) (addData x y) w w
    (add_fast _ _ _ _ hy hx) (add_fast _ _ _ _ hx hy) hw hw
    (add_commutative F F y x hy hx) (cross_refl _ _ hw)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second (sum_sub_right F F x y hx hy))

private theorem bracket_reorder (P : Presentation) (a b j r : PTm n) (hp : Γ ⊢[PRAAx] laws P)
    (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] crossEquivalent (D (addF P.nameF W) Sum) bracketF
      (dd (addData (argument P (base b j) b) (boundData a b r)) (sumData a b (succ j))) (endpointData a b j r) := by
  let F := P.nameF
  let N := negativeF Sum
  let x := argument P (base b j) b
  let u := logData (fact j) one
  let v := boundData a b r
  let z := sumData a b (succ j)
  let w := negativeData z
  have hX := (observe_value P _ _ hp.andE₂.andE₁ (base_source b j hs.andE₂)).andE₁
  have hU := GaussianHarmonicLogarithmName.name_regular (Γ := Γ) (fact j) one
    (.andI (GammaEulerMesh.factorial_positive j) (le_refl one))
  have hV := fractional_regular H a b (logData r one) (GaussianHarmonicLogarithmName.name_regular r one (.andI hr (le_refl one)))
  have hZ := sum_regular a b (succ j) hs
  have hW := negative_fast Sum z hZ
  have changeBase := add_cross F H W W x u v v hX hU hV hV
    (GaussianBohrMollerupFactorialNormalization.at_scaled_integer P b j hp hs.andE₂) (cross_refl _ _ hV)
  have changeExpr := add_cross (addF F W) (addF H W) N N (addData x v) (addData u v) w w
    (add_fast _ _ _ _ hX hV) (add_fast _ _ _ _ hU hV) hW hW changeBase (cross_refl _ _ hW)
  have first := add_associative H W N u v w hU hV hW
  have second := add_cross H H (addF W N) (addF N W) u u (addData v w) (addData w v)
    hU hU (add_fast _ _ _ _ hV hW) (add_fast _ _ _ _ hW hV) (cross_refl _ _ hU) (add_commutative W N v w hV hW)
  have last := cross_symm _ _ _ _ (add_associative H N W u w v hU hW hV)
  exact cross_trans _ _ _ _ _ _ changeExpr (cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second last))

theorem enclosure (P : Presentation) (a b B j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source a b B) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] realOrder bracketF P.nameF (lowerData a b j) (argument P a b) ⋏
      realOrder P.nameF bracketF (argument P a b) (upperData a b B j) := by
  let F := P.nameF
  let I := incrementF P
  let N := negativeF Sum
  let x := argument P a b
  let y := argument P (base b j) b
  let v := argument P (translated a b j) b
  let z := sumData a b (succ j)
  let w := negativeData z
  let i := incrementData P a b j
  let r := boundData a b j
  let s := boundData a b (j+B)
  have hp' := hp.andE₂.andE₁
  have hb := hs.andE₁.andE₂
  have hJ := le_trans hj (le_add_right j B)
  have hx := (observe_value P _ _ hp' hs.andE₁).andE₁
  have hy := (observe_value P _ _ hp' (base_source b j hb)).andE₁
  have hv := (observe_value P _ _ hp' (translated_source a b j hb)).andE₁
  have hz := sum_regular a b (succ j) hs.andE₁
  have hw := negative_fast Sum z hz
  have hi := GaussianNamedDifference.name_regular F F v y hv hy
  have hcenter := plus_difference F v y hv hy
  have step := GaussianBohrMollerupFiniteRecurrence.iterated_cross P a b (succ j) hp' hp.andE₂.andE₂.andE₁ hs.andE₁
  have trimmed := difference_cross F (addF F Sum) Sum Sum v (addData x z) z z
    hv (add_fast _ _ _ _ hx hz) hz hz step (cross_refl _ _ hz)
  have collapse := cross_trans _ _ _ _ _ _ trimmed (sum_sub_right F Sum x z hx hz)
  have middle := cross_trans _ _ _ _ _ _
    (add_cross (addF F I) F N N (addData y i) v w w (add_fast _ _ _ _ hy hi) hv hw hw hcenter (cross_refl _ _ hw)) collapse
  have low := add_order F F W I y y r i (order_refl _ _ hy) (GaussianBohrMollerupBracketIncrements.lower P a b j hp hs.andE₁ hj)
  have high := add_order F F I W y y i s (order_refl _ _ hy) (GaussianBohrMollerupBracketIncrements.upper P a b B j hp hs)
  have lo := add_order (addF F W) (addF F I) N N (addData y r) (addData y i) w w low (order_refl _ _ hw)
  have hi := add_order (addF F I) (addF F W) N N (addData y i) (addData y s) w w high (order_refl _ _ hw)
  exact .andI (transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ (bracket_reorder P a b j j hp hs.andE₁ hj)) middle lo)
    (transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ middle) (bracket_reorder P a b j (j+B) hp hs.andE₁ hJ) hi)

theorem actual_literal_Bohr_Mollerup_brackets_closed (P : Presentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (laws P ⟶ source (var 0) (var 1) (var 2) ⟶ le one (var 3) ⟶
        (realOrder bracketF P.nameF (lowerData (var 0) (var 1) (var 3)) (argument P (var 0) (var 1)) ⋏
          realOrder P.nameF bracketF (argument P (var 0) (var 1)) (upperData (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (enclosure P _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupBracketEnclosure
