import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Recurrence.GaussianLogGammaEulerProductShift
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerDenominatorShift
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.FiniteHeads.GaussianLogGammaEulerNormalizedHead
import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupDifferenceTransform

/-!
# Unit recurrence at the original finite log-Gamma head

The factorial terms cancel and the shifted and unshifted denominator rows
share the same interior. The exact correction is the difference of the
integer logarithm and the terminal shifted logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRecurrenceFinite

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerHead (nameF data productF productData sumData)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRightHalfPlaneLogarithm (source)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "S" => GaussianLogGammaEulerHead.sumF
local notation "L" => GaussianPositiveRationalLogarithm.data

def correctedF : PR 2 := F logF (F G G)

def correctedData (A B D neg N : PTm n) : PTm n :=
  X (L N one) (X (P (A+succ N*D) B D neg) (P A B D neg))

ipra_subst correctedData [one]

theorem shift_source (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] source (A+D) D neg :=
  .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right A D)) h.andE₁.andE₂) h.andE₂

theorem difference (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (F nameF nameF) correctedF
      (X (data (A+D) B D neg N) (data A B D neg N)) (correctedData A B D neg N) := by
  let C := addF logF productF
  let e := L (fact N) one
  let a := productData (A+D) B D neg N
  let b := productData A B D neg N
  let u := addData e a
  let v := addData e b
  let x := sumData (A+D) B D neg N
  let y := sumData A B D neg N
  let z := P (A+succ N*D) B D neg
  let w := P A B D neg
  let q := L N one
  have hE := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) (fact N) one
    (.andI (GammaEulerMesh.factorial_positive N) (le_refl one))
  have hQ := GaussianPositiveRationalLogarithm.name_regular (Γ := Γ) N one (.andI hN (le_refl one))
  have hA := GaussianLogGammaEulerNormalizedHead.product_regular (A+D) B D neg N hN
  have hB := GaussianLogGammaEulerNormalizedHead.product_regular A B D neg N hN
  have hU : Γ ⊢[PRAAx] pointCN C u := add_fast logF productF e a hE hA
  have hV : Γ ⊢[PRAAx] pointCN C v := add_fast logF productF e b hE hB
  have hX := GaussianLogGammaEulerHead.sum_regular (A+D) B D neg N (shift_source A D neg h)
  have hY := GaussianLogGammaEulerHead.sum_regular A B D neg N h
  have hZ := GaussianRightHalfPlaneLogarithm.regular (A+succ N*D) B D neg
    (GaussianLogGammaEulerHead.shifted_source (succ N) A D neg h)
  have hW := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have exchange := GaussianBohrMollerupDifferenceTransform.exchange C S C S u x v y hU hX hV hY
  have num := cross_trans (F C C) (F productF productF) logF (X u v) (X a b) q
    (GaussianBohrMollerupDifference.cancel_common logF productF productF e a b hE hA hB)
    (GaussianLogGammaEulerProductShift.difference A B D neg N h.andE₂ hN)
  have den := GaussianLogGammaEulerDenominatorShift.difference A B D neg N h
  have corrected := difference_proper (F C C) logF (F S S) (F G G) (X u v) q (X x y) (X z w)
    (GaussianNamedDifference.name_regular C C u v hU hV) hQ
    (GaussianNamedDifference.name_regular S S x y hX hY)
    (GaussianNamedDifference.name_regular G G z w hZ hW) num den
  exact cross_trans (F nameF nameF) (F (F C C) (F S S)) correctedF
    (X (data (A+D) B D neg N) (data A B D neg N)) (X (X u v) (X x y)) (correctedData A B D neg N) exchange corrected

theorem actual_finite_log_Gamma_unit_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 2) (var 3) ⋏ le one (var 4)) ⟶ crossEquivalent (F nameF nameF) correctedF
      (X (data (var 0+var 2) (var 1) (var 2) (var 3) (var 4))
        (data (var 0) (var 1) (var 2) (var 3) (var 4)))
      (correctedData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (difference _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerRecurrenceFinite
