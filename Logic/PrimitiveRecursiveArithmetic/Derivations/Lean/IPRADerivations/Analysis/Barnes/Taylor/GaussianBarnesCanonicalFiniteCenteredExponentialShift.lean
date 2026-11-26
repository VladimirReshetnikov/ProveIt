import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteCentralExponential
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalFiniteExponentTaylor

/-!
# Translate the exponential of the actual finite Barnes exponent

The shifted literal product has the exact centered kept polynomial,
the actual finite central scalar, and the exponential of its finite
exponent increment. All three use the same literal partial-product cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCenteredExponentialShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCenteredExponentialShift (head)
open GaussianBarnesCanonicalFiniteCentralExponential
  (finiteNameF finiteData finite_regular prefixExpData)
open GaussianBarnesCanonicalFiniteExponentTaylor (exponentF exponentData exponent_regular)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (prefixF prefixData prefix_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaFoldedApproximantBalance (exponential_product_equivalent)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "I" => GaussianBarnesCanonicalFiniteExponentTaylor.nameF
local notation "id" => GaussianBarnesCanonicalFiniteExponentTaylor.data

def incrementExpData (z h R B r : PTm n) : PTm n := exponentialInputData I (id z h R B r)

abbrev productF : PR 2 := multiplyF finiteNameF (E I)

def productData (z h R B r : PTm n) : PTm n :=
  multiplyData finiteNameF (E I) (finiteData z R B r) (incrementExpData z h R B r)

abbrev nameF : PR 2 := multiplyF constantF productF

def data (z h R B r : PTm n) : PTm n :=
  multiplyData constantF productF (head z h R B) (productData z h R B r)

theorem finite_single_exponential (z R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent finiteNameF (E exponentF) (finiteData z R B r)
      (exponentialInputData exponentF (exponentData z R B r)) := by
  let A := GaussianBarnesCanonicalFiniteLog.nameF
  let a := GaussianBarnesCanonicalFiniteLog.data z R B (initial R) r
  let b := prefixData z R B
  let v := exponentData z R B r
  have hr := exponent_regular z R B r hz
  exact exponential_product_equivalent prefixF A exponentF (U prefixF b) (GaussianBarnesCanonicalFiniteLog.radius R)
    (U exponentF v) b a v (exponential_input _ _ (prefix_regular z R B))
    (GaussianBarnesCanonicalFiniteLog.exponential_input _ _ _ _ _
      (GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz))
    (exponential_input _ _ hr) (cross_refl _ _ hr)

theorem increment_exp_regular (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) : Γ ⊢[PRAAx] pointCN (E I) (incrementExpData z h R B r) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (exponential_input _ _ (GaussianNamedDifference.name_regular exponentF exponentF _ _
      (exponent_regular (add z h) R B r hw) (exponent_regular z R B r hz)))

theorem exponential_shift (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent productF finiteNameF (productData z h R B r) (finiteData (add z h) R B r) := by
  let w := add z h
  let x := exponentData z R B r
  let y := exponentData w R B r
  let d := id z h R B r
  let v := incrementExpData z h R B r
  let a := exponentialInputData exponentF x
  let b := exponentialInputData exponentF y
  have hx := exponent_regular z R B r hz
  have hy := exponent_regular w R B r hw
  have hd := GaussianNamedDifference.name_regular exponentF exponentF y x hy hx
  have ix := exponential_input _ _ hx
  have ir := increment_exp_regular z h R B r hz hw
  have ar := GaussianRadiusExponentialName.name_regular _ _ _ ix
  have fold := exponential_product_equivalent I exponentF exponentF (U I d) (U exponentF x) (U exponentF y) d x y
    (exponential_input _ _ hd) ix (exponential_input _ _ hy)
    (GaussianGammaRationalRatioBinding.difference_add_recover exponentF exponentF y x hy hx)
  have commute := GaussianNameRingLaws.multiply_commutative (E exponentF) (E I) a v ar ir
  have first := multiply_cross finiteNameF (E exponentF) (E I) (E I) (finiteData z R B r) a v v
    (finite_regular z R B r hz) ar ir ir (finite_single_exponential z R B r hz) (cross_refl _ _ ir)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ commute
      (cross_trans _ _ _ _ _ _ fold (cross_symm _ _ _ _ (finite_single_exponential w R B r hw))))

theorem literal_shift (z h R B r : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalValue.prefixF nameF
      (GaussianBarnesCanonicalProduct.literalData (add z h) R B (initial R+r)) (data z h R B r) := by
  let w := add z h
  let q := head z h R B
  have hq := constant_regular (Γ := Γ) q
  have regular := multiply_fast _ _ _ _ (finite_regular z R B r hz) (increment_exp_regular z h R B r hz hw)
  have moved := multiply_cross constantF constantF productF finiteNameF q q (productData z h R B r) (finiteData w R B r)
    hq hq regular (finite_regular w R B r hw) (cross_refl _ _ hq) (exponential_shift z h R B r hz hw)
  exact cross_trans _ _ _ _ _ _ (GaussianBarnesCanonicalFiniteCentralExponential.shifted_factorization z h R B r hw)
    (cross_symm _ _ _ _ moved)

theorem actual_Barnes_literal_finite_product_exponential_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     source z R B ⟶ source (add z h) R B ⟶ crossEquivalent GaussianBarnesCanonicalValue.prefixF nameF
       (GaussianBarnesCanonicalProduct.literalData (add z h) R B (initial R+r)) (data z h R B r)) :=
  closeUniv 5 (.impI (.impI (literal_shift _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteCenteredExponentialShift
