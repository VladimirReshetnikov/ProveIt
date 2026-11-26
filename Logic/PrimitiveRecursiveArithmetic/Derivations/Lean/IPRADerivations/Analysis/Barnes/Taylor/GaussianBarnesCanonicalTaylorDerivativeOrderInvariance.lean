import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFixedTaylorDerivativeName
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorProductOrderInvariance

/-!
# Independence of the retaining degree in the Barnes derivative names

One sufficiently late prefactor observation compares the two finite
coefficient names at their exact common coefficient. The finite
central scalar and factorial preserve this equality. A common finite
cutoff transfers it to the cofinal names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (precision prefactorGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (query_budget)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedUniformRateClosure (equivalent family)
open GaussianRationalNaturalScale (naturalPoint)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "D" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "dd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "L" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "ld" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

private theorem fixed_coefficient_rate (p z R B r M S e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) :
    Γ ⊢[PRAAx] independentRate F F (fd z R B r M e) (fd z R B r S e) ((one+one)+(one+one)) (unit p) := by
  let a := clock p z R B M e
  let b := clock p z R B S e
  let q := precision (a+b) R
  let x := productCoefficient q z R B r M e
  let y := productCoefficient q z R B r S e
  have paid : Γ ⊢[PRAAx] le (prefactorGain R*unit (a+b)) (unit q) := query_budget _ _
  have hqM : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready p z R B M e q :=
    le_trans (le_mul_mono (le_refl _) (unit_monotone (le_add_right a b))) paid
  have hqS : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorCoefficientName.ready p z R B S e q :=
    le_trans (le_mul_mono (le_refl _) (unit_monotone (le_add_left b a))) paid
  have first := GaussianBarnesCanonicalFixedTaylorCoefficientName.finite_rate p z R B r M e q hz hM hqM
  have second := GaussianBarnesCanonicalFixedTaylorCoefficientName.finite_rate p z R B r S e q hz hS hqS
  have same : Γ ⊢[PRAAx] x ≐ y :=
    GaussianBarnesCanonicalTaylorProductOrderInvariance.order_invariance q z R B r M S e hM hS
  have leftRegular := constant_regular (Γ := Γ) x
  have rightRegular := constant_regular (Γ := Γ) y
  have middle := GaussianGammaInputProperness.code_data_cross constantF x y leftRegular rightRegular same
  have fixedRegular := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r S e hz hS
  have aligned := GaussianNamedRateTransport.transport F constantF F constantF (fd z R B r S e) y (fd z R B r S e) x
    (one+one) (unit p) (unit_positive p) second (cross_refl _ _ fixedRegular) middle
  exact GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ (one+one) (unit p) (one+one)
    (unit_positive p) first (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p) aligned)

theorem fixed_coefficient_cross (z R B r M S e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) :
    Γ ⊢[PRAAx] crossEquivalent F F (fd z R B r M e) (fd z R B r S e) := by
  apply equivalent _ _ _ _ ((one+one)+(one+one))
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hz' : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Fm.shift,Syn.shift] using hz.shift
  have hM' : Γ.map Fm.shift ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [sh,Fm.shift,Syn.shift] using hM.shift
  have hS' : Γ.map Fm.shift ⊢[PRAAx] le (sh e) (previous (sh S)) := by simpa [sh,Fm.shift,Syn.shift] using hS.shift
  simpa [family,sh,Syn.shift,one] using
    fixed_coefficient_rate (var 0) (sh z) (sh R) (sh B) (sh r) (sh M) (sh S) (sh e) hz' hM' hS'

theorem fixed_cross (z R B r M S e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) :
    Γ ⊢[PRAAx] crossEquivalent D D (dd z R B r M e) (dd z R B r S e) := by
  let a := naturalPoint (fact e)
  let G := GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientF
  let gd := GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData (n := n)
  let T := GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF
  let t := GaussianBarnesCanonicalFiniteCentralExponential.finiteData z R B r
  have ha := constant_regular (Γ := Γ) a
  have hc₁ := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M e hz hM
  have hc₂ := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r S e hz hS
  have same := multiply_cross constantF constantF F F a a (fd z R B r M e) (fd z R B r S e)
    ha ha hc₁ hc₂ (cross_refl _ _ ha) (fixed_coefficient_cross z R B r M S e hz hM hS)
  have ht := GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz
  exact multiply_cross T T G G t t (gd z R B r M e) (gd z R B r S e) ht ht
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficient_regular z R B r M e hz hM)
    (GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficient_regular z R B r S e hz hS) (cross_refl _ _ ht) same

private theorem cofinal_order_rate (p z R B M S e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) :
    Γ ⊢[PRAAx] independentRate L L (ld z R B M e) (ld z R B S e) (one+one) (unit p) := by
  let a := GaussianBarnesCanonicalFixedTaylorDerivativeName.cutoff p z R B M e
  let b := GaussianBarnesCanonicalFixedTaylorDerivativeName.cutoff p z R B S e
  let r := a+b
  have first := GaussianBarnesCanonicalFixedTaylorDerivativeName.late_rate p z R B r M e hz hM (le_add_right a b)
  have second := GaussianBarnesCanonicalFixedTaylorDerivativeName.late_rate p z R B r S e hz hS (le_add_left b a)
  have hx := GaussianBarnesCanonicalTaylorProductDerivativeName.regular z R B S e hz hS
  have aligned := GaussianNamedRateTransport.transport L D L D (ld z R B S e) (dd z R B r S e) (ld z R B S e)
    (dd z R B r M e) one (unit p) (unit_positive p) second (cross_refl _ _ hx) (fixed_cross z R B r M S e hz hM hS)
  exact GaussianNamedRateComposition.same_denominator _ _ _ _ _ _ one (unit p) one (unit_positive p) first
    (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p) aligned)

theorem cofinal_cross (z R B M S e : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) :
    Γ ⊢[PRAAx] crossEquivalent L L (ld z R B M e) (ld z R B S e) := by
  apply equivalent _ _ _ _ (one+one)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hz' : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Fm.shift,Syn.shift] using hz.shift
  have hM' : Γ.map Fm.shift ⊢[PRAAx] le (sh e) (previous (sh M)) := by simpa [sh,Fm.shift,Syn.shift] using hM.shift
  have hS' : Γ.map Fm.shift ⊢[PRAAx] le (sh e) (previous (sh S)) := by simpa [sh,Fm.shift,Syn.shift] using hS.shift
  simpa [family,sh,Syn.shift,one,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
    GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData] using
    cofinal_order_rate (var 0) (sh z) (sh R) (sh B) (sh M) (sh S) (sh e) hz' hM' hS'

theorem actual_Barnes_cofinal_factorial_coefficient_order_invariance_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let R := var 1
       let B := var 2
       let M := var 3
       let S := var 4
       let e := var 5
       source z R B ⟶ le e (previous M) ⟶ le e (previous S) ⟶ crossEquivalent L L (ld z R B M e) (ld z R B S e)) :=
  closeUniv 6 (.impI (.impI (.impI (cofinal_cross _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeOrderInvariance
