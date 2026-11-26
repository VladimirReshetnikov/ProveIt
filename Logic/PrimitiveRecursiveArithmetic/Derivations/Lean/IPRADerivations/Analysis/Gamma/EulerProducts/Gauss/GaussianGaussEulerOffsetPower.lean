import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerPowerRatio
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerRowExponents
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedRepeatedExponential
import IPRADerivations.Analysis.Integration.Moments.GaussianMomentReflection

/-!
# Collecting the common factors of the shifted Euler exponents

The indexed product of the common relative factors is the
exponential with coefficient one minus the scaled argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerOffsetPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerShift (merge_head)
open GaussianGammaFiniteApproximantName (logF log_regular logExponentF exponential_input)
open GaussianGammaGaussReference (offset scaled_offset)
open GaussianGaussEulerPowerRatio (fixedExponentF fixedExponentData fixedPowerF fixedPowerData fixed_exponent_regular)
open GaussianGaussEulerRowExponents (offsetExponent)
open GaussianGaussMultiplicationPowerRate (multiplier)
open GaussianNameArithmetic (multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedFiniteProductName (nameF)
open GaussianNamedRepeatedProduct (repeatF)
open GaussianNamedRepeatedExponential (repeatedData repeated_exponential)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qnegative)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product)
open GaussianRadiusExponentialName (input)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem negative_coefficient (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (naturalPoint m) (qnegative (offset z B m)) ≐ qnegative (multiplier z B m) :=
  (GaussianMomentReflection.negative_right_product (naturalPoint m) (offset z B m)).eqTrans
    (GaussianInverseBinomialRows.negative_congr ((natScale_as_product m (offset z B m)).eqSymm.eqTrans
      (scaled_offset z B m hB hm)))

theorem offset_exponent_input (z B m N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] input logExponentF (GaussianNameBounds.U logExponentF (offsetExponent z B m N))
      (offsetExponent z B m N) :=
  exponential_input _ _ (multiply_fast logF constantF N (qnegative (offset z B m))
    (log_regular N hN) (constant_regular _))

theorem scaled_offset_exponent (z B m N R : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N)
    (hx : Γ ⊢[PRAAx] input logExponentF R (offsetExponent z B m N)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedNaturalScale.nameF logExponentF) fixedExponentF
      (GaussianNamedNaturalScale.data m m (offsetExponent z B m N))
      (fixedExponentData (qnegative (multiplier z B m)) N) := by
  let a := qnegative (offset z B m)
  let c := qnegative (multiplier z B m)
  let M := naturalPoint m
  let X := offsetExponent z B m N
  let Z := fixedExponentData a N
  have hl := log_regular (Γ := Γ) N hN
  have ha := constant_regular (Γ := Γ) a
  have hM := constant_regular (Γ := Γ) M
  have hc := constant_regular (Γ := Γ) c
  have scaled := GaussianNaturalScaleProductName.scale_product_cross logExponentF m m R X hx (le_refl m)
  have swapped := GaussianNameRingLaws.multiply_commutative logF constantF N a hl ha
  have nested := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF logExponentF fixedExponentF
    M M X Z hM hM hx.andE₁ (fixed_exponent_regular a N hN) (cross_refl _ _ hM) swapped
  have merged := merge_head logF M a N hl
  have coeff := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF logF logF (qmul M a) c N N
    (constant_regular _) hc hl hl (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (negative_coefficient z B m hB hm))
    (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ scaled (cross_trans _ _ _ _ _ _ nested (cross_trans _ _ _ _ _ _ merged coeff))

def radius (z B m N : PTm n) : PTm n := GaussianNameBounds.U logExponentF (offsetExponent z B m N)
def repeatedOffsetData (z B m N : PTm n) : PTm n := repeatedData m m (radius z B m N) (offsetExponent z B m N)
def repeatedOffsetF : PR 2 := nameF (repeatF (GaussianBoundedIntegerExponentialStages.expF logExponentF))

theorem offset_product (z B m N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent repeatedOffsetF fixedPowerF (repeatedOffsetData z B m N)
      (fixedPowerData (qnegative (multiplier z B m)) N) := by
  let R := radius z B m N
  let X := offsetExponent z B m N
  let c := qnegative (multiplier z B m)
  let G := GaussianNamedNaturalScale.nameF logExponentF
  have hx := offset_exponent_input z B m N hN
  have repeated := repeated_exponential logExponentF m m R X hx hm (le_refl m)
  have gs := GaussianNamedNaturalScale.exponential_input logExponentF m m R X hx (le_refl m)
  have ht := exponential_input fixedExponentF (fixedExponentData c N) (fixed_exponent_regular c N hN)
  have target := GaussianExponentialRadiusIndependence.independent_radii_proper G fixedExponentF _ _ _ _ gs ht
    (scaled_offset_exponent z B m N R hB hm hN hx)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ repeated) target

theorem actual_Gauss_offset_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
      crossEquivalent repeatedOffsetF fixedPowerF (repeatedOffsetData (var 0) (var 1) (var 2) (var 3))
        (fixedPowerData (qnegative (multiplier (var 0) (var 1) (var 2))) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (offset_product _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerOffsetPower
