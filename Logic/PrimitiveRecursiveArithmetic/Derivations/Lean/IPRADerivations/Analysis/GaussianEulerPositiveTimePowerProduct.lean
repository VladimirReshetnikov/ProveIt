import IPRADerivations.Analysis.GaussianHarmonicLogarithmProduct
import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsParameterShift

/-!
# Products of positive rational times in the original complex-power names

The proved harmonic logarithm product is transported to the unchanged
positive-rational logarithm. Actual named distributivity and exponential
addition then give (s*t)^(z-1)=s^(z-1)*t^(z-1), with all original input
clocks and independently computed exponential radii. This is an evaluator
identity toward positive scaling, without an integral or Gamma premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveTimePowerProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (logF)
open GaussianEulerIntegrandName (coefficient powerExponentF powerExponentData powerRadius powerF powerData power_input)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal cross_at)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logSource (a b c d : PTm n) : Fm PTm n := GaussianHarmonicLogarithmProduct.source a b c d
def source (B a b c d : PTm n) : Fm PTm n := le one B ⋏ logSource a b c d
def logSumData (a b c d : PTm n) : PTm n :=
  addData (GaussianPositiveRationalLogarithm.data a b) (GaussianPositiveRationalLogarithm.data c d)
def productF : PR 2 := multiplyF powerF powerF
def productData (z B a b c d : PTm n) : PTm n := multiplyData powerF powerF (powerData z B a b) (powerData z B c d)
def productClock (p z B a b c d : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus powerF powerF (powerData z B a b) (powerData z B c d)) p

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (B a b c d : PTm n) :
    (source B a b c d).subst σ = source (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]
@[simp] theorem subst_logSumData {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (logSumData a b c d) = logSumData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [logSumData]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (z B a b c d : PTm n) :
    Syn.subst σ (productData z B a b c d) = productData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [productData]
@[simp] theorem subst_productClock {m : ℕ} (σ : Fin n → PTm m) (p z B a b c d : PTm n) :
    Syn.subst σ (productClock p z B a b c d) = productClock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by simp [productClock]

/-- The actual original logarithm has the product identity, independently
of the ordered harmonic representative used to prove it. -/
theorem logarithm_product (a b c d : PTm n) (hs : Γ ⊢[PRAAx] logSource a b c d) : Γ ⊢[PRAAx]
    crossEquivalent logF (addF logF logF) (GaussianPositiveRationalLogarithm.data (a*c) (b*d)) (logSumData a b c d) := by
  let H := GaussianHarmonicLogarithmName.nameF
  have left := GaussianHarmonicLogarithmName.cross_original (a*c) (b*d) (GaussianHarmonicLogarithmProduct.product_source a b c d hs)
  have harmonic := GaussianHarmonicLogarithmProduct.logarithm_product a b c d hs
  have returned := GaussianNameArithmetic.add_equivalent H logF H logF
    (GaussianHarmonicLogarithmName.data a b) (GaussianPositiveRationalLogarithm.data a b)
    (GaussianHarmonicLogarithmName.data c d) (GaussianPositiveRationalLogarithm.data c d)
    (GaussianHarmonicLogarithmName.name_regular a b hs.andE₁) (GaussianPositiveRationalLogarithm.name_regular a b hs.andE₁)
    (GaussianHarmonicLogarithmName.name_regular c d hs.andE₂) (GaussianPositiveRationalLogarithm.name_regular c d hs.andE₂)
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b hs.andE₁)))
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original c d hs.andE₂)))
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ harmonic returned)

theorem power_exponent_product (z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    crossEquivalent (addF powerExponentF powerExponentF) powerExponentF
      (addData (powerExponentData z B a b) (powerExponentData z B c d)) (powerExponentData z B (a*c) (b*d)) := by
  let x := coefficient z B
  let L := GaussianPositiveRationalLogarithm.data a b
  let M := GaussianPositiveRationalLogarithm.data c d
  let P := GaussianPositiveRationalLogarithm.data (a*c) (b*d)
  have hx := constant_regular (Γ := Γ) x
  have hl := GaussianPositiveRationalLogarithm.name_regular a b hs.andE₂.andE₁
  have hm := GaussianPositiveRationalLogarithm.name_regular c d hs.andE₂.andE₂
  have hp := GaussianPositiveRationalLogarithm.name_regular (a*c) (b*d)
    (GaussianHarmonicLogarithmProduct.product_source a b c d hs.andE₂)
  have change := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF logF (addF logF logF)
    x x P (logSumData a b c d) hx hx hp (add_fast logF logF L M hl hm)
    (cross_refl _ _ hx) (logarithm_product a b c d hs.andE₂)
  have distribute := GaussianNameRingLaws.distributive constantF logF logF x L M hx hl hm
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ change distribute)

/-- All three original power names keep their genuine data, input clocks,
scalar-sum cutoffs and independent exponential radii. -/
theorem original_power_product (z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    crossEquivalent powerF productF (powerData z B (a*c) (b*d)) (productData z B a b c d) := by
  have productTime := GaussianHarmonicLogarithmProduct.product_source a b c d hs.andE₂
  exact cross_symm _ _ _ _
    (GaussianGammaFoldedApproximantBalance.exponential_product_equivalent powerExponentF powerExponentF powerExponentF
      (powerRadius z B a b) (powerRadius z B c d) (powerRadius z B (a*c) (b*d))
      (powerExponentData z B a b) (powerExponentData z B c d) (powerExponentData z B (a*c) (b*d))
      (power_input z B a b (.andI hs.andE₁ hs.andE₂.andE₁)) (power_input z B c d (.andI hs.andE₁ hs.andE₂.andE₂))
      (power_input z B (a*c) (b*d) (.andI hs.andE₁ productTime)) (power_exponent_product z B a b c d hs))

theorem product_readback (p z B a b c d : PTm n) : Γ ⊢[PRAAx]
    ap2 productF p (productData z B a b c d) ≐
      qmul (ap2 powerF (productClock p z B a b c d) (powerData z B a b))
        (ap2 powerF (productClock p z B a b c d) (powerData z B c d)) :=
  (GaussianNameArithmetic.multiply_at powerF powerF _ _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem original_observations (p q z B a b c d : PTm n) (hs : Γ ⊢[PRAAx] source B a b c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 powerF p (powerData z B (a*c) (b*d))) (ap2 productF q (productData z B a b c d))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_power_product z B a b c d hs)

theorem actual_original_positive_rational_logarithm_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (logSource (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent logF (addF logF logF)
      (GaussianPositiveRationalLogarithm.data (var 0*var 2) (var 1*var 3)) (logSumData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (logarithm_product _ _ _ _ Prf.hyp0))

theorem actual_original_positive_time_complex_power_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent powerF productF
      (powerData (var 0) (var 1) (var 2*var 4) (var 3*var 5)) (productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_power_product _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveTimePowerProduct
