import IPRADerivations.Analysis.Barnes.CanonicalProducts.Values.GaussianBarnesCanonicalSingleExponential
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalRatioBinding

/-!
# Separate the constant and displacement in the original Barnes exponential

The exponential of the original shifted exponent equals the product of
its value at the center and the exponential of the original increment.
The kept polynomial is carried through exactly, including at zeros.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredExponentialShift

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (exponentF exponentData exponent_regular centered_factorization)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (evaluate ofGaussian)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "A" => exponentF

abbrev incrementF : PR 2 := GaussianNamedDifference.nameF A A

def incrementData (z h R B : PTm n) : PTm n :=
  GaussianNamedDifference.data (exponentData (add z h) R B) (exponentData z R B)

def baseData (z R B : PTm n) : PTm n := exponentialInputData A (exponentData z R B)

def valueData (z h R B : PTm n) : PTm n := exponentialInputData incrementF (incrementData z h R B)

def head (z h R B : PTm n) : PTm n :=
  evaluate (GaussianBarnesCanonicalCenteredHead.polynomial z B (initial R)) (ofGaussian h B)

abbrev productF : PR 2 := multiplyF (E A) (E incrementF)
def productData (z h R B : PTm n) : PTm n :=
  multiplyData (E A) (E incrementF) (baseData z R B) (valueData z h R B)

abbrev nameF : PR 2 := multiplyF C productF
def data (z h R B : PTm n) : PTm n :=
  multiplyData C productF (head z h R B) (productData z h R B)

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (incrementData z h R B) = incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [incrementData]

@[simp] theorem subst_baseData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (baseData z R B) = baseData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [baseData,exponentialInputData]

@[simp] theorem subst_valueData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (valueData z h R B) = valueData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [valueData,exponentialInputData]

@[simp] theorem subst_head {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (head z h R B) = head (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by simp [head]

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (productData z h R B) = productData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [productData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z h R B : PTm n) :
    Syn.subst σ (data z h R B) = data (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) :=
  by simp [data]

theorem increment_regular (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) : Γ ⊢[PRAAx] pointCN incrementF (incrementData z h R B) :=
  GaussianNamedDifference.name_regular _ _ _ _ (exponent_regular (add z h) R B hw) (exponent_regular z R B hz)

theorem base_regular (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN (E A) (baseData z R B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (exponent_regular z R B hz))

theorem value_regular (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) : Γ ⊢[PRAAx] pointCN (E incrementF) (valueData z h R B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (increment_regular z h R B hz hw))

theorem exponential_shift (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent productF (E A) (productData z h R B) (baseData (add z h) R B) := by
  let x := exponentData z R B
  let y := exponentData (add z h) R B
  let d := incrementData z h R B
  have hx := exponent_regular z R B hz
  have hy := exponent_regular (add z h) R B hw
  have hd := increment_regular z h R B hz hw
  have sum := GaussianGammaRationalRatioBinding.difference_add_recover A A y x hy hx
  have exp := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent incrementF A A
    (GaussianNameBounds.U incrementF d) (GaussianNameBounds.U A x) (GaussianNameBounds.U A y) d x y
    (exponential_input _ _ hd) (exponential_input _ _ hx) (exponential_input _ _ hy) sum
  have commute := GaussianNameRingLaws.multiply_commutative (E A) (E incrementF)
    (baseData z R B) (valueData z h R B) (base_regular z R B hz) (value_regular z h R B hz hw)
  exact cross_trans _ _ _ _ _ _ commute exp

theorem shifted_value (z h R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] crossEquivalent V nameF (vd (add z h) R B) (data z h R B) := by
  let p := head z h R B
  have hp := constant_regular (Γ := Γ) p
  have base := base_regular z R B hz
  have inc := value_regular z h R B hz hw
  have atTarget := base_regular (add z h) R B hw
  have cross := exponential_shift z h R B hz hw
  have equiv := multiply_cross C C (E A) productF p p (baseData (add z h) R B) (productData z h R B)
    hp hp atTarget (multiply_fast _ _ _ _ base inc) (cross_refl C p hp) (cross_symm _ _ _ _ cross)
  exact cross_trans _ _ _ _ _ _ (centered_factorization z h R B hw) equiv

theorem actual_Barnes_centered_exponential_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     source z R B ⟶ source (add z h) R B ⟶ crossEquivalent V nameF (vd (add z h) R B) (data z h R B)) :=
  closeUniv 4 (.impI (.impI (shifted_value _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredExponentialShift
