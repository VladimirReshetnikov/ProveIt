import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrationByPartsParameterShift

/-!
# The actual Euler name after an arbitrary encoded parameter increment

The perturbed native numerator is D*z+B*h and its actual denominator is
B*D. Genuine rational representation proves coefficient addition. The
original named multiplication, exponent addition and exponential product
laws then identify the perturbed Euler name with the original Euler name
times the exponential of (h/D)*log(a/b). All independently computed
normalizers and name clocks remain in the displayed programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerParameterExponentialIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (coefficient logarithmF powerExponentF powerExponentData powerRadius powerF powerData
  nameF data source power_regular name_regular power_input)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (qadd qmul ofGaussian canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shifted (z B h D : PTm n) : PTm n := ComplexLogarithmRemainder.add
  (ComplexLogarithmRemainder.scale D z) (ComplexLogarithmRemainder.scale B h)
def incrementData (h D a b : PTm n) : PTm n :=
  multiplyData constantF logarithmF (ofGaussian h D) (GaussianPositiveRationalLogarithm.data a b)
abbrev incrementF : PR 2 := powerExponentF
def incrementRadius (h D a b : PTm n) : PTm n := GaussianNameBounds.U incrementF (incrementData h D a b)
def exponentialData (h D a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (incrementRadius h D a b) (incrementData h D a b)
abbrev exponentialF : PR 2 := GaussianRadiusExponentialName.nameF incrementF
def productF : PR 2 := multiplyF nameF exponentialF
def productData (z B h D a b : PTm n) : PTm n := multiplyData nameF exponentialF (data z B a b) (exponentialData h D a b)

@[simp] theorem subst_shifted {m : ℕ} (σ : Fin n → PTm m) (z B h D : PTm n) :
    Syn.subst σ (shifted z B h D) = shifted (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ h) (Syn.subst σ D) := by
  simp [shifted,ComplexLogarithmRemainder.add,ComplexLogarithmRemainder.scale]
@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (h D a b : PTm n) :
    Syn.subst σ (incrementData h D a b) = incrementData (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [incrementData]
@[simp] theorem subst_incrementRadius {m : ℕ} (σ : Fin n → PTm m) (h D a b : PTm n) :
    Syn.subst σ (incrementRadius h D a b) = incrementRadius (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [incrementRadius]
@[simp] theorem subst_exponentialData {m : ℕ} (σ : Fin n → PTm m) (h D a b : PTm n) :
    Syn.subst σ (exponentialData h D a b) = exponentialData (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [exponentialData]
@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (z B h D a b : PTm n) :
    Syn.subst σ (productData z B h D a b) = productData (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ h) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by simp [productData]

/-- The original coefficient is transported at its true mixed denominator. -/
theorem shifted_coefficient (z B h D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    coefficient (shifted z B h D) (B*D) ≐ qadd (coefficient z B) (ofGaussian h D) := by
  have bd := positive_product _ _ hB hD
  have left := GaussianEulerIntegrandName.coefficient_represents (shifted z B h D) (B*D) bd
  have first := GaussianRationalHorner.represents_rescale _ _ _ D (GaussianEulerIntegrandName.coefficient_represents z B hB)
  have second := GaussianRationalSyntheticDivision.rescale_to _ _ _ B (B*D)
    (GaussianRationalHorner.ofGaussian_represents h D hD) (mul_comm _ _)
  have right := GaussianRationalHorner.qadd_represents _ _ _ _ _ bd first second
  apply canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) bd (hrv := right)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [shifted,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

theorem increment_regular (h D a b : PTm n) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    pointCN incrementF (incrementData h D a b) :=
  multiply_fast constantF logarithmF _ _ (constant_regular _) (GaussianPositiveRationalLogarithm.name_regular a b ht)
theorem increment_input (h D a b : PTm n) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input incrementF (incrementRadius h D a b) (incrementData h D a b) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _ (increment_regular h D a b ht)
theorem exponential_regular (h D a b : PTm n) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) : Γ ⊢[PRAAx]
    pointCN exponentialF (exponentialData h D a b) := GaussianRadiusExponentialName.name_regular _ _ _ (increment_input h D a b ht)

/-- Exponent addition is a consequence of the exact coefficient identity
and the actual named distributive law. -/
theorem power_exponent_addition (z B h D a b : PTm n)
    (hs : Γ ⊢[PRAAx] source z B a b) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    crossEquivalent (addF powerExponentF incrementF) powerExponentF
      (addData (powerExponentData z B a b) (incrementData h D a b)) (powerExponentData (shifted z B h D) (B*D) a b) := by
  let x := coefficient z B
  let y := ofGaussian h D
  let c := coefficient (shifted z B h D) (B*D)
  let l := GaussianPositiveRationalLogarithm.data a b
  have hx := constant_regular (Γ := Γ) x
  have hy := constant_regular (Γ := Γ) y
  have hc := constant_regular (Γ := Γ) c
  have hl := GaussianPositiveRationalLogarithm.name_regular a b hs.andE₂
  have sum := GaussianNameArithmetic.add_fast constantF constantF x y hx hy
  have distribute := GaussianNameRingLaws.right_distributive constantF constantF logarithmF x y l hx hy hl
  have coeff := cross_trans _ _ _ _ _ _ (GaussianGammaEulerShift.constant_sum_cross x y)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (shifted_coefficient z B h D hs.andE₁ hD).eqSymm)
  have last := GaussianGammaAdjacentCutoff.multiply_cross (addF constantF constantF) constantF logarithmF logarithmF
    (addData x y) c l l sum hc hl hl coeff (cross_refl _ _ hl)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ distribute) last

theorem original_power_product (z B h D a b : PTm n)
    (hs : Γ ⊢[PRAAx] source z B a b) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    crossEquivalent powerF (multiplyF powerF exponentialF)
      (powerData (shifted z B h D) (B*D) a b)
      (multiplyData powerF exponentialF (powerData z B a b) (exponentialData h D a b)) := by
  have hp : Γ ⊢[PRAAx] source (shifted z B h D) (B*D) a b := .andI (positive_product _ _ hs.andE₁ hD) hs.andE₂
  exact cross_symm _ _ _ _ (GaussianGammaFoldedApproximantBalance.exponential_product_equivalent powerExponentF incrementF powerExponentF
    (powerRadius z B a b) (incrementRadius h D a b) (powerRadius (shifted z B h D) (B*D) a b)
    (powerExponentData z B a b) (incrementData h D a b) (powerExponentData (shifted z B h D) (B*D) a b)
    (power_input z B a b hs) (increment_input h D a b hs.andE₂) (power_input _ _ _ _ hp)
    (power_exponent_addition z B h D a b hs hD))

/-- The perturbed original Euler program is identified by the actual
exponential product law, with no parameter-Taylor or Gamma premise. -/
theorem original_integrand_product (z B h D a b : PTm n)
    (hs : Γ ⊢[PRAAx] source z B a b) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    crossEquivalent nameF productF (data (shifted z B h D) (B*D) a b) (productData z B h D a b) := by
  let P := powerF
  let I := exponentialF
  let F := GaussianEulerIntegrandName.decayF
  let x := powerData z B a b
  let y := exponentialData h D a b
  let t := GaussianEulerIntegrandName.decayData a b
  have hp := power_regular z B a b hs
  have hi := exponential_regular h D a b hs.andE₂
  have hd := GaussianRadiusExponentialName.name_regular (Γ := Γ) constantF _ _
    (GaussianGammaFiniteApproximantName.exponential_input constantF (GaussianEulerIntegrandName.decayPoint a b) (constant_regular _))
  have hshift : Γ ⊢[PRAAx] source (shifted z B h D) (B*D) a b := .andI (positive_product _ _ hs.andE₁ hD) hs.andE₂
  have start := cross_symm _ _ _ _ (GaussianEulerIntegrandName.original_power_times_decay _ _ _ _ hshift)
  have first := GaussianGammaAdjacentCutoff.multiply_cross P (multiplyF P I) F F
    (powerData (shifted z B h D) (B*D) a b) (multiplyData P I x y) t t
    (power_regular _ _ _ _ hshift) (multiply_fast P I x y hp hi) hd hd
    (original_power_product z B h D a b hs hD) (cross_refl _ _ hd)
  have assoc := GaussianNameRingLaws.multiply_associative P I F x y t hp hi hd
  have commute := GaussianGammaAdjacentCutoff.multiply_cross P P (multiplyF I F) (multiplyF F I)
    x x (multiplyData I F y t) (multiplyData F I t y) hp hp
    (multiply_fast I F y t hi hd) (multiply_fast F I t y hd hi) (cross_refl _ _ hp)
    (GaussianNameRingLaws.multiply_commutative I F y t hi hd)
  have back := cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_associative P F I x t y hp hd hi)
  have last := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF P F) nameF I I
    (GaussianEulerIntegrandName.productData z B a b) (data z B a b) y y
    (multiply_fast P F x t hp hd) (name_regular z B a b hs) hi hi
    (GaussianEulerIntegrandName.original_power_times_decay z B a b hs) (cross_refl _ _ hi)
  exact cross_trans _ _ _ _ _ _ start (cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ commute (cross_trans _ _ _ _ _ _ back last))))

theorem original_encoded_Euler_parameter_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 1) (var 4) (var 5) ⋏ le one (var 3)) ⟶
      crossEquivalent nameF productF (data (shifted (var 0) (var 1) (var 2) (var 3)) (var 1*var 3) (var 4) (var 5))
        (productData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_integrand_product _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerParameterExponentialIncrement
