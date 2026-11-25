import IPRADerivations.Analysis.GaussianBinetKernelPi
import IPRADerivations.Analysis.GaussianPiRationalScale
import IPRADerivations.Analysis.GaussianEulerDecayFactorBounds

/-!
# The original exponential at signed Pi-scaled rational times

Use the actual named Pi and its verified rational sample. Reading each
scaled sample exactly gives a positive real lower bound at the
positive scale. Both signed exponentials use the existing exponential
evaluator with a radius derived from the original scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelPi (sample_fraction denominator_positive sample_margins)
open GaussianDominantPairAlgebra (radiusPoint radius_multiply)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameBounds (U)
open GaussianPositiveRealArithmetic (positive positive_congr)
open GaussianRationalHorner (canonical positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianStirlingConstant (piNumerator piDenominator)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Pi" => GaussianGammaHalfPiName.nameF

def scaleBudget (A : PTm n) : PTm n := two*A+one
def scaleData (s : Bool) (A B : PTm n) : PTm n :=
  GaussianPiRationalScale.data s (two*A) B (scaleBudget A) zero

abbrev scaleF : PR 2 := GaussianPiRationalScale.nameF
def expRadius (A : PTm n) : PTm n := scaleBudget A*U Pi zero
def expData (s : Bool) (A B : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (expRadius A) (scaleData s A B)

abbrev expF : PR 2 := GaussianRadiusExponentialName.nameF scaleF

@[simp] theorem subst_scaleBudget {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (scaleBudget A) = scaleBudget (Syn.subst σ A) := by simp [scaleBudget,two,one]

@[simp] theorem subst_scaleData {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (A B : PTm n) :
    Syn.subst σ (scaleData s A B) = scaleData s (Syn.subst σ A) (Syn.subst σ B) := by simp [scaleData,two]

@[simp] theorem subst_expRadius {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (expRadius A) = expRadius (Syn.subst σ A) := by simp [expRadius]

@[simp] theorem subst_expData {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (A B : PTm n) :
    Syn.subst σ (expData s A B) = expData s (Syn.subst σ A) (Syn.subst σ B) := by simp [expData]

theorem exp_input (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input scaleF (expRadius A) (scaleData s A B) := by
  have budget : Γ ⊢[PRAAx] le (two*A) (scaleBudget A*B) :=
    le_trans (le_add_right (two*A) one)
      (le_congr (one_mul (scaleBudget A)) (mul_comm B (scaleBudget A))
        (mul_le_mul_right (scaleBudget A) hB))
  exact GaussianPiRationalScale.exponential_input s (two*A) B (scaleBudget A) zero hB budget

theorem exp_regular (s : Bool) (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN expF (expData s A B) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exp_input s A B hB)

def piClock (p A : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p (scaleBudget A)

theorem scale_readback (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ap2 scaleF p (scaleData false A B) ≐
      radiusPoint ((two*A)*piNumerator (piClock p A)) (B*piDenominator (piClock p A)) := by
  let k := piClock p A
  let b := piDenominator k
  let a := piNumerator k
  have h := denominator_positive (Γ := Γ) k
  have e := (sample_fraction (Γ := Γ) k).eqTrans
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b h)
  exact (GaussianBoundedConstantProductName.sample_at Pi p (scaleBudget A)
    (GaussianPiRationalScale.point false (two*A) B) zero).eqTrans
    ((qmul_congr (.eqRefl (radiusPoint (two*A) B)) e).eqTrans (radius_multiply (two*A) B a b hB h))

theorem scale_positive (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] positive (ap2 scaleF p (scaleData false A B)) ⋏ canonical (ap2 scaleF p (scaleData false A B)) := by
  let k := piClock p A
  let a := (two*A)*piNumerator k
  let b := B*piDenominator k
  have h := positive_product B (piDenominator k) hB (denominator_positive k)
  have e := scale_readback p A B hB
  exact .andI (positive_congr e.eqSymm (GaussianPositiveExponentialTermBound.actual_positive_fraction a b h))
    (GaussianRationalHorner.canonical_congr e (GaussianRationalHorner.ofGaussian_canonical _ _ h))

theorem scale_lower_order (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint (num 4*A) B)) (fstT (ap2 scaleF p (scaleData false A B))) := by
  let k := piClock p A
  let u := piNumerator k
  let v := piDenominator k
  have hv := denominator_positive (Γ := Γ) k
  have hb := positive_product B v hB hv
  have lower := mul_le_mul_right (B*(two*A)) (sample_margins (Γ := Γ) k).andE₁
  have result : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint (num 4*A) B)) (fstT (radiusPoint ((two*A)*u) (B*v))) :=
    GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hB hb
      (GaussianPositiveExponentialOrder.radius_real_representation _ _ hB)
      (GaussianPositiveExponentialOrder.radius_real_representation _ _ hb)
      (le_congr (by ipra_ring) (by ipra_ring) lower)
  exact rationalLE_congr (.eqRefl _) (congrFst (scale_readback p A B hB)).eqSymm result

end LeanProofs.IPRA.Analysis.GaussianBinetBoseExponential
