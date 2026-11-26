import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianGaussPiPowerSquareRoot
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamilyAppend

/-!
# The independently sampled π half-power in Gauss triplication
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGaussTriplicationPi

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaGaussReferenceSquare (doubledPiBody doubledPiPowerF doubledPiPowerData)
open GaussianGammaGaussReflectionFamily (piBody pi_at pi_rows)
open GaussianGammaGaussReflectionPowerConstant (twoBody two_rows)
open GaussianCyclicSineProductSquare (data)
open GaussianNamedFiniteProductFamily (rowF radius productData)
open GaussianNamedFiniteProductFamilyAppend (family_append_cross family_singleton_cross regular_prefix)
open GaussianNamedBoundedSquareRoot (observations square_root_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast multiply_canonical)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalNonnegativeFractions (fraction_nonnegative multiply_nonnegative_at)
open GaussianRationalNonnegativeProducts (nonnegative)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalHorner (canonical)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF

def doubledPiF : PR 2 := multiplyF P C
def doubledPiData (x : PTm n) : PTm n := multiplyData P C x (naturalPoint two)

theorem doubled_pi_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN doubledPiF (doubledPiData x) :=
  multiply_fast _ _ _ _ (GaussianGammaHalfPiName.name_regular x) (constant_regular _)

private theorem readback (i x : PTm n) :
    Γ ⊢[PRAAx] inst2 doubledPiBody i (data two x) ≐ doubledPiData x := by
  rw [doubledPiBody, GaussianNamedFiniteProductFamilyAlgebra.body_at]
  have e : inst2 twoBody i (data two x) = (naturalPoint two : PTm n) := by simp [twoBody,inst2,two,one]
  rw [e]
  simpa [doubledPiData] using Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (doubledPiData (var 0) : PTm 1)
    (σ := ![inst2 piBody i (data two x)]) (σ' := ![x]) (fun j => by fin_cases j; exact pi_at two x i)

private theorem square_is_power (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent
    (multiplyF doubledPiF doubledPiF) doubledPiPowerF
    (multiplyData doubledPiF doubledPiF (doubledPiData x) (doubledPiData x)) (doubledPiPowerData two x) := by
  let X := data two x
  let F := doubledPiF
  let D := doubledPiPowerF
  let T := doubledPiBody
  let a := doubledPiData x
  let b := productData F T one X
  let c := inst2 T one X
  have h := GaussianNamedFiniteProductFamilyAlgebra.multiply_regular P C piBody twoBody two X
    (pi_rows (Γ := Γ) two x) (two_rows two X)
  have hs := regular_prefix F T one two X (le_succ_self one) h
  have last : Γ ⊢[PRAAx] crossEquivalent D (multiplyF D F) (doubledPiPowerData two x) (multiplyData D F b c) :=
    family_append_cross F T one X h
  have first : Γ ⊢[PRAAx] crossEquivalent D F b a :=
    GaussianGammaRealValues.cross_right_data (readback zero x) (family_singleton_cross F T X hs)
  have reg := doubled_pi_regular (Γ := Γ) x
  have row : Γ ⊢[PRAAx] crossEquivalent F F c a :=
    cross_symm _ _ _ _ (GaussianGammaRealValues.cross_right_data (readback one x).eqSymm (cross_refl F a reg))
  have hc : Γ ⊢[PRAAx] pointCN F c := cross_trans _ _ _ _ _ _ row (cross_symm _ _ _ _ row)
  have hb : Γ ⊢[PRAAx] pointCN D b := cross_trans _ _ _ _ _ _ first (cross_symm _ _ _ _ first)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ last
    (multiply_cross D F F F b a c a hb reg hc reg first row))

private theorem doubled_sample (p x : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 doubledPiF p (doubledPiData x)) ⋏ nonnegative (ap2 doubledPiF p (doubledPiData x)) := by
  let b : PTm n := naturalPoint two
  let s := GaussianFastValueCut.exponent (multiplyModulus P C x b) p
  have hp : Γ ⊢[PRAAx] nonnegative (ap2 P s x) :=
    GaussianRationalNonnegativeProducts.congr (GaussianGammaHalfPiName.sample_at s x).eqSymm
      (fraction_nonnegative _ _ (GaussianGammaHalfRisingFactorial.factorial_positive _))
  have hc : Γ ⊢[PRAAx] nonnegative (ap2 C s b) :=
    GaussianRationalNonnegativeProducts.congr (constant_at s b).eqSymm (fraction_nonnegative two one (le_refl one))
  exact .andI (multiply_canonical P C x b p) (multiply_nonnegative_at P C x b p hp hc)

private theorem doubled_samples (x : PTm n) : Γ ⊢[PRAAx] observations doubledPiF (doubledPiData x) := by
  refine .allI ?_
  simpa [doubledPiData,Syn.shift,two,one] using
    doubled_sample (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)

private theorem power_sample (p x : PTm n) : Γ ⊢[PRAAx] canonical (ap2 doubledPiPowerF p (doubledPiPowerData two x)) ⋏
    nonnegative (ap2 doubledPiPowerF p (doubledPiPowerData two x)) := by
  let f := rowF doubledPiF doubledPiBody
  let R := radius doubledPiF doubledPiBody two (data two x)
  exact .andI (GaussianRationalHorner.canonical_congr
    (GaussianNamedFiniteProductName.name_at f p two R one (data two x))
    (GaussianNamedFiniteProduct.sample_canonical f (GaussianNamedFiniteProductName.clock two R one p) two (data two x)))
    (GaussianGammaGaussIndependentSquareRoot.doubled_power_nonnegative p two x)

private theorem power_samples (x : PTm n) : Γ ⊢[PRAAx] observations doubledPiPowerF (doubledPiPowerData two x) := by
  refine .allI ?_
  simpa [doubledPiPowerData,productData,Syn.shift,two,one] using
    power_sample (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)

theorem pi_half_cross (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGaussPiPowerSquareRoot.nameF doubledPiF
      (GaussianGaussPiPowerSquareRoot.nameData two x) (doubledPiData x) :=
  cross_symm _ _ _ _ (square_root_cross doubledPiF doubledPiPowerF (doubledPiData x) (doubledPiPowerData two x)
    (doubled_pi_regular x) (doubled_samples x) (power_samples x) (square_is_power x))

theorem actual_triplication_pi_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent GaussianGaussPiPowerSquareRoot.nameF doubledPiF
      (GaussianGaussPiPowerSquareRoot.nameData two (var 0)) (doubledPiData (var 0))) :=
  closeUniv 1 (pi_half_cross _)

end LeanProofs.IPRA.Analysis.GaussianGaussTriplicationPi
