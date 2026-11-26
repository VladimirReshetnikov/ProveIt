import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalPoleFreeRecurrence
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaFactorialValues
import IPRADerivations.Analysis.Gamma.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.Gamma.GaussianGammaInputProperness

/-!
# The original Barnes recurrence on an integer trajectory

At index `i`, the stored center is the original Gaussian unit-shift
trajectory from zero. The pole-free recurrence uses the original Gamma
name on the successor center, where the checked factorial theorem
identifies the multiplier as the exact rational number `i!`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalValue (nameF)
open GaussianBarnesCanonicalHead (source)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaFactorialValues (factorialValue)
open GaussianRationalHorner (ofGaussian positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (oneCode zeroCode scale normSq)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def center (i : PTm n) : PTm n := GaussianGammaShiftTrajectory.point zeroCode one i
def data (i : PTm n) : PTm n := GaussianBarnesCanonicalValue.data (center i) i one
def value (p i : PTm n) : PTm n := ap2 nameF p (data i)
def productData (i : PTm n) : PTm n := multiplyData nameF constantF (data i) (factorialValue i)
def modulus (i : PTm n) : PTm n := multiplyModulus nameF constantF (data i) (factorialValue i)

@[simp] theorem subst_center {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (center i) = center (Syn.subst σ i) := by simp [center,one]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (data i) = data (Syn.subst σ i) := by simp [data,one]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p i : PTm n) :
    Syn.subst σ (value p i) = value (Syn.subst σ p) (Syn.subst σ i) := by simp [value]

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (productData i) = productData (Syn.subst σ i) := by simp [productData]

@[simp] theorem subst_modulus {m : ℕ} (σ : Fin n → PTm m) (i : PTm n) :
    Syn.subst σ (modulus i) = modulus (Syn.subst σ i) := by simp [modulus]

theorem center_zero : Γ ⊢[PRAAx] center (zero : PTm n) ≐ zeroCode :=
  GaussianGammaShiftTrajectory.point_zero zeroCode one

theorem center_succ (i : PTm n) : Γ ⊢[PRAAx] center (succ i) ≐ translated (center i) one one :=
  GaussianGammaShiftTrajectory.point_succ zeroCode one i

theorem center_native (i : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (center i) (scale i oneCode) := by
  refine GaussianRootAlgebra.equal_trans (GaussianGammaShiftTrajectory.point_native zeroCode one i) ?_
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_zero,
      GaussianRootAlgebra.im_zero,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem center_norm (i : PTm n) : Γ ⊢[PRAAx] normSq (center i) ≐ i*i :=
  (GaussianRootAlgebra.normSq_equal (center_native i)).eqTrans
    ((ComplexLogarithmRemainder.normSq_scale i oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring)))

theorem integer_source (i : PTm n) : Γ ⊢[PRAAx] source (center i) i one :=
  .andI (le_refl _) (le_congr (center_norm i).eqSymm (by ipra_ring) (le_refl (i*i)))

theorem value_regular (i : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (data i) :=
  GaussianBarnesCanonicalValue.regular (center i) i one (integer_source i)

private theorem successor_gamma_native (i : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (GaussianGammaFactorialValues.argument i) (translated (center i) one one) := by
  refine GaussianRootAlgebra.equal_trans (GaussianGammaShiftTrajectory.point_native oneCode one i) ?_
  refine GaussianRootAlgebra.equal_trans ?_
    (GaussianRootAlgebra.equal_trans (GaussianRootAlgebra.equal_symm (center_native (succ i)))
      (GaussianRootAlgebra.equal_of_code (center_succ i)))
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem gamma_source (i : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (translated (center i) one one) (i+one) one one one := by
  let z := translated (center i) one one
  have old := GaussianGammaInputProperness.gamma_source_equal _ z _ one one one
    (GaussianGammaFactorialValues.integer_source (Γ := Γ) i) (successor_gamma_native i)
  simpa [one] using Prf.eqSubst
    (GaussianGammaReciprocalInverse.source (var 0) (var 1) one one one : Fm PTm 2)
    ![z,GaussianGammaFactorialValues.radius i] ![z,i+one]
    (fun j => by fin_cases j; exact .eqRefl _; exact add_comm _ _) (by simpa [one] using old)

theorem gamma_factorial (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF constantF
      (GaussianGammaReciprocalInverse.gammaData (translated (center i) one one) (i+one) one one)
      (factorialValue i) := by
  let z := translated (center i) one one
  let g := GaussianGammaReciprocalInverse.gammaF
  have proper := GaussianGammaInputProperness.original_Gamma_proper _ z _ one one one
    (GaussianGammaFactorialValues.integer_source (Γ := Γ) i) (successor_gamma_native i)
  have aligned := GaussianGammaCompactCutoffAlignment.cross_data_congr g g _ _ _ _
    (.eqRefl _) (GaussianGammaFactorialValues.gamma_fields_congr (.eqRefl _) (add_comm _ _) (.eqRefl _) (.eqRefl _)) proper
  exact cross_trans _ _ _ _ _ _ (GaussianNameEquivalence.cross_symm _ _ _ _ aligned)
    (GaussianGammaFactorialValues.original_C21_factorial i)

theorem successor (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent nameF (multiplyF nameF constantF) (data (succ i)) (productData i) := by
  let z := translated (center i) one one
  let x := data i
  let g := GaussianGammaReciprocalInverse.gammaF
  let y := GaussianGammaReciprocalInverse.gammaData z (i+one) one one
  have hs := gamma_source (Γ := Γ) i
  have hg := GaussianGammaReciprocalInverse.gamma_regular z (i+one) one one one hs
  have hx := value_regular (Γ := Γ) i
  have original := GaussianBarnesCanonicalPoleFreeRecurrence.recurrence (center i) i one one one
    (integer_source i) hs
  have replace := GaussianGammaAdjacentCutoff.multiply_cross nameF nameF g constantF x x y (factorialValue i)
    hx hx hg (constant_regular _) (cross_refl _ _ hx) (gamma_factorial i)
  have pointEq : Γ ⊢[PRAAx] data (succ i) ≐ GaussianBarnesCanonicalValue.data z (i+one) one := by
    change Γ ⊢[PRAAx]
      GaussianBarnesCanonicalValue.data (center (succ i)) (succ i) one ≐
        GaussianBarnesCanonicalValue.data (translated (center i) one one) (i+one) one
    ipra_congr (GaussianBarnesCanonicalValue.data (var 0) (var 1) one : PTm 2)
      with [center_succ i, succ_eq_add_one i] using [one]
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ pointEq.eqSymm (.eqRefl _)
    (cross_trans _ _ _ _ _ _ original replace)

theorem successor_error (p i : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (value p (succ i)) (qmul (value p i) (factorialValue i)) (two+(modulus i+one)) (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  have cross := GaussianNameEquivalence.cross_at _ _ _ _ p p (successor (Γ := Γ) i)
  have first : Γ ⊢[PRAAx] distanceBounded (value p (succ i)) (ap2 (multiplyF nameF constantF) p (productData i))
      two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
      (le_of_eq_add (d := zero) (by ipra_ring)) cross
  have raw := GaussianNameRingLaws.multiply_sample_error (Γ := Γ) nameF constantF (data i) (factorialValue i) p
    (value_regular i) (constant_regular _)
  have second := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr
    (.eqRefl _) (constant_at p (factorialValue i))) (.eqRefl _) (.eqRefl _) raw
  exact distance_triangle_same _ _ _ _ _ _ hu first second

theorem actual_Barnes_integer_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let i := var 0; crossEquivalent nameF (multiplyF nameF constantF) (data (succ i)) (productData i)) :=
  closeUniv 1 (successor _)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerRecurrence
