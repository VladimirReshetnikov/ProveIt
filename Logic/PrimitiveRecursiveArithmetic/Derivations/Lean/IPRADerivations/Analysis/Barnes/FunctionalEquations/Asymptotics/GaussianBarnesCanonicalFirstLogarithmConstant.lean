import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.GaussianBarnesCanonicalPositiveFirstLogarithmPrefactor

/-!
# Constant in the original positive Barnes logarithmic derivative

The original prefactor exponent's derivative at centered argument zero
is the original Stirling constant minus one half.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmConstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalPrefactor
  (linearF quadraticF quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular
    polynomialF correctionF negativeHalf)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf linearOf quadraticOf polynomialOf correctionOf)
open GaussianBarnesCanonicalPrefactorInverse (exponentF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaTwoShiftNamedSize (constant_product)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameConjugation (equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_at one_fast zeroF zero_at zero_fast multiply_one_left)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (qzero)
open GaussianRationalReciprocal (qone)
open GaussianReciprocalHorner (qmul_one_right)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "T" => GaussianStirlingConstant.nameF
local notation "td" => GaussianStirlingConstant.nameData

def nameF : PR 2 := addF T C

def data : PTm n := addData (td zero) negativeHalf

theorem regular : Γ ⊢[PRAAx] pointCN nameF (data : PTm n) :=
  add_fast _ _ _ _ (GaussianStirlingConstant.name_regular zero) (constant_regular _)

private theorem linear_at_one : Γ ⊢[PRAAx] crossEquivalent linearF T (linearOf (qone : PTm n)) (td zero) := by
  let x : PTm n := td zero
  have ht := GaussianStirlingConstant.name_regular (Γ := Γ) zero
  have hOne : Γ ⊢[PRAAx] crossEquivalent C oneF (qone : PTm n) x := by
    apply equal_samples_cross _ _ _ _ (constant_regular _) (one_fast _)
    refine .allI ?_
    simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalReciprocal.subst_qone] using
      (constant_at (var 0) qone).eqTrans (one_at (var 0) (Syn.shift x)).eqSymm
  have h := multiply_cross C oneF T T qone x x x (constant_regular _) (one_fast _) ht ht
    hOne (cross_refl _ _ ht)
  exact cross_trans _ _ _ _ _ _ h (multiply_one_left T x ht)

private theorem quadratic_at_zero : Γ ⊢[PRAAx] crossEquivalent quadraticF zeroF (quadraticOf (qzero : PTm n)) qone := by
  apply equal_samples_cross _ _ _ _ (multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular)
    (zero_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,quadraticOf,quadraticCoefficientData,
    GaussianNameArithmetic.subst_multiplyData,GaussianNameArithmetic.subst_addData,
    GaussianRationalHorner.subst_qzero,GaussianRationalReciprocal.subst_qone,ConciseIPRA.PTm.subst_zero] using
    (GaussianGammaRationalWendelBoundary.zero_product_at quadraticCoefficientF (var 0) qzero
      (quadraticCoefficientData : PTm (n+1)) (.eqRefl _)).eqTrans (zero_at (var 0) qone).eqSymm

private theorem correction_at_one : Γ ⊢[PRAAx] crossEquivalent correctionF C
    (correctionOf (qone : PTm n) qzero) negativeHalf := by
  let t : PTm n := qone
  let v : PTm n := negativeHalf
  let q := quadraticOf (qzero : PTm n)
  let p := polynomialOf t qzero
  have ht := constant_regular (Γ := Γ) t
  have hv := constant_regular (Γ := Γ) v
  have hq : Γ ⊢[PRAAx] pointCN quadraticF q :=
    multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular
  have hs : Γ ⊢[PRAAx] pointCN polynomialF p := add_fast _ _ _ _ ht hq
  have polynomial := cross_trans _ _ _ _ _ _
    (add_cross C C quadraticF zeroF t t q t ht ht hq (zero_fast _) (cross_refl _ _ ht) quadratic_at_zero)
    (GaussianNameRingLaws.add_zero C t ht)
  have left := multiply_cross C C polynomialF C v v p t hv hv hs ht (cross_refl _ _ hv) polynomial
  exact cross_trans _ _ _ _ _ _ left (constant_product v t v (qmul_one_right v (GaussianRationalMetric.qnegative_canonical _)))

theorem original_cross : Γ ⊢[PRAAx] crossEquivalent exponentF nameF (exponentOf (qone : PTm n) qzero) data := by
  let t : PTm n := qone
  let v : PTm n := negativeHalf
  have linear : Γ ⊢[PRAAx] pointCN linearF (linearOf t) :=
    multiply_fast _ _ _ _ (constant_regular _) (GaussianStirlingConstant.name_regular zero)
  have quadratic : Γ ⊢[PRAAx] pointCN quadraticF (quadraticOf (qzero : PTm n)) :=
    multiply_fast _ _ _ _ (constant_regular _) quadratic_coefficient_regular
  have polynomial : Γ ⊢[PRAAx] pointCN polynomialF (polynomialOf t qzero) :=
    add_fast _ _ _ _ (constant_regular _) quadratic
  have correction : Γ ⊢[PRAAx] pointCN correctionF (correctionOf t qzero) :=
    multiply_fast _ _ _ _ (constant_regular _) polynomial
  exact add_cross linearF T correctionF C (linearOf t) (td zero) (correctionOf t qzero) v
    linear (GaussianStirlingConstant.name_regular zero) correction (constant_regular _) linear_at_one correction_at_one

theorem actual_Barnes_first_logarithm_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent exponentF nameF (exponentOf qone qzero) data :=
  original_cross

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmConstant
