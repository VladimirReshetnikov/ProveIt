import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeLogPrimitiveCell
import IPRADerivations.Analysis.Stirling.GaussianStirlingConstant
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# The original named right side of Raabe's formula
-/

set_option autoImplicit false
set_option maxHeartbeats 780000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeRightSide

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_at multiply_fast sum_distance)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedDifference (difference_distance)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianRaabeLogPrimitiveCell (primitive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qmul qmul_canonical positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "ld" => GaussianPositiveRationalLogarithm.data
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData

def productF : PR 2 := multiplyF constantF L
def productData (A D : PTm n) : PTm n := multiplyData constantF L (fraction A D) (ld A D)
def primitiveF : PR 2 := GaussianNamedDifference.nameF productF constantF
def primitiveData (A D : PTm n) : PTm n := GaussianNamedDifference.data (productData A D) (fraction A D)
def nameF : PR 2 := addF primitiveF C
def data (A D w : PTm n) : PTm n := addData (primitiveData A D) (cd w)
def cost (A : PTm n) : PTm n := num 9+two*A

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A D w : PTm n) :
    Syn.subst σ (data A D w) = data (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ w) := by
  simp [data,primitiveData,productData]

private theorem product_regular (A D : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D) :
    Γ ⊢[PRAAx] pointCN productF (productData A D) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianPositiveRationalLogarithm.name_regular A D h)

private theorem primitive_regular (A D : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D) :
    Γ ⊢[PRAAx] pointCN primitiveF (primitiveData A D) :=
  GaussianNamedDifference.name_regular _ _ _ _ (product_regular A D h) (constant_regular _)

theorem regular (A D w : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D) :
    Γ ⊢[PRAAx] pointCN nameF (data A D w) :=
  add_fast _ _ _ _ (primitive_regular A D h) (GaussianStirlingConstant.name_regular w)

private theorem product_error (p A D : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData A D)) (qmul (fraction A D) (sample p A D))
      (two*A) (unit p) := by
  let t := fraction A D
  let k := GaussianFastValueCut.exponent (multiplyModulus constantF L t (ld A D)) p
  let U := unit p
  let V := unit k
  let u := sample k A D
  let v := sample p A D
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) k
  have grow : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have time : Γ ⊢[PRAAx] le A (A*D) :=
    le_congr (one_mul A) (mul_comm D A) (mul_le_mul_right A h.andE₂)
  have held : Γ ⊢[PRAAx] distanceBounded u v two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hV hU) hU
      (by change Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)); ipra_le 𝔞(U)*sl grow)
      (GaussianNameEquivalence.point_at L (ld A D) k p (GaussianPositiveRationalLogarithm.name_regular A D h))
  have read : Γ ⊢[PRAAx] ap2 productF p (productData A D) ≐ qmul t u :=
    (multiply_at constantF L t (ld A D) p).eqTrans
      ((GaussianNameArithmetic.recode_congr (qmul_congr (constant_at k t) (.eqRefl u))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))
  exact distance_congr read.eqSymm (.eqRefl _) (mul_comm A two) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance t u v A two U hU
      (GaussianEulerExponentCompactBounds.fraction_bound A D A h.andE₂ time) held)

private theorem primitive_error (p A D : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 primitiveF p (primitiveData A D)) (primitive p A D)
      (num 6+two*A) (unit p) := by
  let t := fraction A D
  let T := productData A D
  let u := ap2 productF p T
  let v := qmul t (sample p A D)
  have hU := unit_positive (Γ := Γ) p
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 primitiveF p (primitiveData A D)) (qsub u t) (num 6) (unit p) :=
    distance_congr (.eqRefl _) (qsub_congr (.eqRefl u) (constant_at p t)) (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifference.sample_error productF constantF T t p (product_regular A D h) (constant_regular t))
  have second := difference_distance u v t t _ _ _ hU (product_error p A D h) (distance_refl_zero t _ hU)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first second)

theorem sample_error (p A D w : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A D w))
      (qadd (primitive p A D) (ap2 C p (cd w))) (cost A) (unit p) := by
  let t := ap2 C p (cd w)
  let r := ap2 primitiveF p (primitiveData A D)
  have hU := unit_positive (Γ := Γ) p
  have left := add_sample_error primitiveF C (primitiveData A D) (cd w) p
    (primitive_regular A D h) (GaussianStirlingConstant.name_regular w)
  have right := sum_distance r (primitive p A D) t t _ _ _ hU (primitive_error p A D h)
    (distance_refl_zero t _ hU)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU left right)

end LeanProofs.IPRA.Analysis.GaussianRaabeRightSide
