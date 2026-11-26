import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperTailPointwise
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Scalar majorant for an actual upper-time Euler grid cell

At a common observation precision the pointwise majorant is the
original scalar half-decay observation multiplied by `2^R R!` and
augmented by its fixed dyadic correction. Its embedding differs
from the scaled literal half-decay by at most `(3·2^R R!+1)·2^-p`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperTailScalar

open_ipra
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerUpperTailPointwise (majorantTop majorantBottom majorant_bottom_positive)
open GaussianEulerWeightedHalfDecay (majorant halfSample)
open GaussianEulerHalfDecayReference (scalar numerator denominator denominator_positive scalar_representation decay_reference_error)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalSumMajorant (majorized from_representation)
open GaussianRationalHorner (qadd qmul scalar_congr positive_product)
open GaussianRationalDistanceOrder (distance_triangle_same distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open RationalGaussianEmbedding (embed embed_add embed_multiply embed_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def budget (R : PTm n) : PTm n := num 3*majorant R+one
def scalarMajorant (p R a b : PTm n) : PTm n :=
  fraction (majorantTop p p R a b) (majorantBottom p p a b)

ipra_subst budget
ipra_subst scalarMajorant

theorem original_cell_majorized (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) :
    Γ ⊢[PRAAx] majorized (GaussianEulerIntegrandName.sample p z B a b) (scalarMajorant p R a b) := by
  have den := majorant_bottom_positive (Γ := Γ) p p a b
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (scalarMajorant p R a b)
      (ZT.ofNat (majorantTop p p R a b)) (majorantBottom p p a b) :=
    RationalIntegerNormalization.normalize_preserves_value _ _ den
  exact from_representation _ _ _ _ den (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (GaussianEulerUpperTailPointwise.original_upper_tail_pointwise p p z R B a b h)

private theorem fraction_embedding (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] embed (fraction a b) ≐ radiusPoint a b :=
  (GaussianEulerDecayOrder.fraction_embedding a b hb).eqTrans
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb)

theorem scalar_majorant_sum (p R a b : PTm n) : Γ ⊢[PRAAx]
    scalarMajorant p R a b ≐
      RationalArithmetic.add (RationalArithmetic.multiply (fraction (majorant R) one) (scalar p a b))
        (fraction (majorant R+one) (unit p)) := by
  let M := majorant R
  let U := unit p
  let E := denominator p a b
  let N := numerator p a b
  let x := fraction M one
  let y := scalar p a b
  let k := fraction (M+one) U
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have he : Γ ⊢[PRAAx] le one E := denominator_positive p a b
  have hd := majorant_bottom_positive (Γ := Γ) p p a b
  have rr : Γ ⊢[PRAAx] RationalArithmetic.represents x (ZT.ofNat M) one :=
    RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one)
  have rp : Γ ⊢[PRAAx] RationalArithmetic.represents (RationalArithmetic.multiply x y) (ZT.ofNat (M*N)) E :=
    scalar_congr (.eqRefl _) (by apply ZT.derive; simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]; rfl)
      (one_mul E) (RationalRepresentations.represents_multiply _ _ _ _ _ _ rr (scalar_representation p a b))
  have rk : Γ ⊢[PRAAx] RationalArithmetic.represents k (ZT.ofNat (M+one)) U :=
    RationalIntegerNormalization.normalize_preserves_value _ _ hu
  have rs : Γ ⊢[PRAAx] RationalArithmetic.represents (RationalArithmetic.add (RationalArithmetic.multiply x y) k)
      (ZT.ofNat (M*N*U+(M+one)*E)) (E*U) :=
    scalar_congr (.eqRefl _) (by apply ZT.derive; simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add])
      (.eqRefl _) (RationalRepresentations.represents_add _ _ _ _ _ _ rp rk)
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hd) (RationalArithmetic.add_guard _ _)
    (RationalIntegerNormalization.normalize_preserves_value _ _ hd) rs hd
    (positive_product _ _ he hu) (by
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,majorantTop,majorantBottom,
        GaussianEulerUpperTailPointwise.referenceTop,GaussianEulerUpperTailPointwise.referenceBottom]
      ipra_simps
      ring)

theorem scalar_majorant_scaled_reference_error (p R a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (embed (scalarMajorant p R a b))
      (qmul (radiusPoint (majorant R) one) (halfSample p a b)) (budget R) (unit p) := by
  let M := majorant R
  let U := unit p
  let r := radiusPoint M one
  let y := embed (scalar p a b)
  let k := embed (fraction (M+one) U)
  let a₁ := qmul r y
  let a₂ := qmul r (halfSample p a b)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have e : Γ ⊢[PRAAx] embed (scalarMajorant p R a b) ≐ qadd a₁ k :=
    (RationalGaussianRealPart.embed_congr (scalar_majorant_sum p R a b)).eqTrans
      ((embed_add _ _).eqTrans (GaussianRationalSyntheticDivision.qadd_congr
        ((embed_multiply _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr
          (fraction_embedding M one (le_refl one)) (.eqRefl _))) (.eqRefl k)))
  have near : Γ ⊢[PRAAx] distanceBounded (embed (scalarMajorant p R a b)) a₁ (M+one) U :=
    bound_congr ((GaussianRationalSyntheticDivision.qsub_congr e (.eqRefl a₁)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (embed_canonical _))).eqSymm
      (.eqRefl _) (.eqRefl _) (bound_congr (fraction_embedding _ _ hU).eqSymm (.eqRefl _) (.eqRefl _)
        (radius_bounded _ _ hU))
  have decay := distance_radius_mono y (halfSample p a b) (U+U) (U*U) two U
    (positive_product _ _ hU hU) hU (le_of_eq_add (d := zero) (by ipra_ring))
    (decay_reference_error p p a b hb)
  have far : Γ ⊢[PRAAx] distanceBounded a₁ a₂ (M*two) U :=
    GaussianApproximateInverseDistance.multiply_distance r y _ M two U hU
      (radius_bounded M one (le_refl one)) decay
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU near far)

theorem actual_upper_tail_scalar_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (embed (scalarMajorant (var 0) (var 1) (var 2) (var 3)))
      (qmul (radiusPoint (majorant (var 1)) one) (halfSample (var 0) (var 2) (var 3))) (budget (var 1)) (unit (var 0))) :=
  closeUniv 4 (.impI (scalar_majorant_scaled_reference_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperTailScalar
