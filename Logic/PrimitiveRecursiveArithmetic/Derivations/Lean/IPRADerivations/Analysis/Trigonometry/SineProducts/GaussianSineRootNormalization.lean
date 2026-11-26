import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineSquaredTrace
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLowerBounds

/-!
# Exact normalization of a sampled sine-root factor

In the squared-trace coordinate Y=4(1−s²), the linear factor of
the root r is 4(r²−s²). Its value at Y=4 is 4r². A positive
separation of r licenses division by r² and gives the normalized
factor 1−s²/r².
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineRootNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul qmul_canonical qzero positive_product ofGaussian_canonical)
open GaussianRationalMetric (qsub qnegative_canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qsub_congr qzero_add
  qmul_zero_left)
open GaussianRationalReciprocal (reciprocal reciprocal_identity)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalLowerBounds (product_lower name_lower)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianSineSquaredTrace (fromSine)
open GaussianFastValueCut (difference_identity)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def normalizedFactor (s r : PTm n) : PTm n :=
  qsub qone (qmul (qmul s s) (reciprocal (qmul r r)))

@[simp] theorem subst_normalizedFactor {l : ℕ} (σ : Fin n → PTm l) (s r : PTm n) :
    Syn.subst σ (normalizedFactor s r) = normalizedFactor (Syn.subst σ s) (Syn.subst σ r) := by
  simp [normalizedFactor]

theorem trace_difference (s r : PTm n) : Γ ⊢[PRAAx]
    qsub (fromSine s) (fromSine r) ≐ qmul (naturalPoint (num 4)) (qsub (qmul r r) (qmul s s)) := by
  let X := qmul s s
  let U := qmul r r
  let C : PTm n := naturalPoint (num 4)
  have e : Γ ⊢[PRAAx] qsub (qsub qone X) (qsub qone U) ≐ qsub U X :=
    (difference_identity qone X qone U).eqTrans
      ((qsub_congr (GaussianCoefficientNormOrder.qsub_self qone) (.eqRefl _)).eqTrans
        ((qzero_add _ (qnegative_canonical _)).eqTrans (GaussianRationalDistanceOrder.reversed_difference X U)))
  exact (GaussianRationalRoundedPower.multiplication_difference C (qsub qone X) (qsub qone U)).eqTrans
    (qmul_congr (.eqRefl _) e)

theorem trace_at_zero : Γ ⊢[PRAAx] fromSine (qzero : PTm n) ≐ naturalPoint (num 4) := by
  unfold fromSine
  exact (qmul_congr (.eqRefl _) ((qsub_congr (.eqRefl _) (qmul_zero_left qzero)).eqTrans
    (GaussianRationalReconstruction.qsub_zero_right qone qone_canonical))).eqTrans
    (qmul_one_right _ (ofGaussian_canonical _ _ (le_refl _)))

theorem four_difference (r : PTm n) : Γ ⊢[PRAAx]
    qsub (naturalPoint (num 4)) (fromSine r) ≐ qmul (naturalPoint (num 4)) (qmul r r) :=
  (qsub_congr trace_at_zero.eqSymm (.eqRefl _)).eqTrans
    ((trace_difference qzero r).eqTrans
      (qmul_congr (.eqRefl _) ((qsub_congr (.eqRefl _) (qmul_zero_left qzero)).eqTrans
        (GaussianRationalReconstruction.qsub_zero_right _ (qmul_canonical _ _)))))

theorem root_factor_normalization (s r D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] GaussianNameReciprocal.lower r D) :
    Γ ⊢[PRAAx] qmul (qsub (naturalPoint (num 4)) (fromSine r)) (normalizedFactor s r) ≐
      qsub (fromSine s) (fromSine r) := by
  let X := qmul s s
  let U := qmul r r
  let V := reciprocal U
  let C : PTm n := naturalPoint (num 4)
  have hD2 := positive_product D D hD hD
  have hR : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower r one D := hr
  have low := product_lower r r one D one D hD hD hR hR
  have margin : Γ ⊢[PRAAx] GaussianNameReciprocal.lower U (D*D) :=
    name_lower U (one*one) (D*D) (le_congr (.eqRefl _) (one_mul one).eqSymm (le_refl _)) hD2 low
  have inv : Γ ⊢[PRAAx] qmul U V ≐ qone :=
    reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ _ hD2 margin)
  have cross : Γ ⊢[PRAAx] qmul U (qmul X V) ≐ X :=
    (qmul_associative U X V).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative U X) (.eqRefl _)).eqTrans
        ((qmul_associative X U V).eqTrans ((qmul_congr (.eqRefl _) inv).eqTrans
          (qmul_one_right X (qmul_canonical _ _)))))
  have inner : Γ ⊢[PRAAx] qmul U (normalizedFactor s r) ≐ qsub U X :=
    (GaussianRationalRoundedPower.multiplication_difference U qone (qmul X V)).eqSymm.eqTrans
      (qsub_congr (qmul_one_right U (qmul_canonical _ _)) cross)
  exact (qmul_congr (four_difference r) (.eqRefl _)).eqTrans
    ((qmul_associative C U (normalizedFactor s r)).eqTrans
      ((qmul_congr (.eqRefl _) inner).eqTrans (trace_difference s r).eqSymm))

theorem actual_sampled_sine_root_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ GaussianNameReciprocal.lower (var 1) (var 2) ⟶
      qmul (qsub (naturalPoint (num 4)) (fromSine (var 1))) (normalizedFactor (var 0) (var 1)) ≐
        qsub (fromSine (var 0)) (fromSine (var 1))) :=
  closeUniv 3 (.impI (.impI (root_factor_normalization _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineRootNormalization
