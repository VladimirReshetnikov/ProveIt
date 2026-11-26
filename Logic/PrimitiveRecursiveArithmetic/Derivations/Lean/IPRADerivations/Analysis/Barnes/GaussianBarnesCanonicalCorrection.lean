import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalCubicName
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalFactor

/-!
# Exact cancellation in the Barnes factor exponent

Multiplying the first two local logarithm terms at z/(B k) by k
gives the negative of the direct factor's original correction.
The equality is between the actual Gaussian-rational codes.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrection

open_ipra
open ComplexLogarithmName (baseNumerator baseDenominator)
open ComplexLogarithmRemainder (mul scale)
open GaussianBarnesCanonicalCubicName (base)
open GaussianBarnesCanonicalFactor (correction)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul qadd qzero represents represents_congr positive_product)
open GaussianRationalNaturalScale (natScale natScale_as_product natScale_represents natScale_canonical)
open GaussianRationalMetric (qnegative qnegative_represents qnegative_canonical qsub qsub_canonical qsub_represents)
open GaussianRationalSyntheticDivision (rescale_to qadd_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exact_correction (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] correction z B k ≐ qnegative (natScale k (base z (B*k))) := by
  let N := B*k
  let E := two*N
  let D := B*E
  let W := baseDenominator N
  let a := ofGaussian z B
  let b := ofGaussian z E
  let c := baseNumerator z N
  let w := base z N
  let u := correction z B k
  let v := qnegative (natScale k w)
  let g : PTm n → PTm n := ComplexLogarithmRemainder.neg
  have hN := positive_product B k hB hk
  have hE := positive_product two N (le_succ_self one) hN
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hE
  have hW := ComplexLogarithmName.base_positive N hN
  have hz := ofGaussian_represents z B hB
  have right := rescale_to a z B E D hz (.eqRefl _)
  have left := GaussianRationalHorner.qmul_represents a b z z B E hB hE hz (ofGaussian_represents z E hE)
  have original := qsub_represents (qmul a b) a (mul z z) (scale E z) D hD left right
  have es : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRootAlgebra.sub (mul z z) (scale E z)) (g c) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [g,c,baseNumerator,E,GaussianRootAlgebra.sub,GaussianRootAlgebra.re_add,
        GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg] <;> ring
  have rep : Γ ⊢[PRAAx] represents u (g c) D :=
    represents_congr (.eqRefl _) es (.eqRefl _) original
  have en : Γ ⊢[PRAAx] D*k ≐ W := by dsimp only [D,E,W,N,baseDenominator]; ipra_ring
  have moved := rescale_to u (g c) D k W rep en
  have target := qnegative_represents (natScale k w) (scale k c) W
    (natScale_represents k w c W hW (ofGaussian_represents c W hW))
  have commute : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (g (scale k c)) (scale k (g c)) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [g,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale] <;> ring
  exact GaussianRationalHorner.canonical_unique u v (scale k (g c)) W (qsub_canonical _ _)
    (qnegative_canonical _) hW moved (represents_congr (.eqRefl _) commute (.eqRefl _) target)

private theorem scale_sum (k x y : PTm n) :
    Γ ⊢[PRAAx] natScale k (qadd x y) ≐ qadd (natScale k x) (natScale k y) :=
  (natScale_as_product k (qadd x y)).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (natScale_as_product k x).eqSymm (natScale_as_product k y).eqSymm))

theorem cancel (x z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qadd (natScale k (qadd x (base z (B*k)))) (correction z B k) ≐ natScale k x := by
  let b := natScale k (base z (B*k))
  have e : Γ ⊢[PRAAx] qadd b (correction z B k) ≐ qzero :=
    (qadd_congr (.eqRefl b) (exact_correction z B k hB hk)).eqTrans (GaussianCoefficientNormOrder.qsub_self b)
  exact (qadd_congr (scale_sum k x (base z (B*k))) (.eqRefl _)).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
      ((qadd_congr (.eqRefl _) e).eqTrans (GaussianReciprocalHorner.qadd_zero_right _ (natScale_canonical k x))))

theorem actual_Barnes_factor_correction_cancellation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 2) ⟶ le one (var 3) ⟶
        qadd (natScale (var 3) (qadd (var 0) (base (var 1) (var 2*var 3)))) (correction (var 1) (var 2) (var 3))
          ≐ natScale (var 3) (var 0)) :=
  closeUniv 4 (.impI (.impI (cancel _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrection
