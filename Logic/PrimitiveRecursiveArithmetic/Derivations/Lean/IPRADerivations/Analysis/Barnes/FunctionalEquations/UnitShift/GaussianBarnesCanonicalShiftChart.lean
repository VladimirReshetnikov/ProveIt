import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalCorrectionShift
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactor
import IPRADerivations.Analysis.Barnes.FunctionalEquations.UnitShift.GaussianBarnesCanonicalTerminalRemainder

/-!
# Exact chart arithmetic for the Barnes unit shift

The rational point, translated point, and midpoint use their actual
canonical codes. The midpoint bound and translated disk depend on the
original disk radius and work uniformly over encoded denominators.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalShiftChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode bounded bounded_add bounded_mono bounded_scale normSq_scale normSq_one)
open GaussianBarnesCanonicalCorrectionShift (halfShift)
open GaussianGammaEulerHeadLower (translated)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qmul positive_product ofGaussian ofGaussian_canonical ofGaussian_represents
  qadd_canonical qmul_canonical qadd_represents qmul_represents canonical_unique represents_rescale represents_congr)
open GaussianRationalMetric (qsub qnegative qnegative_represents qnegative_canonical)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_mul im_mul re_neg im_neg re_scale im_scale re_one im_one)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem translated_fraction (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (ofGaussian z B) qone ≐ ofGaussian (translated z B one) B := by
  have lhs := qadd_represents _ _ z (scale B oneCode) B hB
    (ofGaussian_represents z B hB) (qone_represents_scaled B)
  apply canonical_unique _ _ _ B (qadd_canonical _ _) (ofGaussian_canonical _ _ hB) hB lhs
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (ofGaussian_represents (translated z B one) B hB)
  apply equal_of_values <;> simp only [translated,re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring

theorem translated_difference (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qsub (ofGaussian (translated z B one) B) (ofGaussian z B) ≐ qone :=
  (GaussianRationalSyntheticDivision.qsub_congr (translated_fraction z B hB).eqSymm (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ GaussianRationalSyntheticDivision.qone_canonical)

theorem negative_half_mul_sum (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul GaussianBarnesCanonicalPrefactor.negativeHalf (qadd (ofGaussian (translated z B one) B) (ofGaussian z B)) ≐
      qnegative (halfShift z B) := by
  let w := translated z B one
  let a := translated (scale two z) B one
  let C := ComplexLogarithmRemainder.add w z
  let d : PTm n := scale one oneCode
  let T := two*B
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have ht := positive_product two B h2 hB
  have r := qadd_represents _ _ w z B hB (ofGaussian_represents w B hB) (ofGaussian_represents z B hB)
  have l := qmul_represents _ _ (ComplexLogarithmRemainder.neg d) C two B h2 hB
    (qnegative_represents (fraction one two) d two (ofGaussian_represents d two h2)) r
  have rr := qnegative_represents (halfShift z B) a T (ofGaussian_represents a T ht)
  apply canonical_unique _ _ _ T (qmul_canonical _ _) (qnegative_canonical _) ht l
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rr
  apply equal_of_values <;> simp only [C,d,a,w,translated,re_add,im_add,re_mul,im_mul,re_neg,im_neg,
    re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring

private theorem integer_disk (B : PTm n) : Γ ⊢[PRAAx] bounded (scale B oneCode) B :=
  le_congr ((normSq_scale B oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))).eqSymm
    (.eqRefl _) (le_refl (B*B))

theorem translated_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (translated z B one) ((R+one)*B) := by
  have h1 := bounded_add h (integer_disk B)
  have h2 := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
    (bounded (ComplexLogarithmRemainder.add (var 0) (scale (var 1) oneCode)) (var 2) : Fm PTm 3)
    ![z,B,R*B+B] ![z,B*one,(R+one)*B] (fun i => by
      fin_cases i
      · exact .eqRefl z
      · change Γ ⊢[PRAAx] B ≐ B*one
        ipra_ring
      · change Γ ⊢[PRAAx] R*B+B ≐ (R+one)*B
        ipra_ring)
    (by simpa using h1)
  simpa [translated] using h2

theorem half_shift_bound (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] bounded z (R*B)) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (halfShift z B) (R+one) one := by
  let G := translated (scale two z) B one
  let D := two*B
  have hd := positive_product two B (le_succ_self one) hB
  have b := translated_bound (scale two z) (two*R) B
    (bounded_mono (bounded_scale two h) (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)))
  have c : Γ ⊢[PRAAx] bounded G ((R+one)*D) :=
    bounded_mono b (le_of_eq_add (d := B) (by dsimp [D]; ipra_ring))
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hd (le_refl one) (ofGaussian_represents G D hd)
    (le_congr (by ipra_ring) (by dsimp only [D]; ipra_ring) c)

theorem terminal_source (z R B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] bounded z (R*B)) (hk : Γ ⊢[PRAAx] le (two*(R+one)) K) : Γ ⊢[PRAAx]
    GaussianBarnesCanonicalTerminalRemainder.source (translated z B one) (R+one) B K :=
  .andI hB (.andI hK (.andI (translated_bound z R B h) hk))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalShiftChart
