import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Denominators.GaussianGammaEulerHeadRescaling
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.Heads.GaussianGaussEulerHeadCancellation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferenceProduct

/-!
# Exact Gauss head grouping at the original reference arguments

The scaled reference head is the native head at one. The shifted
reference heads are the native heads at ((r+1)/m) in their original
order, despite the larger denominator used by the grouping.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerReferenceHeads

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator shiftedData)
open GaussianGammaEulerHead (run headF)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaEulerHeadRescaling (returned_rescale)
open GaussianGammaFiniteValueProperness (returned_head_equal)
open GaussianGammaGaussEulerHeads (cutoff shiftedHeadBody shiftedHeads shifted_head_at)
open GaussianGammaGaussReferenceProduct (argument)
open GaussianRationalFiniteProduct (qprod product_congr_bounded)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def referenceHeadBody : PTm 2 := run (argument (var 0)) (fstT (var 1)) (sndT (var 1))
def referenceHeads (m N : PTm n) : PTm n := qprod referenceHeadBody m (pairT m N)

ipra_subst referenceHeads

theorem reference_head_at (r m N : PTm n) : Γ ⊢[PRAAx]
    inst2 referenceHeadBody r (pairT m N) ≐ run (argument r) m N := by
  have read : Γ ⊢[PRAAx] run (argument r) (fstT (pairT m N)) (sndT (pairT m N)) ≐ run (argument r) m N :=
    congrAp3 headF (.eqRefl _) (fst_pair m N) (snd_pair m N)
  simpa only [referenceHeadBody,inst2,GaussianGammaGaussEulerHeads.subst_head_run,
    GaussianGammaGaussReferenceProduct.subst_argument,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using read

private theorem reference_numerator (r m : PTm n) : Γ ⊢[PRAAx]
    equal (shiftedNumerator oneCode m m r) (scale m (argument r)) := by
  apply equal_of_values <;>
    simp only [shiftedNumerator,translated,argument,re_add,im_add,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem shifted_reference_head (r m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] run (shiftedNumerator oneCode m m r) (m*m) N ≐ run (argument r) m N :=
  (returned_head_equal _ _ _ _ (positive_product m m hm hm) (reference_numerator r m)).eqTrans
    (returned_rescale (argument r) m m N hm hm)

theorem unit_head (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] run (scale m oneCode) m N ≐ run oneCode one N :=
  (congrAp3 headF (.eqRefl _) (one_mul m).eqSymm (.eqRefl N)).eqTrans
    (returned_rescale oneCode one m N (le_refl one) hm)

theorem reference_heads (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] shiftedHeads oneCode m m N ≐ referenceHeads m N := by
  have same : Γ ⊢[PRAAx] termsEqual shiftedHeadBody referenceHeadBody m (shiftedData oneCode m m N) (pairT m N) := by
    refine .allI (.impI ?_)
    let M := Syn.shift m
    let K := Syn.shift N
    let Δ := lt (var 0) M :: Γ.map Fm.shift
    have hM : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hm.shift.wk
    have e := shifted_head_at (Γ := Δ) (var 0) oneCode M M K
    have f := reference_head_at (Γ := Δ) (var 0) M K
    simpa [termsEqual,Δ,M,K,Syn.shift] using e.eqTrans ((shifted_reference_head (var 0) M K hM).eqTrans f.eqSymm)
  exact product_congr_bounded _ _ _ _ _ same

theorem head_grouping (z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qmul (run (scale m z) B (cutoff m N)) (referenceHeads m N) ≐
      qmul (shiftedHeads z B m N) (run oneCode one (cutoff m N)) :=
  (qmul_congr (.eqRefl _) (reference_heads m N hm).eqSymm).eqTrans
    ((GaussianGaussEulerHeadCancellation.relative_head_grouping z oneCode B m m N hB hm hm).eqTrans
      ((qmul_congr (unit_head m (cutoff m N) hm) (.eqRefl _)).eqTrans
        (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

theorem original_Gauss_reference_head_grouping_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      qmul (run (scale (var 2) (var 0)) (var 1) (cutoff (var 2) (var 3))) (referenceHeads (var 2) (var 3)) ≐
        qmul (shiftedHeads (var 0) (var 1) (var 2) (var 3)) (run oneCode one (cutoff (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (head_grouping _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerReferenceHeads
