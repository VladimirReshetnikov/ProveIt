import IPRADerivations.Algebra.QuadraticRationalNonnegativeRadicand
import IPRADerivations.Algebra.QuadraticRadicandScaling

/-!
# Raw representation invariance of the actual nonnegative quadratic stage

The SAME uniform sign program is independent of equivalent original
rational radicand codes. Both its positive and zero branches are derived
from original value equality. Original rational pair multiplication is
proper in its radicand and both coefficient pairs, even without a sign
restriction on the radicand. All equalities compare coefficient values.
This is one rational ground stage; no internal-depth tower is assumed.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalRepresentationInvariance

open_ipra
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalEq denominator_positive rationalEq_congr)
open RationalAlgebra (positive_product)
open QuadraticRationalClearing (sameCoefficients)
open QuadraticRationalRadicand (multiply isPositive)
open QuadraticRationalNonnegativeRadicand (nonnegative radicandZero sign positive isZero equivalent less)
open QuadraticRationalPairArithmetic (add negative)
open QuadraticRationalEqualityOrder (difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem positive_nonnegative (d : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx] nonnegative d := by
  apply QuadraticSignCertificates.nonnegative_of_value
  have hn : Nonneg Γ (ZT.toZ Γ (numeratorOf d)-1) := by
    simpa only [zsl_def,ZT.toZ_ofNat,Q.mk_one,map_one] using nn_zsl hd
  convert nn_add nn_one hn using 1 <;> ring

theorem zero_nonnegative (d : PTm n) (hd : Γ ⊢[PRAAx] radicandZero d) : Γ ⊢[PRAAx] nonnegative d :=
  zle_of_comb 0 (by rw [ZT.toZ_eq hd]; ring) nn_zero

theorem nonnegative_congr (d e : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx] nonnegative e :=
  .orE (QuadraticRationalNonnegativeRadicand.radicand_cases d hd)
    (positive_nonnegative e (QuadraticRadicandScaling.rational_positive_congr d e Prf.hyp0 h.wk))
    (zero_nonnegative e (QuadraticRadicandScaling.rational_zero_congr d e Prf.hyp0 h.wk))

theorem sign_invariance (d e x : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx] sign d x ≐ sign e x := by
  refine .orE (QuadraticRationalNonnegativeRadicand.radicand_cases d hd) ?_ ?_
  · have he := QuadraticRadicandScaling.rational_positive_congr d e Prf.hyp0 h.wk
    exact (QuadraticRationalNonnegativeRadicand.positive_branch d x Prf.hyp0).eqTrans
      ((QuadraticRadicandScaling.rational_radicand_sign_of_equal d e x Prf.hyp0 h.wk).eqTrans
        (QuadraticRationalNonnegativeRadicand.positive_branch e x he).eqSymm)
  · have he := QuadraticRadicandScaling.rational_zero_congr d e Prf.hyp0 h.wk
    exact (QuadraticRationalNonnegativeRadicand.zero_branch d x Prf.hyp0).eqTrans
      (QuadraticRationalNonnegativeRadicand.zero_branch e x he).eqSymm

theorem same_coefficients_sign (d x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] sign d x ≐ sign d y := by
  refine .orE (QuadraticRationalNonnegativeRadicand.radicand_cases d hd) ?_ ?_
  · exact (QuadraticRationalNonnegativeRadicand.positive_branch d x Prf.hyp0).eqTrans
      ((QuadraticRationalRing.same_coefficients_sign d x y Prf.hyp0 h.wk).eqTrans
        (QuadraticRationalNonnegativeRadicand.positive_branch d y Prf.hyp0).eqSymm)
  · exact (QuadraticRationalNonnegativeRadicand.zero_branch d x Prf.hyp0).eqTrans
      ((QuadraticRationalZeroProjection.sign_congr x y
        (QuadraticRationalZeroProjection.equivalent_of_projection x y (.andE₁ h.wk))).eqTrans
          (QuadraticRationalNonnegativeRadicand.zero_branch d y Prf.hyp0).eqSymm)

theorem representation_invariance (d e x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hde : Γ ⊢[PRAAx] rationalEq d e) (hxy : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx]
    sign d x ≐ sign e y :=
  (sign_invariance d e x hd hde).eqTrans (same_coefficients_sign e x y (nonnegative_congr d e hd hde) hxy)

theorem scalar_represents_of_equal (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq a b) : Γ ⊢[PRAAx]
    RationalArithmetic.represents b (numeratorOf a) (denominatorOf a) :=
  QuadraticRadicandScaling.numerator_cross a b h

theorem scalar_equal_of_same_representation (a b D : PTm n) (A : ZT n)
    (hD : Γ ⊢[PRAAx] le one D)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents a A D)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b A D) : Γ ⊢[PRAAx] rationalEq a b :=
  QuadraticRationalRadicand.equal_from_representations a b D D A A hD hD ha hb (.eqRefl _)

theorem scalar_add_congr (a a' b b' : PTm n) (ha : Γ ⊢[PRAAx] rationalEq a a')
    (hb : Γ ⊢[PRAAx] rationalEq b b') : Γ ⊢[PRAAx]
    rationalEq (RationalArithmetic.add a b) (RationalArithmetic.add a' b') :=
  scalar_equal_of_same_representation _ _ _ _ (positive_product (denominator_positive a) (denominator_positive b))
    (RationalRepresentations.represents_add _ _ _ _ _ _ (RationalRepresentations.represents_self a)
      (RationalRepresentations.represents_self b))
    (RationalRepresentations.represents_add _ _ _ _ _ _ (scalar_represents_of_equal a a' ha) (scalar_represents_of_equal b b' hb))

theorem scalar_multiply_congr (a a' b b' : PTm n) (ha : Γ ⊢[PRAAx] rationalEq a a')
    (hb : Γ ⊢[PRAAx] rationalEq b b') : Γ ⊢[PRAAx]
    rationalEq (RationalArithmetic.multiply a b) (RationalArithmetic.multiply a' b') :=
  scalar_equal_of_same_representation _ _ _ _ (positive_product (denominator_positive a) (denominator_positive b))
    (RationalRepresentations.represents_multiply _ _ _ _ _ _ (RationalRepresentations.represents_self a)
      (RationalRepresentations.represents_self b))
    (RationalRepresentations.represents_multiply _ _ _ _ _ _ (scalar_represents_of_equal a a' ha) (scalar_represents_of_equal b b' hb))

theorem scalar_negative_congr (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq a b) : Γ ⊢[PRAAx]
    rationalEq (RationalArithmetic.negative a) (RationalArithmetic.negative b) :=
  scalar_equal_of_same_representation _ _ _ _ (denominator_positive a)
    (RationalRepresentations.represents_negative _ _ _ (RationalRepresentations.represents_self a))
    (RationalRepresentations.represents_negative _ _ _ (scalar_represents_of_equal a b h))

theorem pair_add_congr (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] sameCoefficients x x')
    (hy : Γ ⊢[PRAAx] sameCoefficients y y') : Γ ⊢[PRAAx] sameCoefficients (add x y) (add x' y') :=
  .andI (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm
      (scalar_add_congr _ _ _ _ (.andE₁ hx) (.andE₁ hy)))
    (rationalEq_congr (snd_pair _ _).eqSymm (snd_pair _ _).eqSymm
      (scalar_add_congr _ _ _ _ (.andE₂ hx) (.andE₂ hy)))

theorem pair_negative_congr (x y : PTm n) (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx]
    sameCoefficients (negative x) (negative y) :=
  .andI (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (scalar_negative_congr _ _ (.andE₁ h)))
    (rationalEq_congr (snd_pair _ _).eqSymm (snd_pair _ _).eqSymm (scalar_negative_congr _ _ (.andE₂ h)))

theorem pair_multiply_congr (d e x x' y y' : PTm n) (hde : Γ ⊢[PRAAx] rationalEq d e)
    (hx : Γ ⊢[PRAAx] sameCoefficients x x') (hy : Γ ⊢[PRAAx] sameCoefficients y y') : Γ ⊢[PRAAx]
    sameCoefficients (multiply d x y) (multiply e x' y') :=
  .andI (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm
      (scalar_add_congr _ _ _ _ (scalar_multiply_congr _ _ _ _ (.andE₁ hx) (.andE₁ hy))
        (scalar_multiply_congr _ _ _ _ hde (scalar_multiply_congr _ _ _ _ (.andE₂ hx) (.andE₂ hy)))))
    (rationalEq_congr (snd_pair _ _).eqSymm (snd_pair _ _).eqSymm
      (scalar_add_congr _ _ _ _ (scalar_multiply_congr _ _ _ _ (.andE₁ hx) (.andE₂ hy))
        (scalar_multiply_congr _ _ _ _ (.andE₂ hx) (.andE₁ hy))))

theorem radicand_product_congr (d e x y : PTm n) (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx]
    sameCoefficients (multiply d x y) (multiply e x y) :=
  pair_multiply_congr _ _ _ _ _ _ h (.andI (.eqRefl _) (.eqRefl _)) (.andI (.eqRefl _) (.eqRefl _))

theorem pair_difference_congr (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] sameCoefficients x x')
    (hy : Γ ⊢[PRAAx] sameCoefficients y y') : Γ ⊢[PRAAx] sameCoefficients (difference x y) (difference x' y') :=
  pair_add_congr _ _ _ _ hx (pair_negative_congr _ _ hy)

theorem equivalent_invariance (d e x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx] Fm.iff (equivalent d x y) (equivalent e x y) :=
  .andI (.impI ((sign_invariance d e _ hd h).wk.eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_invariance d e _ hd h).wk.eqTrans Prf.hyp0))

theorem less_invariance (d e x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx] Fm.iff (less d x y) (less e x y) :=
  .andI (.impI ((sign_invariance d e _ hd h).wk.eqSymm.eqTrans Prf.hyp0))
    (.impI ((sign_invariance d e _ hd h).wk.eqTrans Prf.hyp0))

theorem product_sign_invariance (d e x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hde : Γ ⊢[PRAAx] rationalEq d e) (hx : Γ ⊢[PRAAx] sameCoefficients x x')
    (hy : Γ ⊢[PRAAx] sameCoefficients y y') : Γ ⊢[PRAAx]
    sign d (multiply d x y) ≐ sign e (multiply e x' y') :=
  representation_invariance _ _ _ _ hd hde (pair_multiply_congr _ _ _ _ _ _ hde hx hy)

theorem equivalent_representations (d e x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hde : Γ ⊢[PRAAx] rationalEq d e) (hx : Γ ⊢[PRAAx] sameCoefficients x x')
    (hy : Γ ⊢[PRAAx] sameCoefficients y y') : Γ ⊢[PRAAx]
    Fm.iff (equivalent d x y) (equivalent e x' y') := by
  have hs := representation_invariance d e _ _ hd hde (pair_difference_congr _ _ _ _ hx hy)
  exact .andI (.impI (hs.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (hs.wk.eqTrans Prf.hyp0))

theorem less_representations (d e x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (hde : Γ ⊢[PRAAx] rationalEq d e) (hx : Γ ⊢[PRAAx] sameCoefficients x x')
    (hy : Γ ⊢[PRAAx] sameCoefficients y y') : Γ ⊢[PRAAx]
    Fm.iff (less d x y) (less e x' y') := by
  have hs := representation_invariance d e _ _ hd hde (pair_difference_congr _ _ _ _ hy hx)
  exact .andI (.impI (hs.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (hs.wk.eqTrans Prf.hyp0))

def output (d e x y : PTm n) : PTm n :=
  pairT (pairT (sign d x) (sign e x)) (pairT (multiply d x y) (multiply e x y))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (d e x y : PTm n) : PTm n := PTm.app outputF ![d,e,x,y]
ipra_subst output
ipra_subst run

theorem program_at (d e x y : PTm n) : Γ ⊢[PRAAx] run d e x y ≐ output d e x y := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![d,e,x,y]
theorem returned_original_sign (d e x y : PTm n) : Γ ⊢[PRAAx] fstT (fstT (run d e x y)) ≐ sign d x :=
  (program_at _ _ _ _).fstE.fstE
theorem returned_other_sign (d e x y : PTm n) : Γ ⊢[PRAAx] sndT (fstT (run d e x y)) ≐ sign e x :=
  (program_at _ _ _ _).fstE.sndE
theorem returned_original_product (d e x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d e x y)) ≐ multiply d x y :=
  (program_at _ _ _ _).sndE.fstE
theorem returned_other_product (d e x y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d e x y)) ≐ multiply e x y :=
  (program_at _ _ _ _).sndE.sndE
theorem returned_equal_signs (d e x y : PTm n) (hd : Γ ⊢[PRAAx] nonnegative d)
    (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx]
    fstT (fstT (run d e x y)) ≐ sndT (fstT (run d e x y)) :=
  (returned_original_sign _ _ _ _).eqTrans ((sign_invariance _ _ _ hd h).eqTrans (returned_other_sign _ _ _ _).eqSymm)
theorem returned_equal_products (d e x y : PTm n) (h : Γ ⊢[PRAAx] rationalEq d e) : Γ ⊢[PRAAx]
    sameCoefficients (fstT (sndT (run d e x y))) (sndT (sndT (run d e x y))) :=
  QuadraticRationalRing.coefficients_code_congr
    (returned_original_product _ _ _ _).eqSymm (returned_other_product _ _ _ _).eqSymm
    (radicand_product_congr _ _ _ _ h)

theorem actual_nonnegative_radicand_value_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶ nonnegative (var 1)) :=
  closeUniv 2 (.impI (.impI (nonnegative_congr _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_uniform_radicand_sign_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶ sign (var 0) (var 2) ≐ sign (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (sign_invariance _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_uniform_full_representation_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶ sameCoefficients (var 2) (var 3) ⟶
      sign (var 0) (var 2) ≐ sign (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (representation_invariance _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_rational_product_representation_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rationalEq (var 0) (var 1) ⟶ sameCoefficients (var 2) (var 3) ⟶ sameCoefficients (var 4) (var 5) ⟶
      sameCoefficients (multiply (var 0) (var 2) (var 4)) (multiply (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (pair_multiply_congr _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_raw_radicand_product_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rationalEq (var 0) (var 1) ⟶ sameCoefficients
      (multiply (var 0) (var 2) (var 3)) (multiply (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (radicand_product_congr _ _ _ _ Prf.hyp0))
theorem actual_uniform_equality_representation_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶ sameCoefficients (var 2) (var 3) ⟶
      sameCoefficients (var 4) (var 5) ⟶
        Fm.iff (equivalent (var 0) (var 2) (var 4)) (equivalent (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (equivalent_representations _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_uniform_order_representation_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶ sameCoefficients (var 2) (var 3) ⟶
      sameCoefficients (var 4) (var 5) ⟶
        Fm.iff (less (var 0) (var 2) (var 4)) (less (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (less_representations _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_uniform_product_sign_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶ sameCoefficients (var 2) (var 3) ⟶
      sameCoefficients (var 4) (var 5) ⟶
        sign (var 0) (multiply (var 0) (var 2) (var 4)) ≐ sign (var 1) (multiply (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (product_sign_invariance _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))
theorem actual_representation_invariance_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_uniform_sign_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonnegative (var 0) ⟶ rationalEq (var 0) (var 1) ⟶
      fstT (fstT (run (var 0) (var 1) (var 2) (var 3))) ≐ sndT (fstT (run (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (returned_equal_signs _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_returned_product_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (rationalEq (var 0) (var 1) ⟶ sameCoefficients
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (returned_equal_products _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticRationalRepresentationInvariance
