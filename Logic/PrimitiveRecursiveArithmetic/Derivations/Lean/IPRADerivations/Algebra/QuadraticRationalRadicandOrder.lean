import IPRADerivations.Algebra.QuadraticRationalRadicand

/-!
# Order and sign-zero congruence for a positive rational radicand

The actual change of basis preserves the coefficient values of the
original operations. Transport the sign-zero equality, sign and order
laws through this same change of basis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalRadicandOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (denominatorOf)
open QuadraticRationalRadicand
  (isPositive integerRadicand changeBasis sign equivalent less multiply integer_radicand_positive equivalent_iff less_iff)
open QuadraticRationalClearing (sameCoefficients)
open QuadraticRationalPairArithmetic (add negative)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def isZero (d x : PTm n) : Fm PTm n := sign d x ≐ zero
def positive (d x : PTm n) : Fm PTm n := sign d x ≐ one

theorem same_coefficients_equivalent (D x y : PTm n) (hd : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] QuadraticRationalEqualityOrder.equivalent D x y := by
  have hEq := QuadraticRationalClearing.equal_coefficient_cross x y h
  have zero : Γ ⊢[PRAAx] QuadraticSignCertificates.equal QuadraticSignCertificates.zeroCode
      (QuadraticRationalEqualityOrder.crossOf x y) := by
    apply QuadraticConeOrder.equal_of_values
    · have he := QuadraticConeOrder.equal_first hEq
      simp only [QuadraticRationalEqualityOrder.crossOf,QuadraticRationalEqualityOrder.cross,
        QuadraticIntegerOrder.difference,QuadraticConeOrder.add_first,QuadraticSignCertificates.negative_first,
        QuadraticSignCertificates.zero_first_value]
      linear_combination -he
    · have he := QuadraticConeOrder.equal_second hEq
      simp only [QuadraticRationalEqualityOrder.crossOf,QuadraticRationalEqualityOrder.cross,
        QuadraticIntegerOrder.difference,QuadraticConeOrder.add_second,QuadraticSignCertificates.negative_second,
        QuadraticSignCertificates.zero_second_value]
      linear_combination -he
  exact QuadraticRationalEqualityOrder.zero_of_cross _ _ _ hd
    (QuadraticIntegerOrder.zero_value_congr _ _ _ hd zero (QuadraticIntegerOrder.zero_isZero D hd))

private theorem lift_equivalent (d x y X Y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] sameCoefficients (changeBasis d x) X) (hy : Γ ⊢[PRAAx] sameCoefficients (changeBasis d y) Y)
    (h : Γ ⊢[PRAAx] QuadraticRationalEqualityOrder.equivalent (integerRadicand d) X Y) : Γ ⊢[PRAAx] equivalent d x y := by
  have pos := integer_radicand_positive d hd
  have ex := same_coefficients_equivalent _ _ _ pos hx
  have ey := QuadraticRationalEqualityOrder.equivalent_symm _ _ _ pos (same_coefficients_equivalent _ _ _ pos hy)
  exact (equivalent_iff d x y hd).iffMpr (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ pos
    ex (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ pos h ey))

private theorem lift_less (d x y X Y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] sameCoefficients (changeBasis d x) X) (hy : Γ ⊢[PRAAx] sameCoefficients (changeBasis d y) Y)
    (h : Γ ⊢[PRAAx] QuadraticRationalEqualityOrder.less (integerRadicand d) X Y) : Γ ⊢[PRAAx] less d x y := by
  have pos := integer_radicand_positive d hd
  have ex := same_coefficients_equivalent _ _ _ pos hx
  have ey := QuadraticRationalEqualityOrder.equivalent_symm _ _ _ pos (same_coefficients_equivalent _ _ _ pos hy)
  exact (less_iff d x y hd).iffMpr (QuadraticRationalEqualityOrder.less_equivalent _ _ _ _ pos
    (QuadraticRationalEqualityOrder.equivalent_less _ _ _ _ pos ex h) ey)

theorem equivalent_refl (d x : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx] equivalent d x x :=
  (equivalent_iff _ _ _ hd).iffMpr (QuadraticRationalEqualityOrder.equivalent_refl _ _ (integer_radicand_positive d hd))

theorem equivalent_symm (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (h : Γ ⊢[PRAAx] equivalent d x y) :
    Γ ⊢[PRAAx] equivalent d y x :=
  (equivalent_iff _ _ _ hd).iffMpr (QuadraticRationalEqualityOrder.equivalent_symm _ _ _ (integer_radicand_positive d hd)
    ((equivalent_iff _ _ _ hd).iffMp h))

theorem equivalent_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (hx : Γ ⊢[PRAAx] equivalent d x y)
    (hy : Γ ⊢[PRAAx] equivalent d y z) : Γ ⊢[PRAAx] equivalent d x z :=
  (equivalent_iff _ _ _ hd).iffMpr (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ (integer_radicand_positive d hd)
    ((equivalent_iff _ _ _ hd).iffMp hx) ((equivalent_iff _ _ _ hd).iffMp hy))

theorem equivalent_add (d x y z w : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (hx : Γ ⊢[PRAAx] equivalent d x y)
    (hy : Γ ⊢[PRAAx] equivalent d z w) : Γ ⊢[PRAAx] equivalent d (add x z) (add y w) := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  exact lift_equivalent d _ _ _ _ hd (QuadraticRationalRadicand.rescale_add _ _ _ hq) (QuadraticRationalRadicand.rescale_add _ _ _ hq)
    (QuadraticRationalCongruence.equivalent_add _ _ _ _ _ (integer_radicand_positive d hd)
      ((equivalent_iff _ _ _ hd).iffMp hx) ((equivalent_iff _ _ _ hd).iffMp hy))

theorem equivalent_negative (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (h : Γ ⊢[PRAAx] equivalent d x y) :
    Γ ⊢[PRAAx] equivalent d (negative x) (negative y) := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  exact lift_equivalent d _ _ _ _ hd (QuadraticRationalRadicand.rescale_negative _ _ hq) (QuadraticRationalRadicand.rescale_negative _ _ hq)
    (QuadraticRationalCongruence.equivalent_negative _ _ _ (integer_radicand_positive d hd) ((equivalent_iff _ _ _ hd).iffMp h))

theorem equivalent_multiply (d x y z w : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (hx : Γ ⊢[PRAAx] equivalent d x y)
    (hy : Γ ⊢[PRAAx] equivalent d z w) : Γ ⊢[PRAAx] equivalent d (multiply d x z) (multiply d y w) :=
  lift_equivalent d _ _ _ _ hd (QuadraticRationalRadicand.rescale_multiply _ _ _ hd) (QuadraticRationalRadicand.rescale_multiply _ _ _ hd)
    (QuadraticRationalCongruence.equivalent_multiply _ _ _ _ _ (integer_radicand_positive d hd)
      ((equivalent_iff _ _ _ hd).iffMp hx) ((equivalent_iff _ _ _ hd).iffMp hy))

theorem less_irrefl (d x : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx] neg (less d x x) :=
  .impI (.impE (QuadraticRationalEqualityOrder.less_irrefl _ _ (integer_radicand_positive d hd.wk))
    ((less_iff _ _ _ hd.wk).iffMp Prf.hyp0))

theorem less_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (hx : Γ ⊢[PRAAx] less d x y)
    (hy : Γ ⊢[PRAAx] less d y z) : Γ ⊢[PRAAx] less d x z :=
  (less_iff _ _ _ hd).iffMpr (QuadraticRationalEqualityOrder.less_trans _ _ _ _ (integer_radicand_positive d hd)
    ((less_iff _ _ _ hd).iffMp hx) ((less_iff _ _ _ hd).iffMp hy))

theorem trichotomy (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    less d x y ⋎ (less d y x ⋎ equivalent d x y) := by
  refine .orE (QuadraticRationalEqualityOrder.ordered_trichotomy (integerRadicand d)
    (changeBasis d x) (changeBasis d y) (integer_radicand_positive d hd)) ?_ ?_
  · exact .orI₁ ((less_iff _ _ _ hd.wk).iffMpr Prf.hyp0)
  · exact .orE Prf.hyp0 (.orI₂ (.orI₁ ((less_iff _ _ _ hd.wk.wk).iffMpr Prf.hyp0)))
      (.orI₂ (.orI₂ ((equivalent_iff _ _ _ hd.wk.wk).iffMpr Prf.hyp0)))

theorem less_translate (d x y z : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (h : Γ ⊢[PRAAx] less d x y) :
    Γ ⊢[PRAAx] less d (add x z) (add y z) := by
  have hq := LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive (Γ := Γ) d
  exact lift_less d _ _ _ _ hd (QuadraticRationalRadicand.rescale_add _ _ _ hq) (QuadraticRationalRadicand.rescale_add _ _ _ hq)
    (QuadraticRationalCongruence.less_translate _ _ _ _ (integer_radicand_positive d hd) ((less_iff _ _ _ hd).iffMp h))

theorem less_multiply_positive (d x y z : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hz : Γ ⊢[PRAAx] positive d z) (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d (multiply d z x) (multiply d z y) :=
  lift_less d _ _ _ _ hd (QuadraticRationalRadicand.rescale_multiply _ _ _ hd) (QuadraticRationalRadicand.rescale_multiply _ _ _ hd)
    (QuadraticRationalCongruence.less_multiply_positive _ _ _ _ (integer_radicand_positive d hd) hz ((less_iff _ _ _ hd).iffMp h))

theorem zero_product_reflect (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (h : Γ ⊢[PRAAx] isZero d (multiply d x y)) :
    Γ ⊢[PRAAx] isZero d x ⋎ isZero d y := by
  have pos := integer_radicand_positive d hd
  have eq := QuadraticRationalClearing.sign_congr (integerRadicand d) _ _ pos (QuadraticRationalRadicand.rescale_multiply d x y hd)
  exact QuadraticRationalPairArithmetic.zero_product_reflect _ _ _ pos (eq.eqSymm.eqTrans h)

theorem less_respects (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') (h : Γ ⊢[PRAAx] less d x y) :
    Γ ⊢[PRAAx] less d x' y' :=
  (less_iff _ _ _ hd).iffMpr (QuadraticRationalEqualityOrder.less_congr _ _ _ _ _ (integer_radicand_positive d hd)
    ((equivalent_iff _ _ _ hd).iffMp hx) ((equivalent_iff _ _ _ hd).iffMp hy) ((less_iff _ _ _ hd).iffMp h))

theorem less_congr (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') :
    Γ ⊢[PRAAx] Fm.iff (less d x y) (less d x' y') :=
  .andI (.impI (less_respects _ _ _ _ _ hd.wk hx.wk hy.wk Prf.hyp0))
    (.impI (less_respects _ _ _ _ _ hd.wk (equivalent_symm _ _ _ hd.wk hx.wk)
      (equivalent_symm _ _ _ hd.wk hy.wk) Prf.hyp0))

theorem positive_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx] positive d (add x y) := by
  have pos := integer_radicand_positive d hd
  have he := QuadraticRationalRadicand.rescale_add (Γ := Γ) (denominatorOf d) x y (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d)
  exact (QuadraticRationalClearing.sign_congr _ _ _ pos he).eqTrans
    (QuadraticRationalPairArithmetic.positive_add _ _ _ pos hx hy)

theorem positive_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] positive d x) (hy : Γ ⊢[PRAAx] positive d y) : Γ ⊢[PRAAx] positive d (multiply d x y) := by
  have pos := integer_radicand_positive d hd
  exact (QuadraticRationalClearing.sign_congr _ _ _ pos (QuadraticRationalRadicand.rescale_multiply d x y hd)).eqTrans
    (QuadraticRationalPairArithmetic.positive_multiply _ _ _ pos hx hy)

theorem zero_add (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (hx : Γ ⊢[PRAAx] isZero d x) (hy : Γ ⊢[PRAAx] isZero d y) : Γ ⊢[PRAAx] isZero d (add x y) := by
  have pos := integer_radicand_positive d hd
  have he := QuadraticRationalRadicand.rescale_add (Γ := Γ) (denominatorOf d) x y (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d)
  exact (QuadraticRationalClearing.sign_congr _ _ _ pos he).eqTrans
    (QuadraticRationalPairArithmetic.zero_add _ _ _ pos hx hy)

theorem zero_negative (d x : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (h : Γ ⊢[PRAAx] isZero d x) :
    Γ ⊢[PRAAx] isZero d (negative x) := by
  have pos := integer_radicand_positive d hd
  have he := QuadraticRationalRadicand.rescale_negative (Γ := Γ) (denominatorOf d) x (LeanProofs.IPRA.Analysis.RationalArgmin.denominator_positive d)
  exact (QuadraticRationalClearing.sign_congr _ _ _ pos he).eqTrans
    (QuadraticRationalPairArithmetic.zero_negative _ _ pos h)

theorem zero_multiply (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) (h : Γ ⊢[PRAAx] isZero d x) :
    Γ ⊢[PRAAx] isZero d (multiply d x y) := by
  have pos := integer_radicand_positive d hd
  exact (QuadraticRationalClearing.sign_congr _ _ _ pos (QuadraticRationalRadicand.rescale_multiply d x y hd)).eqTrans
    (QuadraticRationalPairArithmetic.zero_multiply _ _ _ pos h)

theorem actual_rational_radical_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (isPositive (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 2) (var 3) ⟶
      (equivalent (var 0) (var 1) (var 1) ⋏ (equivalent (var 0) (var 2) (var 1) ⋏ equivalent (var 0) (var 1) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (.andI (equivalent_refl _ _ Prf.hyp1.wk)
    (.andI (equivalent_symm _ _ _ Prf.hyp1.wk Prf.hyp1) (equivalent_trans _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem actual_rational_radical_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (isPositive (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      (equivalent (var 0) (add (var 1) (var 3)) (add (var 2) (var 4)) ⋏
        (equivalent (var 0) (negative (var 1)) (negative (var 2)) ⋏
          equivalent (var 0) (multiply (var 0) (var 1) (var 3)) (multiply (var 0) (var 2) (var 4))))) :=
  closeUniv 5 (.impI (.impI (.impI (.andI (equivalent_add _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0)
    (.andI (equivalent_negative _ _ _ Prf.hyp1.wk Prf.hyp1) (equivalent_multiply _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem actual_rational_radical_trichotomy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ (less (var 0) (var 1) (var 2) ⋎ (less (var 0) (var 2) (var 1) ⋎ equivalent (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (trichotomy _ _ _ Prf.hyp0))

theorem actual_rational_radical_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (isPositive (var 0) ⟶ (neg (less (var 0) (var 1) (var 1)) ⋏
      (less (var 0) (var 1) (var 2) ⟶ less (var 0) (var 2) (var 3) ⟶ less (var 0) (var 1) (var 3)))) :=
  closeUniv 4 (.impI (.andI (less_irrefl _ _ Prf.hyp0) (.impI (.impI (less_trans _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_rational_radical_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (isPositive (var 0) ⟶ less (var 0) (var 1) (var 2) ⟶ less (var 0) (add (var 1) (var 3)) (add (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (less_translate _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_radical_zero_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⟶ (isZero (var 0) (var 1) ⋎ isZero (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (zero_product_reflect _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_radical_order_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (isPositive (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      Fm.iff (less (var 0) (var 1) (var 3)) (less (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (less_congr _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_rational_radical_cone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ positive (var 0) (var 1) ⟶ positive (var 0) (var 2) ⟶
      (positive (var 0) (add (var 1) (var 2)) ⋏ positive (var 0) (multiply (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (.andI (positive_add _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0)
    (positive_multiply _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem actual_rational_radical_ideal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ isZero (var 0) (var 1) ⟶
      (isZero (var 0) (negative (var 1)) ⋏ (isZero (var 0) (multiply (var 0) (var 1) (var 2)) ⋏
        (isZero (var 0) (var 2) ⟶ isZero (var 0) (add (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (.impI (.andI (zero_negative _ _ Prf.hyp1 Prf.hyp0)
    (.andI (zero_multiply _ _ _ Prf.hyp1 Prf.hyp0) (.impI (zero_add _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Algebra.QuadraticRationalRadicandOrder
