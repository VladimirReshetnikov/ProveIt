import IPRADerivations.Algebra.QuadraticRationalPairArithmetic

/-!
# Actual rational-pair sign-zero equality and strict order

Equality is zero sign of the ACTUAL rational difference. Cross-cleared
native differences and their proved chain identities derive equivalence,
strict total order and order properness, with every denominator computed
from the original raw inputs. The numerical radicand is a positive integer.
This slice does not yet assert equality's arithmetic congruences or order
translation for the rational pair operations.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalEqualityOrder

open_ipra
open QuadraticSignCertificates (first second equal negative_first negative_second)
open QuadraticConeOrder (equal_of_values equal_symm equal_first equal_second add_first add_second)
open QuadraticRationalClearing (clear denominator represents clear_represents denominator_positive)
open QuadraticPositiveScaling (scale scale_first scale_second sign_scale)
open QuadraticRationalPairArithmetic (add negative positive isZero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def difference (x y : PTm n) : PTm n := add x (negative y)
def equivalent (d x y : PTm n) : Fm PTm n := isZero d (difference x y)
def less (d x y : PTm n) : Fm PTm n := positive d (difference y x)
def cross (A D B E : PTm n) : PTm n := QuadraticIntegerOrder.difference (scale E A) (scale D B)
def crossOf (x y : PTm n) : PTm n := cross (clear x) (denominator x) (clear y) (denominator y)
ipra_subst difference
ipra_subst equivalent
ipra_subst less
ipra_subst cross
ipra_subst crossOf

theorem represents_native_congr (x A B D : PTm n) (h : Γ ⊢[PRAAx] represents x A D)
    (he : Γ ⊢[PRAAx] equal A B) : Γ ⊢[PRAAx] represents x B D :=
  .andI (QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ (equal_first he) (.andE₁ h))
    (QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ (equal_second he) (.andE₂ h))
theorem cross_represents (x y A D B E : PTm n) (hx : Γ ⊢[PRAAx] represents x A D)
    (hy : Γ ⊢[PRAAx] represents y B E) : Γ ⊢[PRAAx] represents (difference x y) (cross A D B E) (D*E) := by
  apply represents_native_congr _ _ _ _
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ hx (QuadraticRationalPairArithmetic.negative_represents _ _ _ hy))
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,scale_first,scale_second] <;> ring
theorem difference_sign (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    QuadraticRationalClearing.sign d (difference x y) ≐ QuadraticSignCertificates.sign d (crossOf x y) :=
  QuadraticRationalClearing.representation_sign _ _ _ _ hd
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (cross_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
theorem cross_self (A D : PTm n) : Γ ⊢[PRAAx] equal (cross A D A D) QuadraticSignCertificates.zeroCode := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,QuadraticSignCertificates.zero_first_value,QuadraticSignCertificates.zero_second_value] <;> ring
theorem cross_reverse (A D B E : PTm n) : Γ ⊢[PRAAx]
    equal (cross B E A D) (QuadraticSignCertificates.negative (cross A D B E)) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,negative_first,negative_second] <;> ring
theorem cross_chain (A D B E C F : PTm n) : Γ ⊢[PRAAx]
    equal (scale E (cross A D C F))
      (QuadraticSignCertificates.add (scale F (cross A D B E)) (scale D (cross B E C F))) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,scale_first,scale_second] <;> ring
theorem forward_chain (A D B E C F : PTm n) : Γ ⊢[PRAAx]
    equal (scale E (cross C F A D))
      (QuadraticSignCertificates.add (scale F (cross B E A D)) (scale D (cross C F B E))) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,scale_first,scale_second] <;> ring
theorem native_add_commute (A B : PTm n) : Γ ⊢[PRAAx]
    equal (QuadraticSignCertificates.add A B) (QuadraticSignCertificates.add B A) := by
  apply equal_of_values <;> simp only [add_first,add_second] <;> ring

theorem zero_cross (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] QuadraticIntegerOrder.isZero d (crossOf x y) :=
  (difference_sign _ _ _ hd).eqSymm.eqTrans h
theorem zero_of_cross (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] QuadraticIntegerOrder.isZero d (crossOf x y)) : Γ ⊢[PRAAx] equivalent d x y :=
  (difference_sign _ _ _ hd).eqTrans h
theorem positive_cross (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] QuadraticIntegerOrder.positive d (crossOf y x) :=
  (difference_sign _ _ _ hd).eqSymm.eqTrans h
theorem positive_of_cross (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] QuadraticIntegerOrder.positive d (crossOf y x)) : Γ ⊢[PRAAx] less d x y :=
  (difference_sign _ _ _ hd).eqTrans h

theorem equivalent_refl (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] equivalent d x x :=
  zero_of_cross _ _ _ hd (QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (cross_self _ _))
    (QuadraticIntegerOrder.zero_isZero d hd))
theorem equivalent_symm (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d y x :=
  zero_of_cross _ _ _ hd (QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (cross_reverse _ _ _ _))
    (QuadraticIntegerOrder.zero_negative _ _ hd (zero_cross _ _ _ hd h)))
theorem equivalent_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] equivalent d x y) (hyz : Γ ⊢[PRAAx] equivalent d y z) : Γ ⊢[PRAAx] equivalent d x z := by
  apply zero_of_cross _ _ _ hd
  apply (sign_scale d (denominator y) (crossOf x z) hd (denominator_positive y)).eqSymm.eqTrans
  apply QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (cross_chain _ _ _ _ _ _))
  exact QuadraticIntegerOrder.zero_add _ _ _ hd
    ((sign_scale d (denominator z) (crossOf x y) hd (denominator_positive z)).eqTrans (zero_cross _ _ _ hd hxy))
    ((sign_scale d (denominator x) (crossOf y z) hd (denominator_positive x)).eqTrans (zero_cross _ _ _ hd hyz))
theorem less_irrefl (d x : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] neg (less d x x) := by
  refine .impI ?_
  exact QuadraticIntegerOrder.positive_zero_absurd _ _ (positive_cross _ _ _ hd.wk Prf.hyp0)
    (zero_cross _ _ _ hd.wk (equivalent_refl _ _ hd.wk))
theorem less_trans (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] less d x y) (hyz : Γ ⊢[PRAAx] less d y z) : Γ ⊢[PRAAx] less d x z := by
  apply positive_of_cross _ _ _ hd
  apply (sign_scale d (denominator y) (crossOf z x) hd (denominator_positive y)).eqSymm.eqTrans
  apply QuadraticIntegerOrder.positive_value_congr _ _ _ hd (equal_symm (forward_chain _ _ _ _ _ _))
  exact QuadraticIntegerOrder.positive_add _ _ _ hd
    ((sign_scale d (denominator z) (crossOf y x) hd (denominator_positive z)).eqTrans (positive_cross _ _ _ hd hxy))
    ((sign_scale d (denominator x) (crossOf z y) hd (denominator_positive x)).eqTrans (positive_cross _ _ _ hd hyz))
theorem ordered_trichotomy (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    less d x y ⋎ (less d y x ⋎ equivalent d x y) := by
  refine .orE (QuadraticIntegerOrder.sign_trichotomy d (crossOf y x)) ?_ ?_
  · exact .orI₁ (positive_of_cross _ _ _ hd.wk Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ (positive_of_cross _ _ _ hd.wk.wk
        (QuadraticIntegerOrder.positive_value_congr _ _ _ hd.wk.wk (equal_symm (cross_reverse _ _ _ _))
          (QuadraticIntegerOrder.negative_positive _ _ hd.wk.wk Prf.hyp0))))
    · exact .orI₂ (.orI₂ (equivalent_symm _ _ _ hd.wk.wk (zero_of_cross _ _ _ hd.wk.wk Prf.hyp0)))

theorem equivalent_less (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] equivalent d x y) (hyz : Γ ⊢[PRAAx] less d y z) : Γ ⊢[PRAAx] less d x z := by
  apply positive_of_cross _ _ _ hd
  apply (sign_scale d (denominator y) (crossOf z x) hd (denominator_positive y)).eqSymm.eqTrans
  apply QuadraticIntegerOrder.positive_value_congr _ _ _ hd (equal_symm (forward_chain _ _ _ _ _ _))
  apply QuadraticIntegerOrder.positive_value_congr _ _ _ hd (equal_symm (native_add_commute _ _))
  exact QuadraticIntegerOrder.positive_add_zero _ _ _ hd
    ((sign_scale d (denominator x) (crossOf z y) hd (denominator_positive x)).eqTrans (positive_cross _ _ _ hd hyz))
    ((sign_scale d (denominator z) (crossOf y x) hd (denominator_positive z)).eqTrans
      (zero_cross _ _ _ hd (equivalent_symm _ _ _ hd hxy)))
theorem less_equivalent (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hxy : Γ ⊢[PRAAx] less d x y) (hyz : Γ ⊢[PRAAx] equivalent d y z) : Γ ⊢[PRAAx] less d x z := by
  apply positive_of_cross _ _ _ hd
  apply (sign_scale d (denominator y) (crossOf z x) hd (denominator_positive y)).eqSymm.eqTrans
  apply QuadraticIntegerOrder.positive_value_congr _ _ _ hd (equal_symm (forward_chain _ _ _ _ _ _))
  exact QuadraticIntegerOrder.positive_add_zero _ _ _ hd
    ((sign_scale d (denominator z) (crossOf y x) hd (denominator_positive z)).eqTrans (positive_cross _ _ _ hd hxy))
    ((sign_scale d (denominator x) (crossOf z y) hd (denominator_positive x)).eqTrans
      (zero_cross _ _ _ hd (equivalent_symm _ _ _ hd hyz)))
theorem less_congr (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y')
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d x' y' :=
  less_equivalent _ _ _ _ hd (equivalent_less _ _ _ _ hd (equivalent_symm _ _ _ hd hx) h) hy
theorem less_not_equivalent (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] neg (equivalent d x y) := by
  refine .impI ?_
  exact .impE (less_irrefl _ _ hd.wk) (less_equivalent _ _ _ _ hd.wk h.wk (equivalent_symm _ _ _ hd.wk Prf.hyp0))
theorem less_asymm (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] neg (less d y x) := by
  refine .impI ?_
  exact .impE (less_irrefl _ _ hd.wk) (less_trans _ _ _ _ hd.wk h.wk Prf.hyp0)

def output (d x y : PTm n) : PTm n := pairT (difference x y) (pairT (crossOf x y)
  (pairT (QuadraticRationalClearing.sign d (difference x y)) (QuadraticSignCertificates.sign d (crossOf x y))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d x y : PTm n) : PTm n := ap3 outputF d x y
ipra_subst output
ipra_subst run
theorem program_at (d x y : PTm n) : Γ ⊢[PRAAx] run d x y ≐ output d x y := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![d,x,y]
theorem returned_difference (d x y : PTm n) : Γ ⊢[PRAAx] fstT (run d x y) ≐ difference x y :=
  (program_at _ _ _).fstE
theorem returned_cross (d x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x y)) ≐ crossOf x y :=
  (program_at _ _ _).sndE.fstE
theorem returned_rational_sign (d x y : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d x y))) ≐ QuadraticRationalClearing.sign d (difference x y) :=
  (program_at _ _ _).sndE.sndE.fstE
theorem returned_native_sign (d x y : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d x y))) ≐ QuadraticSignCertificates.sign d (crossOf x y) :=
  (program_at _ _ _).sndE.sndE.sndE
theorem returned_equal_signs (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run d x y))) ≐ sndT (sndT (sndT (run d x y))) :=
  (returned_rational_sign _ _ _).eqTrans ((difference_sign _ _ _ hd).eqTrans (returned_native_sign _ _ _).eqSymm)

theorem actual_rational_difference_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (represents (difference (var 0) (var 1)) (crossOf (var 0) (var 1)) (denominator (var 0)*denominator (var 1))) :=
  closeUniv 2 (cross_represents _ _ _ _ _ _ (clear_represents _) (clear_represents _))
theorem actual_rational_difference_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ QuadraticRationalClearing.sign (var 0) (difference (var 1) (var 2)) ≐
      QuadraticSignCertificates.sign (var 0) (crossOf (var 1) (var 2))) := closeUniv 3 (.impI (difference_sign _ _ _ Prf.hyp0))
theorem actual_rational_equality_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ (equivalent (var 0) (var 1) (var 1) ⋏
      ((equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 2) (var 1)) ⋏
        (equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 2) (var 3) ⟶ equivalent (var 0) (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.andI (equivalent_refl _ _ Prf.hyp0)
    (.andI (.impI (equivalent_symm _ _ _ Prf.hyp1 Prf.hyp0)) (.impI (.impI (equivalent_trans _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_rational_strict_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ (neg (less (var 0) (var 1) (var 1)) ⋏
      ((less (var 0) (var 1) (var 2) ⟶ less (var 0) (var 2) (var 3) ⟶ less (var 0) (var 1) (var 3)) ⋏
        (less (var 0) (var 1) (var 2) ⋎ (less (var 0) (var 2) (var 1) ⋎ equivalent (var 0) (var 1) (var 2)))))) :=
  closeUniv 4 (.impI (.andI (less_irrefl _ _ Prf.hyp0)
    (.andI (.impI (.impI (less_trans _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))) (ordered_trichotomy _ _ _ Prf.hyp0))))
theorem actual_rational_order_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      less (var 0) (var 1) (var 3) ⟶ less (var 0) (var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (less_congr _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_rational_strict_order_separated_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ less (var 0) (var 1) (var 2) ⟶
      (neg (less (var 0) (var 2) (var 1)) ⋏ neg (equivalent (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.andI (less_asymm _ _ _ Prf.hyp1 Prf.hyp0) (less_not_equivalent _ _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_rational_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_rational_returned_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (returned_equal_signs _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticRationalEqualityOrder
