import IPRADerivations.Algebra.QuadraticRationalEqualityOrder

/-!
# Rational quadratic equality and order respect actual arithmetic

Every rational operation is the original normalized producer. Fixed
native cross-numerator identities derive its sign-zero congruences,
translation of strict order and multiplication by a positive factor.
All input representations in the final laws are computed internally.
The radicand is a positive integer; rational radicands and towers are
separate obligations.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalCongruence

open_ipra
open QuadraticSignCertificates (first second equal multiply_first multiply_second negative_first negative_second)
open QuadraticConeOrder (equal_of_values equal_symm add_first add_second)
open QuadraticRationalClearing (clear denominator represents clear_represents denominator_positive)
open QuadraticPositiveScaling (scale scale_first scale_second sign_scale)
open QuadraticRationalPairArithmetic (add negative multiply positive)
open QuadraticRationalEqualityOrder (difference cross crossOf equivalent less zero_cross positive_cross)
open LeanProofs.IPRA.Analysis.RationalAlgebra (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem equivalent_of_representations (d x y A D B E : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E)
    (hz : Γ ⊢[PRAAx] QuadraticIntegerOrder.isZero d (cross A D B E)) : Γ ⊢[PRAAx] equivalent d x y :=
  (QuadraticRationalClearing.representation_sign _ _ _ _ hd (positive_product hD hE)
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ hx hy)).eqTrans hz
theorem less_of_representations (d x y A D B E : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E)
    (hp : Γ ⊢[PRAAx] QuadraticIntegerOrder.positive d (cross B E A D)) : Γ ⊢[PRAAx] less d x y :=
  (QuadraticRationalClearing.representation_sign _ _ _ _ hd (positive_product hE hD)
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ hy hx)).eqTrans hp

theorem addition_cross (A D A' D' B E B' E' : PTm n) : Γ ⊢[PRAAx]
    equal (cross (QuadraticSignCertificates.add (scale E A) (scale D B)) (D*E)
      (QuadraticSignCertificates.add (scale E' A') (scale D' B')) (D'*E'))
      (QuadraticSignCertificates.add (scale (E*E') (cross A D A' D')) (scale (D*D') (cross B E B' E'))) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,scale_first,scale_second,Q.mk_mul,map_mul] <;> ring
theorem negative_cross (A D B E : PTm n) : Γ ⊢[PRAAx]
    equal (cross (QuadraticSignCertificates.negative A) D (QuadraticSignCertificates.negative B) E)
      (QuadraticSignCertificates.negative (cross A D B E)) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,scale_first,scale_second] <;> ring
theorem multiplication_cross (d A D A' D' B E B' E' : PTm n) : Γ ⊢[PRAAx]
    equal (cross (QuadraticSignCertificates.multiply d A B) (D*E)
      (QuadraticSignCertificates.multiply d A' B') (D'*E'))
      (QuadraticSignCertificates.add
        (QuadraticSignCertificates.multiply d (cross A D A' D') (scale E' B))
        (QuadraticSignCertificates.multiply d (scale D A') (cross B E B' E'))) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,multiply_first,multiply_second,scale_first,scale_second,Q.mk_mul,map_mul] <;> ring
theorem translation_cross (A D B E C F : PTm n) : Γ ⊢[PRAAx]
    equal (cross (QuadraticSignCertificates.add (scale F B) (scale E C)) (E*F)
      (QuadraticSignCertificates.add (scale F A) (scale D C)) (D*F))
      (scale (F*F) (cross B E A D)) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,scale_first,scale_second,Q.mk_mul,map_mul] <;> ring
theorem positive_factor_cross (d A D B E C F : PTm n) : Γ ⊢[PRAAx]
    equal (cross (QuadraticSignCertificates.multiply d C B) (F*E)
      (QuadraticSignCertificates.multiply d C A) (F*D))
      (scale F (QuadraticSignCertificates.multiply d C (cross B E A D))) := by
  apply equal_of_values <;> simp only [cross,QuadraticIntegerOrder.difference,add_first,add_second,
    negative_first,negative_second,multiply_first,multiply_second,scale_first,scale_second,Q.mk_mul,map_mul] <;> ring

theorem equivalent_add (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') : Γ ⊢[PRAAx]
    equivalent d (add x y) (add x' y') := by
  apply equivalent_of_representations _ _ _ _ _ _ _ hd
    (positive_product (denominator_positive x) (denominator_positive y))
    (positive_product (denominator_positive x') (denominator_positive y'))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x') (clear_represents y'))
  apply QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (addition_cross _ _ _ _ _ _ _ _))
  exact QuadraticIntegerOrder.zero_add _ _ _ hd
    ((sign_scale d (denominator y*denominator y') (crossOf x x') hd
      (positive_product (denominator_positive y) (denominator_positive y'))).eqTrans (zero_cross _ _ _ hd hx))
    ((sign_scale d (denominator x*denominator x') (crossOf y y') hd
      (positive_product (denominator_positive x) (denominator_positive x'))).eqTrans (zero_cross _ _ _ hd hy))
theorem equivalent_negative (d x y : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] equivalent d x y) : Γ ⊢[PRAAx] equivalent d (negative x) (negative y) := by
  apply equivalent_of_representations _ _ _ _ _ _ _ hd (denominator_positive x) (denominator_positive y)
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents x))
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents y))
  exact QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (negative_cross _ _ _ _))
    (QuadraticIntegerOrder.zero_negative _ _ hd (zero_cross _ _ _ hd h))
theorem equivalent_multiply (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') : Γ ⊢[PRAAx]
    equivalent d (multiply d x y) (multiply d x' y') := by
  apply equivalent_of_representations _ _ _ _ _ _ _ hd
    (positive_product (denominator_positive x) (denominator_positive y))
    (positive_product (denominator_positive x') (denominator_positive y'))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive x') (denominator_positive y') (clear_represents x') (clear_represents y'))
  apply QuadraticIntegerOrder.zero_value_congr _ _ _ hd (equal_symm (multiplication_cross _ _ _ _ _ _ _ _ _))
  exact QuadraticIntegerOrder.zero_add _ _ _ hd
    (QuadraticIntegerOrder.zero_multiply _ _ _ hd (zero_cross _ _ _ hd hx))
    (QuadraticIntegerOrder.zero_value_congr _ _ _ hd (QuadraticPositiveScaling.product_commute _ _ _)
      (QuadraticIntegerOrder.zero_multiply _ _ _ hd (zero_cross _ _ _ hd hy)))

theorem less_translate (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx] less d (add x z) (add y z) := by
  apply less_of_representations _ _ _ _ _ _ _ hd
    (positive_product (denominator_positive x) (denominator_positive z))
    (positive_product (denominator_positive y) (denominator_positive z))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents z))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents y) (clear_represents z))
  apply QuadraticIntegerOrder.positive_value_congr _ _ _ hd (equal_symm (translation_cross _ _ _ _ _ _))
  exact (sign_scale d (denominator z*denominator z) (crossOf y x) hd
    (positive_product (denominator_positive z) (denominator_positive z))).eqTrans (positive_cross _ _ _ hd h)
theorem less_multiply_positive (d x y z : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hz : Γ ⊢[PRAAx] positive d z) (h : Γ ⊢[PRAAx] less d x y) : Γ ⊢[PRAAx]
    less d (multiply d z x) (multiply d z y) := by
  apply less_of_representations _ _ _ _ _ _ _ hd
    (positive_product (denominator_positive z) (denominator_positive x))
    (positive_product (denominator_positive z) (denominator_positive y))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive z) (denominator_positive x) (clear_represents z) (clear_represents x))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive z) (denominator_positive y) (clear_represents z) (clear_represents y))
  apply QuadraticIntegerOrder.positive_value_congr _ _ _ hd (equal_symm (positive_factor_cross _ _ _ _ _ _ _))
  exact (sign_scale d (denominator z) _ hd (denominator_positive z)).eqTrans
    (QuadraticIntegerOrder.positive_multiply _ _ _ hd hz (positive_cross _ _ _ hd h))

/-! This actual PR5 returns the three computed zero-sign checks for
addition, negation and multiplication on the original input pairs. -/
def output (d x x' y y' : PTm n) : PTm n := pairT
  (QuadraticRationalClearing.sign d (difference (add x y) (add x' y')))
  (pairT (QuadraticRationalClearing.sign d (difference (negative x) (negative x')))
    (QuadraticRationalClearing.sign d (difference (multiply d x y) (multiply d x' y'))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (d x x' y y' : PTm n) : PTm n := PTm.app outputF ![d,x,x',y,y']
ipra_subst output
ipra_subst run
theorem program_at (d x x' y y' : PTm n) : Γ ⊢[PRAAx] run d x x' y y' ≐ output d x x' y y' := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![d,x,x',y,y']
theorem returned_zero_certificate (d x x' y y' : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] equivalent d x x') (hy : Γ ⊢[PRAAx] equivalent d y y') : Γ ⊢[PRAAx]
    run d x x' y y' ≐ pairT zero (pairT zero zero) :=
  (program_at _ _ _ _ _).eqTrans (congrPairT (equivalent_add _ _ _ _ _ hd hx hy)
    (congrPairT (equivalent_negative _ _ _ hd hx) (equivalent_multiply _ _ _ _ _ hd hx hy)))

theorem actual_rational_equality_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      (equivalent (var 0) (add (var 1) (var 3)) (add (var 2) (var 4)) ⋏
        (equivalent (var 0) (negative (var 1)) (negative (var 2)) ⋏
          equivalent (var 0) (multiply (var 0) (var 1) (var 3)) (multiply (var 0) (var 2) (var 4))))) :=
  closeUniv 5 (.impI (.impI (.impI (.andI (equivalent_add _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)
    (.andI (equivalent_negative _ _ _ Prf.hyp0.wk.wk Prf.hyp1) (equivalent_multiply _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_rational_order_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ less (var 0) (var 1) (var 2) ⟶ less (var 0) (add (var 1) (var 3)) (add (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (less_translate _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_positive_factor_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ positive (var 0) (var 3) ⟶ less (var 0) (var 1) (var 2) ⟶
      less (var 0) (multiply (var 0) (var 3) (var 1)) (multiply (var 0) (var 3) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (less_multiply_positive _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_congruence_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_rational_returned_congruence_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ equivalent (var 0) (var 1) (var 2) ⟶ equivalent (var 0) (var 3) (var 4) ⟶
      run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ pairT zero (pairT zero zero)) :=
  closeUniv 5 (.impI (.impI (.impI (returned_zero_certificate _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Algebra.QuadraticRationalCongruence
